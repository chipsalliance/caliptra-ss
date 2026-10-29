// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_SEQUENCE_SV

// =============================================================================
// USB High-Speed device INTERRUPT endpoint loopback sequence.
//
// Flow:
//   1. Wait for the host link to reach ENABLED (the VIP drives SE0 + chirp
//      autonomously before ENABLED, so the DUT has already seen its bus reset).
//   2. Start SOF generation.
//   3. Settling delay so firmware can service DRES_C and re-arm EP0 / EPn.
//   4. Enumerate the hub (address 1) and USBDC0 (address 2).
//   5. INTERRUPT OUT of 64 bytes to EPn, pattern byte[i] = i.
//   6. INTERRUPT IN of 64 bytes from EPn and byte-compare against what was
//      sent (the firmware copies the OUT buffer into the IN buffer).
//
// Endpoint number: read from the uvm_config_db key "usb_int_ep_num" if the
// firmware has published it (stage 2 of the spec, via the MCI DEBUG_OUT
// handshake); otherwise the default INT_EP_DEFAULT is used, which must match
// USB_INT_EP_FIXED in the firmware.
// =============================================================================

class caliptra_ss_usb_hs_dev_int_loopback_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_int_loopback_sequence)

    // Must match USB_INT_EP_FIXED in caliptra_ss_usb_hs_dev_int_loopback.c
    // while the firmware still forces a fixed endpoint number.
    localparam int INT_EP_DEFAULT   = 2;
    localparam int INT_XFER_BYTES   = 64;

    function new(string name = "caliptra_ss_usb_hs_dev_int_loopback_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      int_out_req;
        svt_usb_transfer      int_in_req;
        bit [7:0]             send_data[];
        int unsigned          i;
        int                   int_ep;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: wait for link ENABLED.
        wait_for_link_enabled(shared_status, "HS host link");


        // Step 2: keep the link alive.
        start_sof_generation();

        // Step 3: post-reset settling delay (firmware DRES_C handling).
        #50us;

        // Step 4: enumerate hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_INT_LOOPBACK_SEQ", "Enumeration complete.", UVM_LOW)
        #10us;

        // Endpoint number: firmware-published value wins, else the default.
        // The firmware publishes usb_int_ep_num over the MCI DEBUG_OUT scratch
        // register very early (~30us), long before enumeration completes, so
        // reading it here (rather than at the top of body()) avoids racing
        // ahead of the firmware's config_db set and falsely falling back to
        // the default endpoint.
        if (!uvm_config_db#(int)::get(null, "*", "usb_int_ep_num", int_ep)) begin
            int_ep = INT_EP_DEFAULT;
            `uvm_info("USB_HS_INT_LOOPBACK_SEQ",
                $sformatf("usb_int_ep_num not published by firmware, using default EP%0d",
                          int_ep), UVM_LOW)
        end else begin
            `uvm_info("USB_HS_INT_LOOPBACK_SEQ",
                $sformatf("Firmware published interrupt endpoint EP%0d", int_ep),
                UVM_LOW)
        end

        // The modeled device endpoint descriptors were built with ep_number =
        // INT_EP_DEFAULT (the test cannot know the randomized value at
        // build_phase). The VIP auto-adds an anchor constraint
        // (endpoint_number == ep_anchor.ep_number), so unless the descriptors
        // are retargeted to the firmware's endpoint the transfer randomize()
        // is inconsistent (ep_anchor==2 vs ep_num==int_ep). usb_cfg is the host
        // configuration and its remote_device_cfg[0] is the same descriptor
        // object the host anchor reads (dev_cfg.local_device_cfg is aliased
        // into host_cfg.remote_device_cfg in the shared cfg constructor), so
        // updating it here retargets the anchor. endpoint_cfg[1] is INTERRUPT
        // IN, endpoint_cfg[2] is INTERRUPT OUT.
        usb_cfg.remote_device_cfg[0].endpoint_cfg[1].ep_number = int_ep;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[2].ep_number = int_ep;
        // Patching the cfg object alone is not enough: the host agent caches
        // its own endpoint model built at build_phase (with INT_EP_DEFAULT).
        // The descriptor must be pushed into the agent with reconfigure(),
        // exactly like the device_address changes in the enumeration steps.
        // Without this, a randomized EP != default leaves the host modeling
        // the old endpoint - it issues the new EP token but the modeled device
        // never ACKs it, and the transfer retries to timeout. Only ep_number
        // is EP-dependent here (direction/type/speed/max_packet_size are
        // identical for any EP), so retargeting ep_number + reconfigure() is a
        // complete retarget.
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_INT_LOOPBACK_SEQ",
            $sformatf("Retargeted device INTERRUPT endpoint descriptors to EP%0d",
                      int_ep), UVM_LOW)


        // Step 5: INTERRUPT OUT, pattern byte[i] = i. The firmware checks this
        // exact pattern before looping it back.
        send_data = new[INT_XFER_BYTES];

        for (i = 0; i < INT_XFER_BYTES; i++) send_data[i] = i[7:0];

        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::INTERRUPT_OUT_TRANSFER),
            .device_addr   (2),
            .ep_num        (int_ep),
            .byte_count    (INT_XFER_BYTES),
            .ep_anchor_idx (2),
            .label         ($sformatf("HS_INT_OUT_EP%0d", int_ep)),
            .req           (int_out_req),
            .obj_name      ("int_out_req"),
            .payload_data  (send_data));

        // Allow firmware to verify the OUT payload, copy it to the IN buffer
        // and arm the IN entry.
        #20us;

        // Step 6: INTERRUPT IN loopback read.
        do_data_xfer(
            .agent_h       (host_agent_h),
            .usb_cfg       (usb_cfg),
            .xfer_kind     (svt_usb_transfer::INTERRUPT_IN_TRANSFER),
            .device_addr   (2),
            .ep_num        (int_ep),
            .byte_count    (INT_XFER_BYTES),
            .ep_anchor_idx (1),
            .label         ($sformatf("HS_INT_IN_EP%0d", int_ep)),
            .req           (int_in_req),
            .obj_name      ("int_in_req"));

        // Data check.
        begin
            int mismatch_count;
            mismatch_count = 0;
            for (int unsigned bi = 0; bi < INT_XFER_BYTES; bi++) begin
                if (int_in_req.payload.data[bi] !== send_data[bi]) begin
                    `uvm_error("USB_HS_INT_LOOPBACK_SEQ",
                        $sformatf("INT loopback mismatch at byte[%0d]: sent=0x%02h received=0x%02h",
                                  bi, send_data[bi], int_in_req.payload.data[bi]))
                    mismatch_count++;
                end
            end
            if (mismatch_count == 0)
                `uvm_info("USB_HS_INT_LOOPBACK_SEQ",
                    $sformatf("INTERRUPT loopback data check PASSED: all %0d bytes match.",
                              INT_XFER_BYTES), UVM_LOW)
            else
                `uvm_error("USB_HS_INT_LOOPBACK_SEQ",
                    $sformatf("INTERRUPT loopback data check FAILED: %0d byte(s) mismatched.",
                              mismatch_count))
        end

        // Allow firmware to observe the IN Active-bit clear and log PASS.
        #20us;

        `uvm_info("USB_HS_INT_LOOPBACK_SEQ",
            "USB HS device INTERRUPT endpoint loopback sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_SEQUENCE_SV
