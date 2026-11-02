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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_SEQUENCE_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_SEQUENCE_SV

// =============================================================================
// USB dual-device High-Speed bulk loopback sequence.
//
// Exercises BOTH embedded device controllers of the compound USB IP (IP_3511)
// behind the on-chip 2-port hub, each doing an independent EP1 64-byte bulk
// OUT -> IN loopback:
//   - USBDC0 : hub downstream port 1, assigned USB device address 2.
//   - USBDC1 : hub downstream port 2, assigned USB device address 3.
//
// The two controllers share one USB bus, so they must take DISTINCT addresses.
// The SVT VIP shared_cfg models a SINGLE remote device (local_device_cfg_size
// = 1); addressing a specific controller is therefore done by mutating
// usb_cfg.remote_device_cfg[0].device_address and calling
// host_agent_h.reconfigure(usb_cfg) in lockstep (see the constraint note in
// caliptra_ss_usb_base_sequence.svh). select_remote_device() below centralizes
// that switch so the OUT/IN data phases can be interleaved across the two
// controllers while the single remote-device model follows whichever address
// is currently being driven.
//
// Flow:
//   1. Wait for HS host link ENABLED.
//   2. Start SOF generation to keep the link alive between transfers.
//   3. Post-reset settling delay for MCU firmware to re-arm EP0 on both
//      controllers.
//   4. Enumerate the hub (addr 1).
//   5. Bring up port 1, enumerate USBDC0 at address 2.
//   6. Bring up port 2, enumerate USBDC1 at address 3.
//   7. Bulk OUT 64 bytes to USBDC0 EP1, then to USBDC1 EP1 (interleaved so
//      both controllers are driven in the same window).
//   8. Bulk IN  64 bytes from USBDC0 EP1, then from USBDC1 EP1.
//   9. Verify each loopback payload matches the bytes sent to that controller.
//
// Each controller gets a distinct OUT pattern (dev0: byte[i]=i; dev1:
// byte[i]=i^0xFF) so a mis-routed loopback (data from the wrong controller) is
// caught by the content check, not just a length check.
// =============================================================================
class caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence)

    // USB device addresses assigned to the two controllers. They MUST differ.
    localparam bit [6:0] USBDC0_ADDR = 7'd2;
    localparam bit [6:0] USBDC1_ADDR = 7'd3;

    function new(string name = "caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence");
        super.new(name);
    endfunction

    // Point the single remote-device model at the given bus address so the
    // next data transfer's device_address constraint is satisfiable. Must be
    // called before each OUT/IN phase that targets a different controller.
    task select_remote_device(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg,
                              bit [6:0] addr);
        usb_cfg.remote_device_cfg[0].device_address = addr;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_DUAL_LOOPBACK_SEQ",
            $sformatf("Remote device model retargeted to address %0d.", addr),
            UVM_HIGH)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      dev0_out_req, dev0_in_req;
        svt_usb_transfer      dev1_out_req, dev1_in_req;
        bit [7:0]             dev0_data[];
        bit [7:0]             dev1_data[];
        int unsigned          i;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for HS link ENABLED.
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) return;

        // Step 2: Start SOF generation to keep the link alive.
        start_sof_generation();

        // Step 3: Post-reset settling delay (both controllers re-arm EP0).
        #50us;

        // Step 4: Enumerate the hub (addr 1). Done once for both controllers.
        hub_enum_stepA(host_agent_h, usb_cfg);

        // Step 5: Bring up port 1 and enumerate USBDC0 at address 2.
        hub_port_bringup_stepB(
            .host_agent_h(host_agent_h), .usb_cfg(usb_cfg), .port_num(1));
        usbdc0_enum_stepC(
            .host_agent_h  (host_agent_h),
            .usb_cfg       (usb_cfg),
            .suffix        ("_dev0"),
            .device_idx    (0),
            .assign_address(USBDC0_ADDR));

        // Step 6: Bring up port 2 and enumerate USBDC1 at address 3.
        // Step 5's usbdc0_enum_stepC() left the VIP anchor at address 2
        // (USBDC0). hub_port_bringup_stepB() issues hub-class requests at
        // device address 1 and requires the anchor to be 1 on entry (see its
        // header comment), so re-anchor onto the hub first; otherwise the
        // GetPortStatus_Port2 WITH-constraint (device_address==1) contradicts
        // the VIP fixed_dev_ep_ustr_valid_ranges constraint (device_address==2)
        // and randomize() fails.
        select_remote_device(host_agent_h, usb_cfg, 7'd1);
        hub_port_bringup_stepB(
            .host_agent_h(host_agent_h), .usb_cfg(usb_cfg), .port_num(2));

        usbdc0_enum_stepC(
            .host_agent_h  (host_agent_h),
            .usb_cfg       (usb_cfg),
            .suffix        ("_dev1"),
            .device_idx    (1),
            .assign_address(USBDC1_ADDR));

        `uvm_info("USB_DUAL_LOOPBACK_SEQ",
            "Dual-device enumeration complete (USBDC0@2, USBDC1@3).", UVM_LOW)
        #10us;

        // Build distinct 64-byte patterns so a cross-routed loopback fails the
        // content check (dev0: i, dev1: i xor 0xFF).
        dev0_data = new[64];
        dev1_data = new[64];
        for (i = 0; i < 64; i++) begin
            dev0_data[i] = i[7:0];
            dev1_data[i] = i[7:0] ^ 8'hFF;
        end

        // Step 7: Bulk OUT to both controllers (interleaved). Retarget the
        // single remote-device model before each OUT. ep_anchor_idx 2 = EP1
        // BULK OUT (see the test's endpoint_cfg[] layout). HS EP1 bulk
        // max_packet_size is 512, so a 64-byte OUT is a valid short packet;
        // do NOT set no_zero_length_end (that forces a 512-aligned length).
        select_remote_device(host_agent_h, usb_cfg, USBDC0_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr  (int'(USBDC0_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(2),
            .label        ("HS_BULK_OUT_EP1_dev0"),
            .req          (dev0_out_req),
            .obj_name     ("dev0_out_req"),
            .payload_data (dev0_data));

        select_remote_device(host_agent_h, usb_cfg, USBDC1_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr  (int'(USBDC1_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(2),
            .label        ("HS_BULK_OUT_EP1_dev1"),
            .req          (dev1_out_req),
            .obj_name     ("dev1_out_req"),
            .payload_data (dev1_data));

        // Allow MCU firmware time to copy EP1 OUT->IN and arm IN on both.
        #20us;

        // Step 8: Bulk IN from both controllers (loopback readback).
        // ep_anchor_idx 1 = EP1 BULK IN.
        select_remote_device(host_agent_h, usb_cfg, USBDC0_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr  (int'(USBDC0_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(1),
            .label        ("HS_BULK_IN_EP1_dev0"),
            .req          (dev0_in_req),
            .obj_name     ("dev0_in_req"));

        select_remote_device(host_agent_h, usb_cfg, USBDC1_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr  (int'(USBDC1_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(1),
            .label        ("HS_BULK_IN_EP1_dev1"),
            .req          (dev1_in_req));

        // Step 9: Verify each loopback payload.
        check_loopback("USBDC0", dev0_in_req, dev0_data);
        check_loopback("USBDC1", dev1_in_req, dev1_data);

        // Allow MCU firmware time to log both completions.
        #20us;

        `uvm_info("USB_DUAL_LOOPBACK_SEQ",
            "USB dual-device HS bulk loopback sequence complete.", UVM_LOW)
    endtask

    // Compare a received bulk IN payload against the bytes sent to that
    // controller, erroring on any mismatch.
    function void check_loopback(string dev_name, svt_usb_transfer in_req,
                                 bit [7:0] sent[]);
        int mismatch_count;
        mismatch_count = 0;
        for (int unsigned bi = 0; bi < 64; bi++) begin
            if (in_req.payload.data[bi] !== sent[bi]) begin
                `uvm_error("USB_DUAL_LOOPBACK_SEQ",
                    $sformatf("%s loopback mismatch at byte[%0d]: sent=0x%02h received=0x%02h",
                              dev_name, bi, sent[bi], in_req.payload.data[bi]))
                mismatch_count++;
            end
        end
        if (mismatch_count == 0)
            `uvm_info("USB_DUAL_LOOPBACK_SEQ",
                $sformatf("%s loopback data check PASSED: all 64 bytes match.",
                          dev_name), UVM_LOW)
        else
            `uvm_error("USB_DUAL_LOOPBACK_SEQ",
                $sformatf("%s loopback data check FAILED: %0d byte(s) mismatched.",
                          dev_name, mismatch_count))
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_SEQUENCE_SV
