// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_GET_BOS_DESCRIPTOR_SEQUENCE_SV
`define CALIPTRA_SS_USB_GET_BOS_DESCRIPTOR_SEQUENCE_SV

// =============================================================================
// USB hub GET_DESCRIPTOR(BOS) sequence for the hub-composite topology.
//
// Enumerates the hub + USBDC0, then issues GetDescriptor(BOS) for the hub:
// GET_DESCRIPTOR with wValue=0x0F00 (BOS descriptor, index 0). The response is
// the 12-byte Binary Device Object Store of the compound hub: a 5-byte BOS
// header followed by a single 7-byte USB 2.0 Extension device capability
// descriptor (bmAttributes bit1 = LPM supported).
//
// The transfer is issued in two passes, mirroring how a real host reads a
// variable-length descriptor:
//
//   Pass 1 - short read, wLength=0x0005. A host first fetches only the BOS
//            header to learn wTotalLength, then comes back for the whole
//            object. This also exercises the IP's ability to truncate the
//            control-read at exactly the requested length.
//   Pass 2 - full read, wLength=0x000C (12 bytes), checked field-by-field
//            with check_bos_descriptor().
//
// Only the full read is handed to the checker: check_bos_descriptor() asserts
// a 12-byte payload, so feeding it the 5-byte short read would be a false
// failure. The short read is still valuable as stimulus and its length is
// verified locally below.
//
// The hub DEVICE descriptor reports bcdUSB=0x0210 (see check_device_descriptor
// in caliptra_ss_usb_data_check_api_impl.svh), which is what makes a BOS query
// legal in the first place: per the USB 2.0 LPM ECN a device must report
// bcdUSB >= 0x0201 before a host is allowed to ask for the BOS.
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev0 -> device address 2 (behind hub downstream port 1)
// =============================================================================

class caliptra_ss_usb_get_bos_descriptor_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_get_bos_descriptor_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV0_ADDR = 2;

    // GET_DESCRIPTOR(BOS) request constants.
    // bRequest = 0x06 (GET_DESCRIPTOR), wValue high byte = descriptor type
    // 0x0F (BOS), low byte = descriptor index 0.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] WVALUE_BOS          = 16'h0F00;
    localparam bit [15:0] WLENGTH_BOS_HEADER  = 16'h0005; // 5-byte BOS header
    localparam bit [15:0] WLENGTH_BOS_FULL    = 16'h000C; // 12-byte full BOS

    function new(string name = "caliptra_ss_usb_get_bos_descriptor_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Re-anchor the VIP host agent onto the target device address before a
    // control transfer. do_control_xfer() calls fix_anchors(0,0,0), which
    // anchors the transfer to remote_device_cfg[0]; svt_usb_transfer ties
    // device_address to that remote device's configured address. After
    // enumerate_hub_and_usbdc0() the anchor is left at dev0 (address 2), so
    // issuing a transfer WITH-constrained to a different address (e.g. the hub
    // at address 1) makes randomize() fail. Setting the configured address to
    // match the target and reconfiguring keeps the two in agreement.
    // -------------------------------------------------------------------------
    task set_anchor_addr(svt_usb_agent         host_agent_h,
                         svt_usb_configuration usb_cfg,
                         int                   addr);
        usb_cfg.remote_device_cfg[0].device_address = addr[6:0];
        host_agent_h.reconfigure(usb_cfg);
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        int unsigned          short_bytes;

        `uvm_info("USB_GET_BOS_DESCR",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_GET_BOS_DESCR",
                "Link never reached ENABLED; aborting get_bos_descriptor sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_GET_BOS_DESCR",
            "Enumeration complete. Issuing GetDescriptor(BOS) for the hub.",
            UVM_LOW)

        // Step 5: Re-anchor onto the hub (address 1). After
        // enumerate_hub_and_usbdc0() the VIP anchor is left at dev0
        // (address 2), so without this the device_address WITH-constraint
        // inside do_control_xfer() would contradict the anchored remote
        // device's address and randomize() would fail.
        set_anchor_addr(host_agent_h, usb_cfg, HUB_ADDR);

        // Step 6: Pass 1 - short read of just the 5-byte BOS header. This is
        // the first half of the normal two-step host flow for a
        // variable-length descriptor, and it checks that the IP truncates the
        // control-read at the requested wLength instead of returning all 12
        // bytes.
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_GET_DESCRIPTOR),
            .wvalue               (WVALUE_BOS),
            .windex               (16'h0000),
            .wlength              (WLENGTH_BOS_HEADER),
            .device_addr          (HUB_ADDR),
            .label                ("GET_DESCRIPTOR_BOS_header_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label  ("GET_DESCRIPTOR_BOS_header_hub"));

        // Verify the short read locally. check_bos_descriptor() is not used
        // here because it requires the full 12-byte payload; a 5-byte payload
        // would trip its CHK_BOS_NUM_BYTES assertion.
        if (last_ctrl_seq_item == null) begin
            `uvm_error("USB_GET_BOS_DESCR",
                "last_ctrl_seq_item is null after the BOS short read")
        end
        else begin
            short_bytes = last_ctrl_seq_item.payload_byte_count();
            CHK_BOS_HEADER_SHORT_READ: assert(short_bytes == WLENGTH_BOS_HEADER) else
                `uvm_error("USB_GET_BOS_DESCR",
                    $sformatf("BOS short read returned %0d bytes, expected %0d",
                              short_bytes, WLENGTH_BOS_HEADER))
            `uvm_info("USB_GET_BOS_DESCR",
                $sformatf("BOS header short read returned %0d bytes as requested.",
                          short_bytes), UVM_LOW)
        end

        // Step 7: Pass 2 - full 12-byte read, which is what the field-by-field
        // checker consumes.
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_GET_DESCRIPTOR),
            .wvalue               (WVALUE_BOS),
            .windex               (16'h0000),
            .wlength              (WLENGTH_BOS_FULL),
            .device_addr          (HUB_ADDR),
            .label                ("GET_DESCRIPTOR_BOS_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_DESCRIPTOR_BOS_hub"));

        // Step 8: Check the 12-byte BOS descriptor returned by the hub against
        // the BOS DESCRIPTOR block of the RTL ROM constant.
        usb_data_check_api.check_bos_descriptor(.usb_item(last_ctrl_seq_item),
                                                .device_name("hub"));

        `uvm_info("USB_GET_BOS_DESCR",
            "USB get_bos_descriptor sequence complete.", UVM_LOW)

    endtask

endclass

`endif // CALIPTRA_SS_USB_GET_BOS_DESCRIPTOR_SEQUENCE_SV
