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

`ifndef CALIPTRA_SS_USB_FS_DEV_HUB_CONFIG_DESCRIPTOR_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_HUB_CONFIG_DESCRIPTOR_SEQUENCE_SV

// =============================================================================
// Full-Speed USB hub CONFIGURATION descriptor sequence for the hub-composite
// topology.
//
// Enumerates the hub + USBDC0, then issues two GET_DESCRIPTOR requests for the
// hub:
//   - GET_DESCRIPTOR(CONFIGURATION):             wValue=0x0200, wLength=0x0019.
//   - GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION): wValue=0x0700, wLength=0x0019.
// Both responses are 25-byte composite descriptors (9-byte configuration header
// + 9-byte interface descriptor + 7-byte endpoint descriptor). The returned
// bytes are compared against the hub RTL ROM expected values by the data-check
// API.
//
// This FS sequence issues GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) just like
// the HS variant (caliptra_ss_usb_hub_config_descriptor_sequence). The hub
// composite is a HIGH_SPEED_SUPPORT device, and per USB 2.0 spec 9.6.2/9.6.4
// an HS-capable device must return DEVICE_QUALIFIER and
// OTHER_SPEED_CONFIGURATION descriptors regardless of the speed the link is
// currently operating at -- this is a device property, not a link-speed
// property. The hub RTL ROM therefore returns a valid 25-byte
// OTHER_SPEED_CONFIGURATION on the FS link, and the check must pass. (Same
// rationale used to keep GetDeviceQualifier in the FS variants.)
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev0 -> device address 2 (behind hub downstream port 1)
// =============================================================================

class caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV0_ADDR = 2;

    function new(string name = "caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence");
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

        `uvm_info("USB_FS_HUB_CONFIG_DESC",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_FS_HUB_CONFIG_DESC",
                "Link never reached ENABLED; aborting fs hub_config_descriptor sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #50us;

        // Step 4: Enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_FS_HUB_CONFIG_DESC",
            "Enumeration complete. Issuing GET_DESCRIPTOR(CONFIGURATION) for the hub.",
            UVM_LOW)

        // After enumerate_hub_and_usbdc0() the VIP anchor is left at dev0
        // (address 2), so re-anchor onto the hub (address 1) first; otherwise
        // do_control_xfer()'s device_address WITH-constraint would contradict
        // the anchored remote device's address and randomize() would fail.
        set_anchor_addr(host_agent_h, usb_cfg, HUB_ADDR);

        // Step 5: GET_DESCRIPTOR(CONFIGURATION) for the hub. wValue=0x0200
        // (CONFIGURATION descriptor, index 0), wLength=0x0019 (25 bytes).
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0200),
            .windex               (16'h0000),
            .wlength              (16'h0019),
            .device_addr          (HUB_ADDR),
            .label                ("GET_CONFIGURATION_DESCRIPTOR_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_CONFIGURATION_DESCRIPTOR_hub"));

        // Step 6: Check the 25-byte CONFIGURATION descriptor returned by the
        // hub against the values in the RTL ROM.
        usb_data_check_api.check_configuration_descriptor(.usb_item(last_ctrl_seq_item),
                                                          .device_name("hub"));

        `uvm_info("USB_FS_HUB_CONFIG_DESC",
            "Issuing GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) for the hub.",
            UVM_LOW)

        // Step 7: GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) for the hub.
        // wValue=0x0700 (OTHER_SPEED_CONFIGURATION descriptor, index 0),
        // wLength=0x0019 (25 bytes). The hub composite is an HS-capable device,
        // so per USB 2.0 spec 9.6.2/9.6.4 it must return this descriptor even
        // when the link is running at full speed. The anchor is already on the
        // hub from the previous transfer.
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0700),
            .windex               (16'h0000),
            .wlength              (16'h0019),
            .device_addr          (HUB_ADDR),
            .label                ("GET_OTHER_SPEED_CONFIGURATION_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_OTHER_SPEED_CONFIGURATION_hub"));

        // Step 8: Check the 25-byte OTHER_SPEED_CONFIGURATION descriptor
        // returned by the hub against the values in the RTL ROM.
        usb_data_check_api.check_other_speed_configuration(.usb_item(last_ctrl_seq_item),
                                                           .device_name("hub"));

        `uvm_info("USB_FS_HUB_CONFIG_DESC",
            "USB fs hub_config_descriptor sequence complete.", UVM_LOW)

    endtask


endclass

`endif // CALIPTRA_SS_USB_FS_DEV_HUB_CONFIG_DESCRIPTOR_SEQUENCE_SV
