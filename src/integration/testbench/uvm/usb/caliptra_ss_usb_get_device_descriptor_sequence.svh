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

`ifndef CALIPTRA_SS_USB_GET_DEVICE_DESCRIPTOR_SEQUENCE_SV
`define CALIPTRA_SS_USB_GET_DEVICE_DESCRIPTOR_SEQUENCE_SV

// =============================================================================
// USB GET_DESCRIPTOR(DEVICE) sequence for the hub-composite topology.
//
// Enumerates the hub + USBDC0, then issues a standard GET_DESCRIPTOR for the
// DEVICE descriptor to BOTH the hub and dev0: GET_DESCRIPTOR with
// wValue=0x0100 (descriptor type 1 = DEVICE, index 0), wLength=0x0012 (18
// bytes, the standard device-descriptor length). Each response is checked with
// usb_data_check_api.check_device_descriptor(). The device descriptor byte
// layout does not change with link speed, so this sequence is shared by the HS
// and FS variants with no speed gating.
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev0 -> device address 2 (behind hub downstream port 1)
// =============================================================================

class caliptra_ss_usb_get_device_descriptor_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_get_device_descriptor_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV0_ADDR = 2;

    function new(string name = "caliptra_ss_usb_get_device_descriptor_sequence");
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
    // Issue GET_DESCRIPTOR(DEVICE) to the target address and check the result.
    // -------------------------------------------------------------------------
    task get_device_descriptor(svt_usb_agent         host_agent_h,
                               svt_usb_configuration usb_cfg,
                               int                   addr,
                               string                dev_name);
        string label = {"GET_DEVICE_DESCRIPTOR_", dev_name};

        // Re-anchor onto the target device before the transfer so the
        // device_address WITH-constraint agrees with the anchored remote
        // device's configured address.
        set_anchor_addr(host_agent_h, usb_cfg, addr);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (addr),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));

        usb_data_check_api.check_device_descriptor(.usb_item(last_ctrl_seq_item),
                                                   .device_name(dev_name));
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        `uvm_info("USB_GET_DEVICE_DESCRIPTOR",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_GET_DEVICE_DESCRIPTOR",
                "Link never reached ENABLED; aborting get_device_descriptor sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_GET_DEVICE_DESCRIPTOR",
            "Enumeration complete. Issuing GET_DESCRIPTOR(DEVICE) for the hub and dev0.",
            UVM_LOW)

        // Step 5: GET_DESCRIPTOR(DEVICE) for the hub (address 1).
        get_device_descriptor(host_agent_h, usb_cfg, HUB_ADDR, "hub");

        // Step 6: GET_DESCRIPTOR(DEVICE) for dev0 (address 2).
        get_device_descriptor(host_agent_h, usb_cfg, DEV0_ADDR, "dev0");

        `uvm_info("USB_GET_DEVICE_DESCRIPTOR",
            "USB get_device_descriptor sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_GET_DEVICE_DESCRIPTOR_SEQUENCE_SV
