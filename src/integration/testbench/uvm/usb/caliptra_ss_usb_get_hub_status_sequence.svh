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

`ifndef CALIPTRA_SS_USB_GET_HUB_STATUS_SEQUENCE_SV
`define CALIPTRA_SS_USB_GET_HUB_STATUS_SEQUENCE_SV

// =============================================================================
// USB GetHubStatus sequence for the hub-composite topology.
//
// Enumerates the hub + USBDC0, then issues GetHubStatus for the hub: hub-class
// GET_STATUS (DEVICE_TO_HOST, recipient=device, bRequest=GET_STATUS, wLength=4)
// returning 4 bytes: wHubStatus + wHubChange. Freshly after enumeration both
// defined bits are zero, checked with check_hub_status.
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev0 -> device address 2 (behind hub downstream port 1)
// =============================================================================

class caliptra_ss_usb_get_hub_status_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_get_hub_status_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV0_ADDR = 2;

    function new(string name = "caliptra_ss_usb_get_hub_status_sequence");
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

        `uvm_info("USB_GET_HUB_STATUS",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_GET_HUB_STATUS",
                "Link never reached ENABLED; aborting get_hub_status sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_GET_HUB_STATUS",
            "Enumeration complete. Issuing GetHubStatus for the hub.",
            UVM_LOW)

        // Step 5: GetHubStatus for the hub. Hub-class GET_STATUS with
        // recipient=device returns 4 bytes: wHubStatus + wHubChange. Freshly
        // after enumeration both defined bits are zero. After
        // enumerate_hub_and_usbdc0() the VIP anchor is left at dev0 (address
        // 2), so re-anchor onto the hub (address 1) first; otherwise
        // do_control_xfer()'s device_address WITH-constraint would contradict
        // the anchored remote device's address and randomize() would fail.
        set_anchor_addr(host_agent_h, usb_cfg, HUB_ADDR);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h00),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0004),
            .device_addr          (HUB_ADDR),
            .label                ("GET_HUB_STATUS_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_HUB_STATUS_hub"));
        usb_data_check_api.check_hub_status(.usb_item(last_ctrl_seq_item),
                                            .device_name("hub"),
                                            .expected_hub_status(16'h0000),
                                            .expected_hub_change(16'h0000));

        `uvm_info("USB_GET_HUB_STATUS",
            "USB get_hub_status sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_GET_HUB_STATUS_SEQUENCE_SV
