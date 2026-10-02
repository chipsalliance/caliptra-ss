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

`ifndef CALIPTRA_SS_USB_GET_STATUS_SEQUENCE_SV
`define CALIPTRA_SS_USB_GET_STATUS_SEQUENCE_SV

// =============================================================================
// USB GET_STATUS sequence for the hub-composite topology.
//
// Enumerates the hub + USBDC0, then exercises SetFeature/ClearFeature
// (DEVICE_REMOTE_WAKEUP) + GET_STATUS on both the hub (address 1) and dev0
// (address 2):
//
//   1. hub  SetFeature(DEVICE_REMOTE_WAKEUP)   + GET_STATUS, expect 0x0002.
//   2. dev0 SetFeature(DEVICE_REMOTE_WAKEUP)   + GET_STATUS, expect 0x0003.
//   3. dev0 ClearFeature(DEVICE_REMOTE_WAKEUP) + GET_STATUS, expect 0x0001.
//
// dev0 reports Self-Powered (bit0=1) in its firmware GET_STATUS response, so
// its expected values carry the extra 0x0001. The hub is separate RTL and
// keeps its fixed 0x0002 / 0x0000 (bus-powered) responses.
//
// NOTE (hardware caveat): the hub is separate RTL
// (third_party/usb_hub_composite_device), not MCU firmware. The hub
// GET_STATUS response is fixed by the hub RTL; it is checked here against the
// value the hub RTL returns.
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev0 -> device address 2 (behind hub downstream port 1)
// =============================================================================

class caliptra_ss_usb_get_status_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_get_status_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV0_ADDR = 2;

    function new(string name = "caliptra_ss_usb_get_status_sequence");
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
    // Issue SetFeature/ClearFeature(DEVICE_REMOTE_WAKEUP) then GET_STATUS on
    // one device and check the 2-byte status word against expected. dev_name
    // selects the coverage/label tag ("hub" or "dev0"). When
    // remote_wakeup_enable is 1 (default) the transfer is SET_FEATURE(0x03);
    // when 0 it is CLEAR_FEATURE(0x01). Both carry feature selector
    // DEVICE_REMOTE_WAKEUP(0x0001). The firmware sets/clears its remote-wakeup
    // shadow accordingly, so the paired GET_STATUS returns 0x0002 after enable
    // and 0x0000 after disable (passed in via expected_status by the caller).
    // -------------------------------------------------------------------------
    task set_feature_and_get_status(svt_usb_agent         host_agent_h,
                                    svt_usb_configuration usb_cfg,
                                    int                   device_addr,
                                    string                dev_name,
                                    bit [15:0]            expected_status,
                                    bit                   remote_wakeup_enable = 1);
        bit [7:0] feat_brequest;
        string    feat_label;

        // enable=1 -> SET_FEATURE(0x03), enable=0 -> CLEAR_FEATURE(0x01).
        feat_brequest = remote_wakeup_enable ? 8'h03 : 8'h01;
        feat_label    = {(remote_wakeup_enable ? "SET_FEATURE_REMOTE_WAKEUP_"
                                               : "CLEAR_FEATURE_REMOTE_WAKEUP_"),
                         dev_name};

        // Anchor the VIP on this device before the SETUP transfers so the
        // device_address WITH-constraint matches the configured remote device.
        set_anchor_addr(host_agent_h, usb_cfg, device_addr);

        // SET_FEATURE/CLEAR_FEATURE(DEVICE_REMOTE_WAKEUP): HOST_TO_DEVICE,
        // STANDARD, recipient=device, bRequest selected above, wValue=feature
        // selector DEVICE_REMOTE_WAKEUP(0x0001), no data stage.
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (feat_brequest),
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (device_addr),
            .label                (feat_label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label(feat_label));

        // GET_STATUS: DEVICE_TO_HOST, STANDARD, recipient=device,
        // bRequest=GET_STATUS(0x00), 2-byte status response.
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h00),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0002),
            .device_addr          (device_addr),
            .label                ({"GET_STATUS_", dev_name}),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_STATUS_", dev_name}));
        usb_data_check_api.check_get_status(.usb_item(last_ctrl_seq_item),
                                            .device_name(dev_name),
                                            .expected(expected_status));
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        `uvm_info("USB_GET_STATUS",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_GET_STATUS",
                "Link never reached ENABLED; aborting get_status sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub at address 1 and USBDC0 at address 2.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_GET_STATUS",
            "Enumeration complete. Issuing SetFeature/ClearFeature + GET_STATUS.",
            UVM_LOW)

        // Step 5: SetFeature(DEVICE_REMOTE_WAKEUP) + GET_STATUS for the hub.
        set_feature_and_get_status(
            .host_agent_h   (host_agent_h),
            .usb_cfg        (usb_cfg),
            .device_addr    (HUB_ADDR),
            .dev_name       ("hub"),
            .expected_status(16'h0002));

        // Step 6: SetFeature(DEVICE_REMOTE_WAKEUP) + GET_STATUS for dev0.
        // USBDC0 firmware reports Self-Powered (bit0) always set and honors
        // the SET_FEATURE, so it returns 0x0003 (Self-Powered + Remote Wakeup).
        set_feature_and_get_status(
            .host_agent_h   (host_agent_h),
            .usb_cfg        (usb_cfg),
            .device_addr    (DEV0_ADDR),
            .dev_name       ("dev0"),
            .expected_status(16'h0003));

        // Step 7: ClearFeature(DEVICE_REMOTE_WAKEUP) + GET_STATUS for dev0.
        // USBDC0 firmware clears the remote-wakeup shadow flag, so the paired
        // GET_STATUS returns 0x0001 (Self-Powered set, remote-wakeup disabled).
        set_feature_and_get_status(
            .host_agent_h        (host_agent_h),
            .usb_cfg             (usb_cfg),
            .device_addr         (DEV0_ADDR),
            .dev_name            ("dev0"),
            .expected_status     (16'h0001),
            .remote_wakeup_enable(1'b0));

        set_feature_and_get_status(
            .host_agent_h        (host_agent_h),
            .usb_cfg             (usb_cfg),
            .device_addr         (HUB_ADDR),
            .dev_name            ("hub"),
            .expected_status     (16'h0000),
            .remote_wakeup_enable(1'b0));

        `uvm_info("USB_GET_STATUS",
            "USB get_status sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_GET_STATUS_SEQUENCE_SV
