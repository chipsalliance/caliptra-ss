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

`ifndef CALIPTRA_SS_USB_HS_HUB_TEST_MODE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_TEST_MODE_SEQUENCE_SV

// =============================================================================
// USB SET_FEATURE(DEVICE, TEST_MODE) sequence for the hub.
//
// Enumerates the hub alone (hub_enum_stepA, no downstream port bring-up and no
// USBDC0 enumeration) and then issues exactly two SET_FEATURE requests to the
// hub at address 1:
//   1. one with a randomly drawn INVALID test selector (6..255) -> rejected
//   2. one with a randomly drawn VALID   test selector (1..5)   -> accepted
//
// Request encoding (USB 2.0 section 9.4.9):
//   bmRequestType = 0x00 (HOST_TO_DEVICE, STANDARD, recipient = device)
//   bRequest      = 0x03 (SET_FEATURE)
//   wValue        = 0x0002 (TEST_MODE feature selector)
//   wIndex[15:8]  = test selector, wIndex[7:0] = 0
//   wLength       = 0
//
// Valid test selectors: 1 Test_J, 2 Test_K, 3 Test_SE0_NAK, 4 Test_Packet,
// 5 Test_Force_Enable.
//
// Accept/reject is not observable from the VIP transfer item, so it is read
// from the RTL instead: usb_ep0_handler_1.usb_phy_test_mode is mirrored by
// usb_dev_addr_probe as hub_phy_test_mode and compared by
// check_phy_test_mode(). The register resets to 3'b000, is loaded with
// selector[2:0] only when the handler accepts the request, and has no clear
// path. So 3'b000 after the invalid request proves rejection and
// selector[2:0] after the valid request proves acceptance.
//
// The accepted SET_FEATURE must be the LAST USB activity of the sequence: once
// usb_phy_test_mode is non-zero the PIE enters BUS_EVENT_TEST_MODE, whose only
// documented exit is a power cycle (usb_pie.m.vhdl). Do not append further
// transfers after step 7.
//
// The two selectors are drawn with $urandom_range() and printed at UVM_LOW so
// a failing run can be reproduced from the log; the test is registered in the
// master test list with the Random category so nightly regressions sweep the
// selector space across seeds.
//
// Address map after hub_enum_stepA (see caliptra_ss_usb_base_sequence.svh):
//   hub -> device address 1, and the VIP anchor is already left at address 1,
//   so no re-anchoring is needed before the SET_FEATURE transfers.
// =============================================================================

class caliptra_ss_usb_hs_hub_test_mode_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_test_mode_sequence)

    // USB device address assigned to the hub during enumeration.
    localparam int HUB_ADDR = 1;

    // SET_FEATURE(TEST_MODE) encoding.
    localparam bit [7:0]  BREQ_SET_FEATURE = 8'h03;
    localparam bit [15:0] FEATURE_TEST_MODE = 16'h0002;

    // Test selector ranges accepted and rejected by the hub EP0 handler.
    localparam int VALID_SEL_LO   = 1;
    localparam int VALID_SEL_HI   = 5;
    localparam int INVALID_SEL_LO = 6;
    localparam int INVALID_SEL_HI = 255;

    function new(string name = "caliptra_ss_usb_hs_hub_test_mode_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Issue one SET_FEATURE(DEVICE, TEST_MODE) to the hub with the given test
    // selector placed in wIndex[15:8].
    // -------------------------------------------------------------------------
    task set_feature_test_mode(svt_usb_agent         host_agent_h,
                               svt_usb_configuration usb_cfg,
                               bit [7:0]             test_selector,
                               string                label);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_SET_FEATURE),
            .wvalue               (FEATURE_TEST_MODE),
            .windex               ({test_selector, 8'h00}),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        bit [7:0]             invalid_selector;
        bit [7:0]             valid_selector;

        `uvm_info("USB_HUB_TEST_MODE",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_HUB_TEST_MODE",
                "Link never reached ENABLED; aborting hub test_mode sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub alone at address 1. The downstream ports
        // are deliberately left un-powered: the hub EP0 handler only accepts
        // TEST_MODE on the hub itself.
        hub_enum_stepA(host_agent_h, usb_cfg);

        // Step 5: SET_FEATURE with a random invalid test selector. The EP0
        // SETUP-match ROM leaves wIndex[15:8] as a don't-care, so the request
        // does reach the handler, which stalls it because selector > 5.
        invalid_selector = $urandom_range(INVALID_SEL_HI, INVALID_SEL_LO);
        `uvm_info("USB_HUB_TEST_MODE",
            $sformatf("Invalid test selector draw: %0d (wIndex=0x%04h)",
                      invalid_selector, {invalid_selector, 8'h00}),
            UVM_LOW)
        set_feature_test_mode(host_agent_h, usb_cfg, invalid_selector,
                              "SET_FEATURE_TEST_MODE_invalid_hub");
        usb_data_check_api.check_phy_test_mode(.device_name("hub"),
                                               .expected_test_mode(3'b000));

        // Step 6: The stalled request must not have disturbed the link. A hub
        // class GET_HUB_STATUS proves EP0 still answers before the accepted
        // request shuts the link down.
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

        // Step 7: SET_FEATURE with a random valid test selector. This is the
        // last USB activity of the sequence: accepting a test mode drives the
        // PIE into BUS_EVENT_TEST_MODE, which only a power cycle exits.
        valid_selector = $urandom_range(VALID_SEL_HI, VALID_SEL_LO);
        `uvm_info("USB_HUB_TEST_MODE",
            $sformatf("Valid test selector draw: %0d (wIndex=0x%04h)",
                      valid_selector, {valid_selector, 8'h00}),
            UVM_LOW)
        set_feature_test_mode(host_agent_h, usb_cfg, valid_selector,
                              "SET_FEATURE_TEST_MODE_valid_hub");
        usb_data_check_api.check_phy_test_mode(.device_name("hub"),
                                               .expected_test_mode(valid_selector[2:0]));

        `uvm_info("USB_HUB_TEST_MODE",
            "USB hub test_mode sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_TEST_MODE_SEQUENCE_SV
