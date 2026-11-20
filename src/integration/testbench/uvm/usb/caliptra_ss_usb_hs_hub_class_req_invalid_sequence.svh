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

`ifndef CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_SEQUENCE_SV

// =============================================================================
// Hub class-request INVALID sequence (High Speed).
//
// Extends caliptra_ss_usb_hs_hub_class_req_stall_sequence. super.body() runs
// the parent's nine steps unchanged (link, SOF, hub-only enumeration, six
// STALL legs, one legal GetPortStatus), then this class adds steps 10..24.
//
// WHAT THIS TEST IS FOR
//
// Code coverage of usb_app_hw_hub.m.vhdl (third_party/usb2 copy, the one the
// regression compiles) plus TOGGLE coverage of its EP0_WVALUE, EP0_WINDEX and
// EP0_REQUEST input ports. The target list was given in the parent README's
// line numbering, which is 9 lines behind the current file:
//
//   requested  current  code                                     status
//   103        112      ClearPortFeature bad port -> stall        parent step 3
//   125        134      ClearPortFeature bad wValue -> stall      parent step 4
//   128        137      ClearHubFeature null                      step 10
//   133        142      GetPortStatus bad port -> stall           parent step 7
//   138        147      SetPortFeature bad port -> stall          parent step 5
//   158        167      SetPortFeature bad wValue -> stall        parent step 6
//   161        170      SetHubFeature null                        step 11
//   214        223      ClearPortFeature bad port null            parent step 3
//   228        237      ClearPortFeature accepted, no action      step 12
//   248        257      ClearPortFeature when others              parent step 4
//   259        268      SetPortFeature bad port null              parent step 5
//   275        284      SetPortFeature accepted, no action        step 13
//   286        295      SetPortFeature when others                parent step 6
//
// Current line 286 (SetPortFeature(PORT_ENABLE)) was also uncovered and is
// step 14; step 15 clears it again so no state is left behind.
//
// TWO FILTERS SIT BETWEEN THE HOST AND usb_app_hw_hub (MEASURED)
//
// 1. The hub SETUP-match table (usb_ep0_hub_descr.m.vhdl:362-399) compares
//    wIndex with mask 0xFFFC on the GetHubPortStatus / ClearHubPortFeature /
//    SetHubPortFeature rows. Port 3 passes and is stalled by usb_app_hw_hub
//    (parent steps 3/5/7); ports 4..255 are rejected one level earlier by
//    usb_ep0_handler (falls off the table, lines 205-207 / 239-241) and are
//    STALLed there. Steps 16-17 cover that case. SetAndTestHubPortFeature has
//    a wIndex mask of 0x0000, so port 3 DOES reach usb_app_hw_hub on that
//    request (step 18).
//
// 2. ep0_request is NOT the host bRequest. It is the 7-bit opcode stored in
//    the matched table row (usb_ep0_handler.m.vhdl:192) and it is cleared to 0
//    when no row matches (lines 207 / 241). An undefined class bRequest
//    (step 22) is therefore STALLed by the EP0 handler and can never toggle
//    EP0_REQUEST[5:4]: no shipped row has those bits set. The firmware of this
//    test rewrites the opcode of the GetHubStatus row (hub table word 157)
//    from 0x42 to 0x72 before the hub is enabled, so step 23 (GetHubStatus)
//    presents opcode 0x72 to usb_app_hw_hub: bits 6:4 = 111, which falls into
//    the "when others => null" arm, does not stall, and is the 0 -> 1 edge.
//    Step 24 restores a normal opcode and gives the 1 -> 0 edge.
//
// EP0_WVALUE / EP0_WINDEX are wired to the raw SETUP bytes
// (usb_ep0_handler.m.vhdl:292-293), so they toggle even on a request that is
// rejected. Steps 20 and 21 drive the missing bits to 1 and the following
// steps drive them back to 0:
//
//   wValue 0xD4E0 -> bits 15,14,12,10,7,6,5 (missing 0->1 and 1->0 of [7:5],
//                    [12], [15:14], and 1->0 of [10])
//   wIndex 0x01EC -> bits 8,7,6,5,3,2      (missing 0->1 and 1->0 of [3:2],
//                    [6:5], [8], and 1->0 of [7])
//
// STATE SAFETY
//
// Every leg is a decode no-op except step 14, which sets hub_port_enable_int
// for port 1. USBDC0 is never addressed (the host only talks to address 1),
// and step 15 clears the bit again. No PORT_RESET is issued on a legal port,
// so no bus reset reaches USBDC0.
//
// VERDICT
//
// A STALL is observed exactly as in the parent (ABORTED with
// results_status[4]); no report catcher is needed because nothing times out
// (note 38 section 5). The last leg is a legal GetPortStatus that must
// COMPLETE so that a wedged EP0 cannot satisfy the stall legs.
// =============================================================================

class caliptra_ss_usb_hs_hub_class_req_invalid_sequence
    extends caliptra_ss_usb_hs_hub_class_req_stall_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_class_req_invalid_sequence)

    // Own copies of the constants used here. They are deliberately NOT read
    // from the parent so this class does not depend on parent localparam
    // visibility rules, and the values are self-documenting at the call site.
    localparam int        INV_HUB_ADDR = 1;

    localparam bit [7:0]  INV_BREQ_GET_STATUS           = 8'h00;
    localparam bit [7:0]  INV_BREQ_CLEAR_FEATURE        = 8'h01;
    localparam bit [7:0]  INV_BREQ_SET_FEATURE          = 8'h03;
    localparam bit [7:0]  INV_BREQ_SET_AND_TEST_FEATURE = 8'h0C;
    localparam bit [7:0]  INV_BREQ_GET_TT_STATE         = 8'h0A;

    localparam bit [15:0] INV_FEAT_HUB_LOCAL_POWER = 16'h0000; // C_HUB_LOCAL_POWER
    localparam bit [15:0] INV_FEAT_PORT_ENABLE     = 16'h0001;
    localparam bit [15:0] INV_FEAT_PORT_RESET      = 16'h0004;
    localparam bit [15:0] INV_FEAT_PORT_POWER      = 16'h0008;
    localparam bit [15:0] INV_FEAT_PORT_L1         = 16'h000A;
    localparam bit [15:0] INV_FEAT_C_PORT_CONN     = 16'h0010;
    localparam bit [15:0] INV_FEAT_UNLISTED        = 16'h0005;

    localparam bit [15:0] INV_PORT_OK      = 16'h0001;
    // SetAndTestPortFeature decodes wIndex[3:0]; 3 is > C_HUB_NB_PORTS = 2.
    localparam bit [15:0] INV_PORT_BAD_3   = 16'h0003;
    // Rejected by the SETUP-table wIndex mask 0xFFFC before the hub decoder.
    localparam bit [15:0] INV_PORT_BAD_4   = 16'h0004;
    localparam bit [15:0] INV_PORT_BAD_255 = 16'h00FF;

    // Toggle patterns, see the header.
    localparam bit [15:0] INV_TOGGLE_WVALUE = 16'hD4E0;
    localparam bit [15:0] INV_TOGGLE_WINDEX = 16'h01EC;

    localparam bit [15:0] INV_STATUS_LEN = 16'h0004;

    localparam bit INV_MUST_STALL    = 1'b1;
    localparam bit INV_MUST_COMPLETE = 1'b0;

    // Class bRequest codes that no hub SETUP-table row matches. 0x02/0x04/0x05
    // are reserved in USB 2.0 table 11-16; 0x08/0x09/0x0B are TT requests this
    // embedded hub does not implement; 0xFF is out of range. 0x0A
    // (GET_TT_STATE) is a control READ and is issued separately in step 22.
    bit [7:0] undefined_out_breqs[] = '{8'h02, 8'h04, 8'h05, 8'h08,
                                        8'h09, 8'h0B, 8'hFF};

    function new(string name = "caliptra_ss_usb_hs_hub_class_req_invalid_sequence");
        super.new(name);
        MSG_ID = "USB_HUB_CLASS_REQ_INVALID";
    endfunction

    // -------------------------------------------------------------------------
    // Main body: parent steps 1-9, then steps 10-24.
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        int                   stall_legs = 0;

        // Parent: link, SOF, hub_enum_stepA, six STALL legs, legal GetPortStatus.
        super.body();

        host_agent_h = resolve_host_agent();
        usb_cfg      = resolve_usb_cfg();

        // ---------------------------------------------------------------------
        // Steps 10-15: ACCEPTED requests that land on the uncovered no-op
        // branches. Each must COMPLETE.
        // ---------------------------------------------------------------------

        // Step 10: ClearHubFeature(C_HUB_LOCAL_POWER), recipient DEVICE,
        // wIndex 0. usb_app_hw_hub.m.vhdl:137 (requested 128).
        step(10, "ClearHubFeature(C_HUB_LOCAL_POWER) to the hub itself - must COMPLETE");
        class_req_ex(host_agent_h, usb_cfg, svt_usb_types::HOST_TO_DEVICE,
                     svt_usb_types::BMREQ_DEVICE, INV_BREQ_CLEAR_FEATURE,
                     INV_FEAT_HUB_LOCAL_POWER, 16'h0000, 16'h0000,
                     "ClearHubFeature");
        check_setup_stalled(INV_MUST_COMPLETE, "ClearHubFeature",
                            "wIndex = 0 selects ClearHubFeature, null arm (line 137)");

        // Step 11: SetHubFeature(C_HUB_LOCAL_POWER). Line 170 (requested 161).
        step(11, "SetHubFeature(C_HUB_LOCAL_POWER) to the hub itself - must COMPLETE");
        class_req_ex(host_agent_h, usb_cfg, svt_usb_types::HOST_TO_DEVICE,
                     svt_usb_types::BMREQ_DEVICE, INV_BREQ_SET_FEATURE,
                     INV_FEAT_HUB_LOCAL_POWER, 16'h0000, 16'h0000,
                     "SetHubFeature");
        check_setup_stalled(INV_MUST_COMPLETE, "SetHubFeature",
                            "wIndex = 0 selects SetHubFeature, null arm (line 170)");

        // Step 12: ClearPortFeature(PORT_POWER) on port 1. Accepted by the
        // stall decoder (line 120) and a no-op in the handler (line 237,
        // requested 228).
        step(12, "ClearPortFeature(PORT_POWER) on port 1 - accepted no-op, must COMPLETE");
        class_req(host_agent_h, usb_cfg, INV_BREQ_CLEAR_FEATURE,
                  INV_FEAT_PORT_POWER, INV_PORT_OK, 16'h0000,
                  "ClearPortFeature_portPower");
        check_setup_stalled(INV_MUST_COMPLETE, "ClearPortFeature_portPower",
                            "PORT_POWER is in the accepted Clear list, no-op arm (line 237)");

        // Step 13: SetPortFeature(PORT_POWER) on port 1. Line 284 (requested 275).
        step(13, "SetPortFeature(PORT_POWER) on port 1 - accepted no-op, must COMPLETE");
        class_req(host_agent_h, usb_cfg, INV_BREQ_SET_FEATURE,
                  INV_FEAT_PORT_POWER, INV_PORT_OK, 16'h0000,
                  "SetPortFeature_portPower");
        check_setup_stalled(INV_MUST_COMPLETE, "SetPortFeature_portPower",
                            "PORT_POWER is in the accepted Set list, no-op arm (line 284)");

        // Step 14: SetPortFeature(PORT_ENABLE) on port 1. Line 286, the only
        // leg in this test that changes hub state.
        step(14, "SetPortFeature(PORT_ENABLE) on port 1 - must COMPLETE (restored in step 15)");
        class_req(host_agent_h, usb_cfg, INV_BREQ_SET_FEATURE,
                  INV_FEAT_PORT_ENABLE, INV_PORT_OK, 16'h0000,
                  "SetPortFeature_portEnable");
        check_setup_stalled(INV_MUST_COMPLETE, "SetPortFeature_portEnable",
                            "PORT_ENABLE sets hub_port_enable_int (line 286)");

        // Step 15: put port 1 back the way the parent left it.
        step(15, "ClearPortFeature(PORT_ENABLE) on port 1 - restore, must COMPLETE");
        class_req(host_agent_h, usb_cfg, INV_BREQ_CLEAR_FEATURE,
                  INV_FEAT_PORT_ENABLE, INV_PORT_OK, 16'h0000,
                  "ClearPortFeature_portEnable");
        check_setup_stalled(INV_MUST_COMPLETE, "ClearPortFeature_portEnable",
                            "PORT_ENABLE is in the accepted Clear list (line 239)");

        // ---------------------------------------------------------------------
        // Steps 16-19: further port numbers > C_HUB_NB_PORTS and invalid
        // feature selectors. Each must STALL.
        // ---------------------------------------------------------------------

        // Step 16: port 4 is rejected by the SETUP-table wIndex mask 0xFFFC,
        // so the EP0 handler stalls it before the hub decoder sees it.
        step(16, "ClearPortFeature(C_PORT_CONNECTION) to port 4 - must STALL (SETUP-table mask)");
        class_req(host_agent_h, usb_cfg, INV_BREQ_CLEAR_FEATURE,
                  INV_FEAT_C_PORT_CONN, INV_PORT_BAD_4, 16'h0000,
                  "ClearPortFeature_port4");
        check_setup_stalled(INV_MUST_STALL, "ClearPortFeature_port4",
                            "wIndex 4 fails the 0xFFFC wIndex mask of the row");
        stall_legs++;

        // Step 17: port 255 with PORT_RESET. Must STALL and must not reset.
        step(17, "SetPortFeature(PORT_RESET) to port 255 - must STALL, must not reset anything");
        class_req(host_agent_h, usb_cfg, INV_BREQ_SET_FEATURE,
                  INV_FEAT_PORT_RESET, INV_PORT_BAD_255, 16'h0000,
                  "SetPortFeature_port255");
        check_setup_stalled(INV_MUST_STALL, "SetPortFeature_port255",
                            "wIndex 255 fails the 0xFFFC wIndex mask of the row");
        stall_legs++;

        // Step 18: SetAndTestPortFeature to port 3. That row's wIndex mask is
        // 0x0000, so this one DOES reach usb_app_hw_hub and is stalled by the
        // wIndex[3:0] > C_HUB_NB_PORTS term (line 175).
        step(18, "SetAndTestPortFeature(PORT_L1) to port 3 - must STALL in the hub decoder");
        class_req_in(host_agent_h, usb_cfg, INV_BREQ_SET_AND_TEST_FEATURE,
                     INV_FEAT_PORT_L1, INV_PORT_BAD_3, INV_STATUS_LEN,
                     "SetAndTestPortFeature_port3");
        check_setup_stalled(INV_MUST_STALL, "SetAndTestPortFeature_port3",
                            "wIndex[3:0] = 3 exceeds C_HUB_NB_PORTS (line 175)");
        stall_legs++;

        // Step 19: SetAndTestPortFeature on a legal port with a feature
        // selector other than PORT_L1 - the third OR term (line 176).
        step(19, "SetAndTestPortFeature with wValue 5 on port 1 - must STALL (wValue /= PORT_L1)");
        class_req_in(host_agent_h, usb_cfg, INV_BREQ_SET_AND_TEST_FEATURE,
                     INV_FEAT_UNLISTED, INV_PORT_OK, INV_STATUS_LEN,
                     "SetAndTestPortFeature_badValue");
        check_setup_stalled(INV_MUST_STALL, "SetAndTestPortFeature_badValue",
                            "wValue is not PORT_L1 (line 176)");
        stall_legs++;

        // ---------------------------------------------------------------------
        // Steps 20-21: toggle legs for EP0_WVALUE / EP0_WINDEX upper bits.
        // ---------------------------------------------------------------------

        step(20, $sformatf("ClearPortFeature with wValue 0x%04h on port 1 - must STALL (wValue toggle)",
                           INV_TOGGLE_WVALUE));
        class_req(host_agent_h, usb_cfg, INV_BREQ_CLEAR_FEATURE,
                  INV_TOGGLE_WVALUE, INV_PORT_OK, 16'h0000,
                  "ClearPortFeature_wValueToggle");
        check_setup_stalled(INV_MUST_STALL, "ClearPortFeature_wValueToggle",
                            "wValue fails the 0xFFE0 wValue mask of the row");
        stall_legs++;

        step(21, $sformatf("GetPortStatus with wIndex 0x%04h - must STALL (wIndex toggle)",
                           INV_TOGGLE_WINDEX));
        class_req_in(host_agent_h, usb_cfg, INV_BREQ_GET_STATUS,
                     16'h0000, INV_TOGGLE_WINDEX, INV_STATUS_LEN,
                     "GetPortStatus_wIndexToggle");
        check_setup_stalled(INV_MUST_STALL, "GetPortStatus_wIndexToggle",
                            "wIndex fails the 0xFFFC wIndex mask of the row");
        stall_legs++;

        // ---------------------------------------------------------------------
        // Step 22: undefined class request codes. No table row matches any of
        // them, so the EP0 handler stalls them and ep0_request stays 0.
        // ---------------------------------------------------------------------
        step(22, "undefined hub class bRequest codes - each must STALL");
        foreach (undefined_out_breqs[i]) begin
            string lbl = $sformatf("UndefinedClassReq_0x%02h", undefined_out_breqs[i]);
            class_req(host_agent_h, usb_cfg, undefined_out_breqs[i],
                      16'h0000, INV_PORT_OK, 16'h0000, lbl);
            check_setup_stalled(INV_MUST_STALL, lbl,
                                "no hub SETUP-table row matches this bRequest");
            stall_legs++;
        end
        class_req_in(host_agent_h, usb_cfg, INV_BREQ_GET_TT_STATE,
                     16'h0000, INV_PORT_OK, INV_STATUS_LEN,
                     "UndefinedClassReq_GetTTState");
        check_setup_stalled(INV_MUST_STALL, "UndefinedClassReq_GetTTState",
                            "GET_TT_STATE is not implemented by this embedded hub");
        stall_legs++;

        // ---------------------------------------------------------------------
        // Step 23: GetHubStatus through the firmware-patched row. The opcode
        // the hub sees is 0x72 (bits 6:4 = 111), which only lands in the
        // "when others" arm of usb_app_hw_hub. Must COMPLETE, not stall. The
        // payload is the status word selected by the last latched data_index
        // and is reported only.
        // ---------------------------------------------------------------------
        step(23, "GetHubStatus via the patched SETUP row (ep0_request = 0x72) - must COMPLETE");
        class_req_ex(host_agent_h, usb_cfg, svt_usb_types::DEVICE_TO_HOST,
                     svt_usb_types::BMREQ_DEVICE, INV_BREQ_GET_STATUS,
                     16'h0000, 16'h0000, INV_STATUS_LEN,
                     "GetHubStatus_patchedOpcode");
        check_setup_stalled(INV_MUST_COMPLETE, "GetHubStatus_patchedOpcode",
                            "opcode 0x72 matches no class arm, so no class stall");
        report_status_word("GetHubStatus_patchedOpcode");

        // ---------------------------------------------------------------------
        // Step 24: control leg. A legal GetPortStatus must COMPLETE. It also
        // drives wValue, wIndex and ep0_request bits 5:4 back to 0.
        // ---------------------------------------------------------------------
        step(24, "control leg - LEGAL GetPortStatus(port 1) must COMPLETE");
        class_req_in(host_agent_h, usb_cfg, INV_BREQ_GET_STATUS,
                     16'h0000, INV_PORT_OK, INV_STATUS_LEN,
                     "GetPortStatus_final");
        check_setup_stalled(INV_MUST_COMPLETE, "GetPortStatus_final",
                            "a supported request must not be stalled");
        report_status_word("GetPortStatus_final");

        `uvm_info(MSG_ID,
            $sformatf("Hub class-request INVALID sequence complete: %0d additional stall legs.",
                      stall_legs), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Hub class request with explicit direction and recipient. The parent's
    // class_req()/class_req_in() hardcode recipient OTHER (a port); the
    // hub-itself legs need recipient DEVICE.
    // -------------------------------------------------------------------------
    task class_req_ex(svt_usb_agent         host_agent_h,
                      svt_usb_configuration usb_cfg,
                      bit [7:0]             dir,
                      bit [7:0]             recip,
                      bit [7:0]             brequest,
                      bit [15:0]            wvalue,
                      bit [15:0]            windex,
                      bit [15:0]            wlength,
                      string                label);
        `uvm_info(MSG_ID,
            $sformatf({"%s: issuing CLASS dir=%0d recip=%0d bRequest=0x%02h ",
                       "wValue=0x%04h wIndex=0x%04h wLength=0x%04h to addr %0d."},
                      label, dir, recip, brequest, wvalue, windex, wlength,
                      INV_HUB_ADDR),
            UVM_LOW)
        do_control_xfer(
            .bm_request_type_dir  (dir),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(recip),
            .brequest_val         (brequest),
            .wvalue               (wvalue),
            .windex               (windex),
            .wlength              (wlength),
            .device_addr          (INV_HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // Log a 4-byte status word returned by a completed leg. Reported, not
    // asserted (same policy as the parent's report_port_status()); a short
    // payload is an error because the leg then completed without data.
    // -------------------------------------------------------------------------
    function void report_status_word(string label);
        bit [31:0]   status_word;
        int unsigned nbytes;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured.", label))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 4) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: returned %0d payload byte(s), expected 4.",
                          label, nbytes))
            return;
        end

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};

        `uvm_info(MSG_ID,
            $sformatf("%s: status word 0x%08x (status 0x%04h, change 0x%04h).",
                      label, status_word, status_word[15:0], status_word[31:16]),
            UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_SEQUENCE_SV
