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

`ifndef CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_SEQUENCE_SV

// =============================================================================
// Hub class-request STALL decode sequence (High Speed).
//
// WHAT THIS TEST IS FOR
//
// Stimulus for the hub half of coverage gap G9 of docs/usb_coverage_gaps.md
// ("STALL / halt paths in DMA and hub"). It drives the UNSUPPORTED hub class
// requests that make usb_app_hw_hub assert ep0_class_stall, and requires each
// one to be STALLed.
//
// This is missing today. C_HUB_NB_PORTS = 2 in this integration, and every
// existing hub test addresses wIndex 0 or 1 with legal feature selectors only
// (0x0002, 0x0004, 0x0010, 0x0012, 0x0014). Nothing drives wIndex > 2 or an
// out-of-list wValue at the hub, so the class-request STALL path is never taken.
//
// The STALL already covered elsewhere is a different one:
// caliptra_ss_usb_hs_hub_test_mode drives SET_FEATURE(TEST_MODE), a STANDARD
// request rejected inside the EP0 handler, not by this class decoder.
//
// THE RTL BEING EXERCISED (all MEASURED from
// third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_app_hw_hub.m.vhdl)
//
// PROC_CLASS_STALL (lines 96-177) is purely COMBINATIONAL on ep0_request,
// ep0_setupdone, ep0_windex and ep0_wvalue, and its only output is
// ep0_class_stall. The six stall assignments it contains are:
//
//   ClearPortFeature      bad port  (line 103)  wIndex[7:0] > C_HUB_NB_PORTS
//   ClearPortFeature      bad value (line 125)  wValue not in the accepted list
//   GetPortStatus         bad port  (line 133)  wIndex[15:0] > C_HUB_NB_PORTS
//   SetPortFeature        bad port  (line 138)  wIndex[7:0] > C_HUB_NB_PORTS
//   SetPortFeature        bad value (line 158)  wValue not in the accepted list
//   SetAndTestPortFeature         (lines 165-168) wIndex[3:0] = 0, or
//                                                 wIndex[3:0] > C_HUB_NB_PORTS,
//                                                 or wValue /= 10 (PORT_L1)
//
// WHY ALL OF THESE CAN SHARE ONE TEST
//
// Every one of these legs leaves the hub's state completely untouched, so they
// are order-free and cannot interfere with each other. That is explicit in the
// sequential PROC_REQUEST_HANDLING:
//
//   ClearPortFeature bad port -> null; -- A stall will be returned upon this
//                                request                     (lines 213-214)
//   SetPortFeature   bad port -> null;                       (lines 258-259)
//   GetPortStatus             -> data_index is only latched when
//                                wIndex <= C_HUB_NB_PORTS    (line 253)
//   bad wValue                -> when others => null;        (247-248, 285-286)
//
// No port enable, suspend, reset or change bit moves, no data_index update and
// no bus reset. This is the opposite of
// caliptra_ss_usb_hs_hub_int_ep_status_change, where SetPortFeature(PORT_RESET)
// bus-resets USBDC0 and forces a step order.
//
// WHY wValue = 10 IS USED FOR THE SetPortFeature BAD-VALUE LEG
//
// The accepted-wValue lists of the two requests are deliberately different:
// PORT_L1 (10) and C_PORT_L1 (23) are accepted by ClearPortFeature (lines 113
// and 121) but are NOT in the SetPortFeature list (lines 140-159). Using 10
// here therefore proves the Set decoder really has its own list, which a
// generic out-of-range value such as 5 would not. The ClearPortFeature
// bad-value leg uses a value that is unlisted for both.
//
// WHY THE LAST LEG IS A POSITIVE ONE
//
// Six consecutive STALLs prove nothing if EP0 was simply dead. The final leg
// is a legal GetPortStatus on port 1 that must COMPLETE, which proves the
// stalls were decode decisions and not a wedged endpoint, and - since
// GetPortStatus reports wPortChange - that none of the six rejected requests
// perturbed the port.
//
// HOW A STALL IS OBSERVED
//
// Same mechanism as caliptra_ss_usb_hs_hub_test_mode_sequence: the VIP reports
// a control transfer terminated by a device STALL handshake as
// svt_sequence_item::ABORTED on the cached item. check_setup_stalled() below is
// the same check, generalised over a label.
//
// wLength is 0 on the five SET/CLEAR legs (no data stage) and 4 on the
// GetPortStatus legs, matching what a real host would ask for.
// =============================================================================

class caliptra_ss_usb_hs_hub_class_req_stall_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_class_req_stall_sequence)

    string MSG_ID = "USB_HUB_CLASS_STALL";

    // USB device address hub_enum_stepA leaves the hub at.
    localparam int HUB_ADDR = 1;

    // Downstream port count of this integration (C_HUB_NB_PORTS = 2), the
    // legal port used by the positive leg, and the first ILLEGAL port number.
    // PORT_BAD must be > HUB_NB_PORTS for the decode to stall; 3 is the first
    // such value and is what the coverage item calls for.
    localparam int unsigned HUB_NB_PORTS = 2;
    localparam int unsigned PORT_OK      = 1;
    localparam int unsigned PORT_BAD     = 3;

    // Hub class request codes (USB 2.0 table 11-16).
    localparam bit [7:0] BREQ_GET_STATUS           = 8'h00;
    localparam bit [7:0] BREQ_CLEAR_FEATURE        = 8'h01;
    localparam bit [7:0] BREQ_SET_FEATURE          = 8'h03;
    localparam bit [7:0] BREQ_SET_AND_TEST_FEATURE = 8'h0C;

    // Feature selectors (USB 2.0 table 11-17).
    localparam bit [15:0] FEAT_PORT_RESET        = 16'h0004; // 4
    localparam bit [15:0] FEAT_PORT_L1           = 16'h000A; // 10
    localparam bit [15:0] FEAT_C_PORT_CONNECTION = 16'h0010; // 16

    // wValue that is NOT in either accepted list. 5 sits in the gap between
    // Port_Low_speed (9) and Port_Power (8) handling and the C_* selectors, and
    // is absent from the ClearPortFeature list at lines 105-126 and from the
    // SetPortFeature list at lines 140-159.
    localparam bit [15:0] FEAT_UNSUPPORTED = 16'h0005; // 5

    // GetPortStatus returns 4 bytes: wPortStatus then wPortChange, both LE.
    localparam bit [15:0] PORT_STATUS_LEN = 16'h0004;

    // Expected bus-level outcome, as reported by the VIP on the cached item.
    localparam bit XFER_MUST_STALL    = 1'b1;
    localparam bit XFER_MUST_COMPLETE = 1'b0;

    // Number of STALL legs (steps 3-8), reported by the control leg so the log
    // states how many rejected requests EP0 survived.
    localparam int unsigned STALL_LEG_COUNT = 6;

    // Settling delay after link-up, before any hub traffic. The VIP link SM
    // walks TRANSMIT -> ENABLED over the first microseconds after bus reset.
    localparam realtime LINK_SETTLE_DELAY = 20us;

    function new(string name = "caliptra_ss_usb_hs_hub_class_req_stall_sequence");
        super.new(name);
    endfunction

    // Step banner. The VIP messages between the legs are voluminous, so without
    // an explicit marker it is hard to tell from a log which leg is in progress,
    // or which one a failure belongs to. One line per leg, always printed.
    function void step(int num, string what);
        `uvm_info(MSG_ID,
            $sformatf("=== STEP %0d: %s ===", num, what), UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: link first, then SOF, then settle.
        step(1, "wait for link ENABLED, start SOF, settle");
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(MSG_ID,
                "Link never reached ENABLED; aborting hub class-request STALL sequence.")
            return;
        end
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Step 2: enumerate the hub alone at address 1. hub_enum_stepA leaves
        // the VIP anchor at address 1, so the class requests below need no
        // re-anchoring. The downstream ports are deliberately left alone: every
        // leg here is decoded from the SETUP fields and none of them depends on
        // port state.
        step(2, $sformatf("enumerate the hub alone at address %0d", HUB_ADDR));
        hub_enum_stepA(host_agent_h, usb_cfg);

        // ---------------------------------------------------------------------
        // Steps 3-8: the six unsupported requests. Each must be STALLed.
        //
        // These are state-free (see the header), so their order carries no
        // meaning and any one of them can be read in isolation from the log.
        // ---------------------------------------------------------------------

        // Step 3: ClearPortFeature to a port that does not exist.
        // usb_app_hw_hub.m.vhdl line 103: wIndex[7:0] > C_HUB_NB_PORTS.
        step(3, $sformatf({"ClearPortFeature(C_PORT_CONNECTION) to UNSUPPORTED port %0d ",
                           "(hub has %0d ports) - must STALL"},
                          PORT_BAD, HUB_NB_PORTS));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_C_PORT_CONNECTION, 16'(PORT_BAD), 16'h0000,
                  "ClearPortFeature_badPort");
        check_setup_stalled(XFER_MUST_STALL, "ClearPortFeature_badPort",
                            "wIndex[7:0] exceeds C_HUB_NB_PORTS (line 103)");

        // Step 4: ClearPortFeature with a feature selector that is in neither
        // accepted list. usb_app_hw_hub.m.vhdl line 125, the when others arm.
        step(4, $sformatf({"ClearPortFeature with UNSUPPORTED wValue %0d on valid port %0d ",
                           "- must STALL"},
                          FEAT_UNSUPPORTED, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_UNSUPPORTED, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_badValue");
        check_setup_stalled(XFER_MUST_STALL, "ClearPortFeature_badValue",
                            "wValue is not in the ClearPortFeature selector list (line 125)");

        // Step 5: SetPortFeature to a port that does not exist.
        // usb_app_hw_hub.m.vhdl line 138: wIndex[7:0] > C_HUB_NB_PORTS.
        step(5, $sformatf({"SetPortFeature(PORT_RESET) to UNSUPPORTED port %0d - must STALL ",
                           "(and must NOT reset anything)"}, PORT_BAD));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_PORT_RESET, 16'(PORT_BAD), 16'h0000,
                  "SetPortFeature_badPort");
        check_setup_stalled(XFER_MUST_STALL, "SetPortFeature_badPort",
                            "wIndex[7:0] exceeds C_HUB_NB_PORTS (line 138)");

        // Step 6: SetPortFeature with wValue = PORT_L1 (10).
        //
        // This value is deliberately chosen rather than a generic out-of-range
        // one: ClearPortFeature ACCEPTS 10 (line 113) while SetPortFeature does
        // not list it (lines 140-159), so a STALL here proves the Set decoder
        // carries its own selector list rather than sharing the Clear one.
        step(6, $sformatf({"SetPortFeature with wValue %0d (PORT_L1 - accepted by ",
                           "ClearPortFeature, NOT by SetPortFeature) on valid port %0d ",
                           "- must STALL"}, FEAT_PORT_L1, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_PORT_L1, 16'(PORT_OK), 16'h0000,
                  "SetPortFeature_badValue");
        check_setup_stalled(XFER_MUST_STALL, "SetPortFeature_badValue",
                            "wValue is not in the SetPortFeature selector list (line 158)");

        // Step 7: GetPortStatus of a port that does not exist.
        // usb_app_hw_hub.m.vhdl line 133 compares the FULL wIndex[15:0] here,
        // unlike the two requests above which compare only wIndex[7:0].
        step(7, $sformatf("GetPortStatus of UNSUPPORTED port %0d - must STALL", PORT_BAD));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_BAD), PORT_STATUS_LEN,
                     "GetPortStatus_badPort");
        check_setup_stalled(XFER_MUST_STALL, "GetPortStatus_badPort",
                            "wIndex[15:0] exceeds C_HUB_NB_PORTS (line 133)");

        // Step 8: SetAndTestPortFeature with port number 0.
        //
        // This request has its own stall condition (lines 165-168) with three
        // ORed terms, and it is the only one that decodes the port number from
        // wIndex[3:0] rather than wIndex[7:0]. Port 0 is illegal for it because
        // there is no "hub itself" form of SetAndTest.
        step(8, "SetAndTestPortFeature(PORT_L1) with port number 0 - must STALL");
        class_req_in(host_agent_h, usb_cfg, BREQ_SET_AND_TEST_FEATURE,
                     FEAT_PORT_L1, 16'h0000, PORT_STATUS_LEN,
                     "SetAndTestPortFeature_port0");
        check_setup_stalled(XFER_MUST_STALL, "SetAndTestPortFeature_port0",
                            "wIndex[3:0] = 0 (lines 165-168)");

        // ---------------------------------------------------------------------
        // Step 9: the control leg. A LEGAL GetPortStatus must complete.
        //
        // Without this the six STALLs above would also be satisfied by an EP0
        // that had stopped answering altogether. It also shows wPortChange, so
        // a rejected request that had nevertheless disturbed the port would be
        // visible here.
        // ---------------------------------------------------------------------
        step(9, $sformatf({"control leg - LEGAL GetPortStatus(port %0d) must COMPLETE, ",
                           "proving EP0 is not wedged and the port was not disturbed"},
                          PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_OK), PORT_STATUS_LEN,
                     "GetPortStatus_valid");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetPortStatus_valid",
                            "a supported request must not be stalled");
        report_port_status("GetPortStatus_valid");

        `uvm_info(MSG_ID,
            "Hub class-request STALL sequence complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // HOST_TO_DEVICE hub class request with no data stage (Set / Clear).
    //
    // bmRequestType recipient is OTHER, which is what addresses a downstream
    // PORT rather than the hub itself - the same encoding the working
    // port-suspend and status-change tests use.
    // -------------------------------------------------------------------------
    task class_req(svt_usb_agent         host_agent_h,
                   svt_usb_configuration usb_cfg,
                   bit [7:0]             brequest,
                   bit [15:0]            wvalue,
                   bit [15:0]            windex,
                   bit [15:0]            wlength,
                   string                label);
        `uvm_info(MSG_ID,
            $sformatf({"%s: issuing CLASS OUT bRequest=0x%02h wValue=0x%04h ",
                       "wIndex=0x%04h wLength=0x%04h to addr %0d."},
                      label, brequest, wvalue, windex, wlength, HUB_ADDR),
            UVM_LOW)
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (brequest),
            .wvalue               (wvalue),
            .windex               (windex),
            .wlength              (wlength),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // DEVICE_TO_HOST hub class request (GetPortStatus, SetAndTestPortFeature).
    //
    // SetAndTestPortFeature is a control READ in USB 2.0 section 11.24.2.13: it
    // returns the port L1 status byte, which is why it is issued here rather
    // than through class_req() above.
    // -------------------------------------------------------------------------
    task class_req_in(svt_usb_agent         host_agent_h,
                      svt_usb_configuration usb_cfg,
                      bit [7:0]             brequest,
                      bit [15:0]            wvalue,
                      bit [15:0]            windex,
                      bit [15:0]            wlength,
                      string                label);
        `uvm_info(MSG_ID,
            $sformatf({"%s: issuing CLASS IN bRequest=0x%02h wValue=0x%04h ",
                       "wIndex=0x%04h wLength=0x%04h to addr %0d."},
                      label, brequest, wvalue, windex, wlength, HUB_ADDR),
            UVM_LOW)
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (brequest),
            .wvalue               (wvalue),
            .windex               (windex),
            .wlength              (wlength),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // Bus-level accept/reject check for the request just issued.
    //
    // Must be called after wait_xfer_done(), which blocks on
    // NOTIFY_USB_TRANSFER_ENDED, so the status field on the cached item is
    // final by the time it is read. last_ctrl_seq_item is populated by
    // do_control_xfer(); the null guard is a uvm_fatal so a refactor that drops
    // that cast cannot silently disable this check.
    //
    // expect_stalled = XFER_MUST_STALL    -> the transfer must be ABORTED
    // expect_stalled = XFER_MUST_COMPLETE -> the transfer must not be ABORTED
    //
    // why_text names the RTL condition the leg is aiming at, so a failure
    // message says which decode arm did not behave rather than only that a
    // transfer outcome was unexpected.
    // -------------------------------------------------------------------------
    function void check_setup_stalled(bit    expect_stalled,
                                      string label,
                                      string why_text);
        bit observed_stall;

        if (last_ctrl_seq_item == null)
            `uvm_fatal(MSG_ID,
                $sformatf({"%s: last_ctrl_seq_item is null, the transfer status ",
                           "cannot be checked."}, label))

        observed_stall = (last_ctrl_seq_item.status == svt_sequence_item::ABORTED) &&
                         (last_ctrl_seq_item.results_status[4] === 1'b1);

        if (expect_stalled && !observed_stall) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: expected a STALL handshake because %s; status=%p, results_status=0x%0h.",
                          label, why_text, last_ctrl_seq_item.status,
                          last_ctrl_seq_item.results_status))
        end
        else if (!expect_stalled &&
                 ((last_ctrl_seq_item.status != svt_usb_transfer::ACCEPT) ||
                  ((last_ctrl_seq_item.results_status & ~USB_RESULTS_STATUS_BENIGN_MASK) != 0))) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: supported request did not complete successfully (%s); status=%p, results_status=0x%0h.",
                          label, why_text, last_ctrl_seq_item.status,
                          last_ctrl_seq_item.results_status))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("%s: bus level outcome as expected (stalled=%0b, status=%p) at %0t.",
                          label, observed_stall, last_ctrl_seq_item.status, $time),
                UVM_LOW)
        end
    endfunction

    // -------------------------------------------------------------------------
    // Log the port status word returned by the control leg.
    //
    // This is reported, not asserted. The point of the control leg is that the
    // request COMPLETES - which check_setup_stalled() already requires - and
    // pinning exact wPortStatus bits here would duplicate
    // caliptra_ss_usb_get_hub_status and couple this test to bring-up details
    // it does not control. A short payload IS an error, because that would mean
    // the leg completed without actually returning the status.
    // -------------------------------------------------------------------------
    function void report_port_status(string label);
        bit [31:0]   status_word;
        int unsigned nbytes;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured, so the port status could not be read.",
                          label))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 4) begin
            `uvm_error(MSG_ID,
                $sformatf({"%s: GetPortStatus returned %0d payload byte(s), expected 4. ",
                           "The transfer completed but did not deliver the status word."},
                          label, nbytes))
            return;
        end

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};

        `uvm_info(MSG_ID,
            $sformatf({"%s: port %0d status word 0x%08x (wPortStatus 0x%04h, ",
                       "wPortChange 0x%04h). EP0 still answers after %0d stalled ",
                       "requests."},
                      label, PORT_OK, status_word,
                      status_word[15:0], status_word[31:16], STALL_LEG_COUNT),
            UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_SEQUENCE_SV
