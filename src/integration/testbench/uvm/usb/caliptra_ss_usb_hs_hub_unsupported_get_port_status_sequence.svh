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

`ifndef CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_SEQUENCE_SV

// =============================================================================
// Hub GetPortStatus on an UNSUPPORTED port (High Speed, hub only).
//
// Suffix / MSG_ID: HUB_UNSUPPORTED_GET_PORT_STATUS
//
// A code / branch coverage test for the hub class decoder
// usb_app_hw_hub.m.vhdl (the third_party/usb2 copy, which is the one the
// regression compiles - see src/integration/config/usb_hub_upstream.vhdl.vf).
// Written as a host-misbehaviour scenario: TWENTY-THREE EP0 control transfers
// to the hub at address 1, ten of which must be STALLed. No data endpoint is
// touched and no device controller is enumerated.
//
// Despite the name, this covers unsupported PORT NUMBERS **and** unsupported
// FEATURE SELECTORS, on GetPortStatus, ClearPortFeature, SetPortFeature and
// SetAndTestPortFeature. The name is kept because it is referenced by the
// master test list, three regression ymls and the MSG_ID suffix.
//
// This sequence extends caliptra_ss_usb_base_sequence directly and is
// deliberately NOT derived from caliptra_ss_usb_hs_hub_class_req_stall_sequence
// or from the class_req_invalid sequence: it must hold its target arms on its
// own, and unlike class_req_invalid it needs NO firmware SETUP-table patch.
//
// -----------------------------------------------------------------------------
// 1. LINE NUMBERING (read this before changing any step)
// -----------------------------------------------------------------------------
//
// The requested target lines were given in the OLD usb2 numbering, which is
// 9 lines behind today's file (a GEN_HIRD_ARRAY block was inserted at the top).
// Mapped against the current file and against the merged coverage report:
//
//   requested  current  process                 arm
//   128        137      PROC_CLASS_STALL        else --ClearHubFeature  null
//   161        170      PROC_CLASS_STALL        else --SetHubFeature    null
//   214        223      PROC_REQUEST_HANDLING   ClearPortFeature bad port  null
//   228        237      PROC_REQUEST_HANDLING   ClearPortFeature accepted no-op
//
// Never trust a requested line number for this file: map it against the merged
// coverage report first.
//
// -----------------------------------------------------------------------------
// 2. MEASURED: those four arms were ALREADY COVERED when this test was written
// -----------------------------------------------------------------------------
//
// The merge of 2026-11-26 reports 137 / 170 / 223 / 237 at 1/1, closed by
// caliptra_ss_usb_hs_hub_class_req_invalid (note 39), which ran and PASSED in
// that nightly. An older merged report still showed them as holes, which is
// the stale artefact note 39 was written against.
//
// This test therefore re-covers them INDEPENDENTLY - no table patch, its own
// parent - and additionally targets the two branch holes that really were
// still open, see section 4.
//
// -----------------------------------------------------------------------------
// 3. TWO FILTERS SIT BETWEEN THE HOST AND usb_app_hw_hub (MEASURED)
// -----------------------------------------------------------------------------
//
// a) The hub SETUP-match table (usb_ep0_hub_descr.m.vhdl:362-365 for
//    GetHubPortStatus) compares wIndex with mask 0xFFFC. Port 3 PASSES the
//    table and is stalled by the hub decoder at line 142; ports 4..255 fall
//    off the table and are stalled one level EARLIER by usb_ep0_handler
//    (205-207 / 239-241), so they add no usb_app_hw_hub coverage. Steps 1..3
//    deliberately exercise all three cases so the two stall layers are
//    distinguished in the log rather than conflated.
//
// b) ep0_request is NOT the host bRequest. It is the 7-bit opcode of the
//    matched table row (usb_ep0_handler.m.vhdl:192), cleared to 0 when no row
//    matches. So an undefined class bRequest never reaches this decoder at
//    all. That is why this test drives only SHIPPED request rows and does not
//    attempt any EP0_REQUEST toggle work - that belongs to note 39's test,
//    which patches a row opcode to do it.
//
// -----------------------------------------------------------------------------
// 4. THE TWO REAL BRANCH HOLES AND HOW THEY ARE REACHED (MEASURED)
// -----------------------------------------------------------------------------
//
// Hole 1 - ClearPortFeature(PORT_L1) with hub_port_l1_int already 0
//   usb_app_hw_hub.m.vhdl:243-247
//
//     when 10 =>                                  --Port_L1
//       hub_port_l1_int(var_port)  <= '0';
//       if hub_port_l1_int(var_port) = '1' then   <-- inner guard
//         hub_port_l1_change(var_port) <= '1';
//       end if;
//
//   The coverage database reports the `10 / 1` combination covered (the L1
//   tests clear a port that really is in L1) and the `10 / 0` combination NOT
//   covered. Step 10 is a ClearPortFeature(PORT_L1) on a port that was never
//   put into L1, which takes the inner guard FALSE leg and its MISSING_ELSE.
//
// Hole 2 - SetAndTestPortFeature(PORT_L1) with the LPM condition FALSE
//   usb_app_hw_hub.m.vhdl:305-315
//
//     if wValue = 10 and hub_port_enable_int(var_port) = '1' then
//       if hub_lpm_sup(var_port) = '1' and
//          hub_lpm_data_pending(var_port) = '0' and
//          ep0_windex(7 downto 4) >= hub_port_lpm_hird_sw_array(var_port) then
//          ...                                    <-- only the TRUE leg is covered
//
//   The outer condition needs the port ENABLED; the inner one is the hole.
//   MEASURED reachability: hub_lpm_sup(i) is driven from dev0_lpm_sup /
//   dev1_lpm_sup (structure lines 2329 / 2331) and hub_port_lpm_hird_sw from
//   dev0_lpm_hird_sw / dev1_lpm_hird_sw (2371 / 2379). This is a HUB-ONLY
//   test, so neither device controller is enumerated and dev*_lpm_sup is 0,
//   which makes the inner condition FALSE and takes exactly the uncovered
//   leg. Step 9 must therefore run BEFORE step 11 (it provides the enable)
//   and step 13 must run after (it takes the enable away again). That
//   ordering is load bearing - do not reorder steps 9..13.
//
// Not reachable from here, recorded as waivers in the handover note:
//   lines 357 / 365  - need a DEVICE-initiated remote wakeup from a suspended
//                      or L1 port, which is the note-33 rig, not an EP0 test.
//   lines 456 / 460  - the C_DATAWIDTH = 32 and the unsupported-width legs.
//                      C_DATAWIDTH is 64 in this configuration, so both are
//                      structurally dead.
//
// -----------------------------------------------------------------------------
// 5. RIG: STALL, NOT SILENCE - SO NO REPORT CATCHER
// -----------------------------------------------------------------------------
//
// Every rejected request here ends in a REAL STALL handshake, which the VIP
// reports cleanly as svt_sequence_item::ABORTED. Nothing times out, so unlike
// the unsupported-endpoint and disabled-endpoint families this test needs no
// uvm_report_catcher and no device_timeout relaxation, and UVM_ERROR must be
// exactly 0 on a passing run. Use that as the discriminator when picking a rig
// for a new negative test: silence needs the catcher rig, STALL needs only
// check_setup_stalled().
//
// -----------------------------------------------------------------------------
// 5.1 INTERLEAVE RULE: NO TWO STALL LEGS ARE EVER ADJACENT
// -----------------------------------------------------------------------------
//
// Every leg that must STALL is immediately followed by a leg that must
// COMPLETE. The resulting pattern over steps 1..23 is
//
//   S C S C S C S C S C S C S C S C C C S C S C C      (10 stalls, 13 completes)
//
// This is a deliberate structural property. Keep it when editing.
//
// WHY. Two different hazards were considered; only the second is real, and
// the interleave addresses a third concern that is not a hazard at all:
//
//  a) Reading the PREVIOUS leg's verdict - IMPOSSIBLE here. do_control_xfer()
//     builds a fresh req object per call and repoints the handle with
//     $cast(last_ctrl_seq_item, req) (base sequence line 346), so there is no
//     carry-over state that could go stale.
//
//  b) Sampling the CURRENT leg mid-flight - REAL. The base sequence documents
//     it at lines 550-575: NOTIFY_USB_TRANSFER_ENDED is a protocol-layer-wide
//     event, so a caller can consume the pulse belonging to the previous
//     transfer and return while its own is still in flight. The signature is
//     status = ABORTED with results_status = 0x0, and the hazard "only bites
//     when two control transfers are issued back to back with no delay",
//     which is exactly what a run of consecutive stall legs is. The
//     interleave removes that condition by construction, and
//     check_setup_stalled() additionally names the signature in its own
//     branch so a future occurrence self-diagnoses.
//
//  c) Proving each stall is FRESH, and localising a wedge. ep0_class_stall is
//     combinational and self-clearing (measured in the FSDB: it pulses for a
//     single ep0_setupdone and drops), so a COMPLETE leg in between gives a
//     measured stall -> no-stall -> stall edge pattern instead of a flat run.
//     More practically: a hub that wedges EP0 on some particular stall is now
//     caught by the very next step rather than only by the final leg, so the
//     failing step number names the culprit.
//
// Note that (b) means the dangerous direction was already closed before the
// interleave: a mid-flight sample has results_status = 0, so bit 4 is clear,
// so it is NOT counted as a stall and the leg fails loudly instead of passing
// falsely. The interleave is defence in depth plus diagnosability, not a fix
// for a known escape.
//
// -----------------------------------------------------------------------------
// 6. STATE SAFETY
// -----------------------------------------------------------------------------
//
// Step 9 sets hub_port_enable_int for port 1 and step 13 clears it again, so
// the decoder is left as it was found. No PORT_RESET is ever issued on a legal
// port, so no bus reset is injected into USBDC0, and the host only ever talks
// to address 1, so the device controller is never addressed. Step 14 is a
// legal GetPortStatus that must COMPLETE, so a DUT that wedges EP0 after the
// first stall cannot pass.
// =============================================================================

class caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence)

    string MSG_ID = "HUB_UNSUPPORTED_GET_PORT_STATUS";

    // USB device address hub_enum_stepA leaves the hub at.
    localparam int HUB_ADDR = 1;

    // C_HUB_NB_PORTS = 2 in this integration
    // (usb_app_hw_hub.m.vhdl:25 generic, usb_ep_config_hub_pkg.p.vhdl).
    localparam int unsigned HUB_NB_PORTS = 2;

    // The legal port used by the positive legs.
    localparam int unsigned PORT_OK = 1;

    // The hub itself rather than a port: wIndex 0 selects GetHubStatus /
    // ClearHubFeature / SetHubFeature.
    localparam bit [15:0] WINDEX_HUB_ITSELF = 16'h0000;

    // First ILLEGAL port number that still PASSES the SETUP-table wIndex mask
    // 0xFFFC, so it reaches the hub decoder and is stalled there (line 142).
    localparam bit [15:0] PORT_BAD_3 = 16'h0003;

    // Illegal port numbers that are rejected one level earlier, by
    // usb_ep0_handler, because they do not match the table row at all.
    localparam bit [15:0] PORT_BAD_4   = 16'h0004;
    localparam bit [15:0] PORT_BAD_1FF = 16'h01FF;

    // Hub class request codes (USB 2.0 table 11-16).
    localparam bit [7:0] BREQ_GET_STATUS           = 8'h00;
    localparam bit [7:0] BREQ_CLEAR_FEATURE        = 8'h01;
    localparam bit [7:0] BREQ_SET_FEATURE          = 8'h03;
    localparam bit [7:0] BREQ_SET_AND_TEST_FEATURE = 8'h0C;

    // Feature selectors (USB 2.0 table 11-17).
    localparam bit [15:0] FEAT_PORT_ENABLE        = 16'h0001; // 1
    // Used by step 13 on an ILLEGAL port only: the request stalls, so no
    // reset is ever issued and USBDC0 sees no bus reset. Never send this to
    // a legal port from this test (see header section 6, STATE SAFETY).
    localparam bit [15:0] FEAT_PORT_RESET         = 16'h0004; // 4
    localparam bit [15:0] FEAT_PORT_POWER         = 16'h0008; // 8
    localparam bit [15:0] FEAT_PORT_L1            = 16'h000A; // 10
    localparam bit [15:0] FEAT_C_PORT_CONNECTION  = 16'h0010; // 16

    // wValue that is in neither accepted selector list, so PROC_CLASS_STALL
    // rejects it. Also not equal to 10, which is what the SET_AND_TEST stall
    // condition at lines 174-177 tests.
    // MEASURED against the four case statements in usb_app_hw_hub.m.vhdl:
    //   PROC_CLASS_STALL      Clear accepts 0,1,2,3,4,8,9,10,16..23  (115-130)
    //   PROC_CLASS_STALL      Set   accepts 0,1,2,3,4,8,9,16..22     (150-163)
    //   PROC_REQUEST_HANDLING Clear handles the same 16 values       (227-255)
    //   PROC_REQUEST_HANDLING Set   handles the same 14 values       (272-294)
    // 5 and 11 are absent from ALL FOUR, so each one takes the
    // `when others` arm in both the stall process (134 / 167) and the action
    // process (257 / 295). Do NOT substitute 23 (C_PORT_L1) or 10 (PORT_L1)
    // here: both are ACCEPTED by Clear, so they would silently stop testing
    // the reject path. Re-derive from the RTL before changing these.
    localparam bit [15:0] FEAT_UNSUPPORTED   = 16'h0005; // 5
    localparam bit [15:0] FEAT_UNSUPPORTED_B = 16'h000B; // 11

    // The hub-itself feature rows (ClearHubFeature / SetHubFeature) carry a
    // wValue mask of 0xFFFE, so only wValue 0 and 1 match the row at all.
    // 0 is C_HUB_LOCAL_POWER and is what a real host sends.
    localparam bit [15:0] FEAT_HUB_LOCAL_POWER = 16'h0000;

    // GetPortStatus / GetHubStatus return 4 bytes: status then change, both LE.
    // GetHubStatus / GetPortStatus return 4 bytes: status then change, both LE.
    // This matches the ROM wLength cap on those two rows
    // (usb_ep0_hub_descr.m.vhdl:357 and :363, high half of word A+2 = 0x0004).
    localparam bit [15:0] STATUS_LEN = 16'h0004;

    // DURABLE: the ROM wLength cap is PER ROW - never share a length constant
    // across rows. SetAndTestHubPortFeature caps at ONE byte
    // (usb_ep0_hub_descr.m.vhdl:423, word A+2 = 0x00010000), because USB 2.0
    // section 11.24.2.13 defines its data stage as a single port-L1 status
    // byte, not a 4-byte status word. Asking for 4 here does NOT stall: the
    // clamp at usb_ep0_handler.m.vhdl:218-220 silently shortens the reply to
    // 1 byte (note 38 section 2), so a checker expecting 4 manufactures a
    // false DUT failure on a leg that actually worked. Measured on the wire:
    // the DUT sent DATA1 PID 0x4B then 0x00 + CRC16 0x40BF - one data byte.
    localparam bit [15:0] L1_STATUS_LEN = 16'h0001;

    // Expected bus-level outcome, as reported by the VIP on the cached item.
    localparam bit XFER_MUST_STALL    = 1'b1;
    localparam bit XFER_MUST_COMPLETE = 1'b0;

    // Number of legs that must STALL. See the interleave rule in the header:
    // steps 1, 3, 5, 7, 9, 11, 13, 15, 19 and 21 - ten stalls, each one
    // immediately followed by a leg that must COMPLETE.
    localparam int unsigned STALL_LEG_COUNT = 10;

    // Settling delay after link-up, before any hub traffic. The VIP link SM
    // walks TRANSMIT -> ENABLED over the first microseconds after bus reset.
    localparam realtime LINK_SETTLE_DELAY = 20us;

    function new(string name = "caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence");
        super.new(name);
    endfunction

    // Step banner. The VIP messages between the legs are voluminous, so
    // without an explicit marker it is hard to tell from a log which leg is in
    // progress, or which one a failure belongs to.
    function void step(int num, string what);
        `uvm_info(MSG_ID,
            $sformatf("=== STEP %0d: %s ===", num, what), UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // Main body
    //
    // INTERLEAVE RULE (see header section 5.1): no two STALL legs are ever
    // adjacent. Every leg that must stall is immediately followed by a leg
    // that must COMPLETE, so each stall is proven FRESH rather than inherited,
    // and a hub that wedges EP0 is caught at the exact step that broke it.
    // When editing, keep the alternation and keep the L1 block ordering
    // (16 enables, 17/18 take the branch holes, 22 restores).
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Link first, then SOF, then settle.
        step(0, "wait for link ENABLED, start SOF, settle, enumerate the hub");
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(MSG_ID,
                {"Link never reached ENABLED; aborting hub unsupported ",
                 "port/feature sequence."})
            return;
        end
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Enumerate the hub ALONE at address 1. hub_enum_stepA leaves the VIP
        // anchor at address 1, so every class request below needs no
        // re-anchoring. The downstream ports are deliberately left unpowered:
        // that is what keeps dev*_lpm_sup at 0, which is what makes the
        // step-18 branch hole reachable (see header section 4).
        hub_enum_stepA(host_agent_h, usb_cfg);

        // ---------------------------------------------------------------------
        // Steps 1-5: GetPortStatus on unsupported port numbers, stalled by TWO
        // DIFFERENT pieces of RTL, with COMPLETE legs in between.
        //
        // Port 3 passes the SETUP-table wIndex mask 0xFFFC and is rejected by
        // the hub decoder (step 1); ports 4 and 0x01FF do not match the row and
        // are rejected one level earlier by usb_ep0_handler (steps 3 and 5), so
        // they add no usb_app_hw_hub coverage. The log lines name which layer
        // fired, which is the point of keeping all three.
        // ---------------------------------------------------------------------

        // Step 1: the headline case. GetPortStatus compares the FULL
        // wIndex[15:0] (line 141), unlike Clear/SetPortFeature which compare
        // only wIndex[7:0]. Port 3 > C_HUB_NB_PORTS so the decoder stalls it,
        // and PROC_REQUEST_HANDLING takes the line-264 MISSING_ELSE because
        // data_index is only latched for a port that exists.
        step(1, $sformatf({"GetPortStatus of UNSUPPORTED port %0d (hub has %0d ports) ",
                           "- must STALL in the HUB DECODER"},
                          PORT_BAD_3, HUB_NB_PORTS));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, PORT_BAD_3, STATUS_LEN,
                     "GetPortStatus_badPort3");
        check_setup_stalled(XFER_MUST_STALL, "GetPortStatus_badPort3",
                            {"wIndex[15:0] exceeds C_HUB_NB_PORTS, ",
                             "usb_app_hw_hub.m.vhdl:141-142"});

        // Step 2: SEPARATOR and discriminator. GetHubStatus is the SAME
        // bRequest with wIndex 0, which selects the hub itself and IS
        // supported. It proves step 1 was rejected for the port number rather
        // than because GetStatus is broken, and it takes the data_index <= 0
        // leg at lines 262-263.
        step(2, "SEPARATOR: GetHubStatus (same bRequest, wIndex 0 = the hub) - must COMPLETE");
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, WINDEX_HUB_ITSELF, STATUS_LEN,
                     "GetHubStatus_valid");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetHubStatus_valid",
                            {"wIndex 0 selects the hub itself, which is supported, ",
                             "usb_app_hw_hub.m.vhdl:262-263"});
        report_status_word("GetHubStatus_valid", 0, 4);

        // Step 3: one past the mask. Port 4 fails the SETUP-table comparison
        // (mask 0xFFFC), so the walk falls off the end of the table and
        // usb_ep0_handler stalls it. This never reaches usb_app_hw_hub.
        step(3, $sformatf({"GetPortStatus of port %0d - must STALL EARLIER, in ",
                           "usb_ep0_handler (SETUP-table wIndex mask 0xFFFC)"},
                          PORT_BAD_4));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, PORT_BAD_4, STATUS_LEN,
                     "GetPortStatus_badPort4");
        check_setup_stalled(XFER_MUST_STALL, "GetPortStatus_badPort4",
                            {"wIndex does not match the GetHubPortStatus row, ",
                             "usb_ep0_handler.m.vhdl:205-207 / 239-241"});

        // Step 4: SEPARATOR on the legal port.
        step(4, $sformatf("SEPARATOR: LEGAL GetPortStatus(port %0d) - must COMPLETE", PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_OK), STATUS_LEN,
                     "GetPortStatus_sep4");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetPortStatus_sep4",
                            "a supported request must not be stalled");
        report_status_word("GetPortStatus_sep4", PORT_OK, 4);

        // Step 5: a port number with bits set in the UPPER byte as well, which
        // also drives the EP0_WINDEX high bits on a request that is rejected.
        step(5, $sformatf({"GetPortStatus of port 0x%04h (upper wIndex byte set) ",
                           "- must STALL"}, PORT_BAD_1FF));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, PORT_BAD_1FF, STATUS_LEN,
                     "GetPortStatus_badPort1FF");
        check_setup_stalled(XFER_MUST_STALL, "GetPortStatus_badPort1FF",
                            {"wIndex does not match the GetHubPortStatus row, ",
                             "usb_ep0_handler.m.vhdl:205-207 / 239-241"});

        // ---------------------------------------------------------------------
        // Steps 6-9: the hub-itself feature requests (ACCEPTED no-ops, the
        // `else --ClearHubFeature / SetHubFeature` null arms at 137 and 170)
        // alternating with the UNSUPPORTED feature selectors that must stall.
        //
        // wValue must be 0 on the hub-itself legs because those rows carry a
        // wValue mask of 0xFFFE, so only 0 and 1 match the row at all.
        // ---------------------------------------------------------------------

        // Step 6: SEPARATOR + target 136-137.
        step(6, "SEPARATOR: ClearHubFeature(C_HUB_LOCAL_POWER) wIndex 0 - must COMPLETE as a no-op");
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_HUB_LOCAL_POWER, WINDEX_HUB_ITSELF, 16'h0000,
                  "ClearHubFeature_hubItself");
        check_setup_stalled(XFER_MUST_COMPLETE, "ClearHubFeature_hubItself",
                            {"the hub-itself form is accepted and has no effect, ",
                             "usb_app_hw_hub.m.vhdl:136-137"});

        // Step 7: ClearPortFeature with a feature selector that is in NEITHER
        // accepted list. One request covers two arms: PROC_CLASS_STALL raises
        // the stall at its `when others` (line 134) and PROC_REQUEST_HANDLING
        // takes its own `when others => null` (line 257) in the same cycle.
        step(7, $sformatf({"ClearPortFeature with UNSUPPORTED wValue %0d on valid port %0d ",
                           "- must STALL"}, FEAT_UNSUPPORTED, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_UNSUPPORTED, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_badValue");
        check_setup_stalled(XFER_MUST_STALL, "ClearPortFeature_badValue",
                            {"wValue is in neither ClearPortFeature list, stall at ",
                             "usb_app_hw_hub.m.vhdl:133-134 and no action at :256-257"});

        // Step 8: SEPARATOR + target 169-170.
        step(8, "SEPARATOR: SetHubFeature(C_HUB_LOCAL_POWER) wIndex 0 - must COMPLETE as a no-op");
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_HUB_LOCAL_POWER, WINDEX_HUB_ITSELF, 16'h0000,
                  "SetHubFeature_hubItself");
        check_setup_stalled(XFER_MUST_COMPLETE, "SetHubFeature_hubItself",
                            {"the hub-itself form is accepted and has no effect, ",
                             "usb_app_hw_hub.m.vhdl:169-170"});

        // Step 9: the Set-side mirror of step 7, covering lines 167 and 295.
        step(9, $sformatf({"SetPortFeature with UNSUPPORTED wValue %0d on valid port %0d ",
                           "- must STALL"}, FEAT_UNSUPPORTED, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_UNSUPPORTED, 16'(PORT_OK), 16'h0000,
                  "SetPortFeature_badValue");
        check_setup_stalled(XFER_MUST_STALL, "SetPortFeature_badValue",
                            {"wValue is in neither SetPortFeature list, stall at ",
                             "usb_app_hw_hub.m.vhdl:166-167 and no action at :294-295"});

        // ---------------------------------------------------------------------
        // Steps 10-15: accepted no-op port features alternating with bad-port
        // rejections on both Clear and Set.
        //
        // PORT_POWER is the chosen no-op selector because this hub has only
        // embedded ports, so power is fixed on (hub_status bit 8 is hardwired
        // to '1', line 391) and touching it cannot disturb anything.
        // ---------------------------------------------------------------------

        // Step 10: SEPARATOR + the long accepted-no-action arm at line 237.
        step(10, $sformatf({"SEPARATOR: ClearPortFeature(PORT_POWER) on valid port %0d ",
                            "- must COMPLETE and do nothing"}, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_PORT_POWER, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_portPower_noop");
        check_setup_stalled(XFER_MUST_COMPLETE, "ClearPortFeature_portPower_noop",
                            {"an accepted selector with no action, ",
                             "usb_app_hw_hub.m.vhdl:227-237"});

        // Step 11: ClearPortFeature on the bad port. PROC_CLASS_STALL raises
        // the stall (line 112) and PROC_REQUEST_HANDLING takes its own `null`
        // arm at line 223 in the same cycle.
        step(11, $sformatf({"ClearPortFeature(C_PORT_CONNECTION) on UNSUPPORTED port %0d ",
                            "- must STALL and change no port state"}, PORT_BAD_3));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_C_PORT_CONNECTION, PORT_BAD_3, 16'h0000,
                  "ClearPortFeature_badPort3");
        check_setup_stalled(XFER_MUST_STALL, "ClearPortFeature_badPort3",
                            {"wIndex[7:0] exceeds C_HUB_NB_PORTS, stall at :111-112 ",
                             "and the no-action arm at :222-223"});

        // Step 12: SEPARATOR + the Set-side accepted-no-action arm at line 284.
        step(12, $sformatf({"SEPARATOR: SetPortFeature(PORT_POWER) on valid port %0d ",
                            "- must COMPLETE and do nothing"}, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_PORT_POWER, 16'(PORT_OK), 16'h0000,
                  "SetPortFeature_portPower_noop");
        check_setup_stalled(XFER_MUST_COMPLETE, "SetPortFeature_portPower_noop",
                            {"an accepted selector with no action, ",
                             "usb_app_hw_hub.m.vhdl:272-284"});

        // Step 13: the Set-side bad port, covering the `null` arm at line 268.
        // PORT_RESET is deliberate: the stall means NO reset is issued, so the
        // negative result is also that USBDC0 sees no bus reset.
        step(13, $sformatf({"SetPortFeature(PORT_RESET) on UNSUPPORTED port %0d - must STALL ",
                            "and must NOT reset anything"}, PORT_BAD_3));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_PORT_RESET, PORT_BAD_3, 16'h0000,
                  "SetPortFeature_badPort3");
        check_setup_stalled(XFER_MUST_STALL, "SetPortFeature_badPort3",
                            {"wIndex[7:0] exceeds C_HUB_NB_PORTS, stall at :146-147 ",
                             "and the no-action arm at :267-268"});

        // Step 14: SEPARATOR. A legal GetPortStatus also shows wPortChange, so
        // if step 13 had wrongly reset the port it is visible right here.
        step(14, $sformatf({"SEPARATOR: LEGAL GetPortStatus(port %0d) - must COMPLETE and ",
                            "show the port was not reset"}, PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_OK), STATUS_LEN,
                     "GetPortStatus_sep14");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetPortStatus_sep14",
                            "a supported request must not be stalled");
        report_status_word("GetPortStatus_sep14", PORT_OK, 4);

        // Step 15: a SECOND unlisted selector on Clear. This proves the
        // line-134 stall is driven by the VALUE and not by the port number,
        // which step 7 alone cannot distinguish from step 11.
        step(15, $sformatf({"ClearPortFeature with a second UNSUPPORTED wValue %0d on valid ",
                            "port %0d - must STALL (value-driven, not port-driven)"},
                           FEAT_UNSUPPORTED_B, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_UNSUPPORTED_B, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_badValueB");
        check_setup_stalled(XFER_MUST_STALL, "ClearPortFeature_badValueB",
                            {"wValue is in neither ClearPortFeature list, ",
                             "usb_app_hw_hub.m.vhdl:133-134"});

        // ---------------------------------------------------------------------
        // Steps 16-22: the L1 branch holes. THIS ORDER IS LOAD BEARING.
        //
        // Step 16 enables port 1, which is the outer precondition of the
        // SET_AND_TEST handler (line 306). Steps 17-18 take the two uncovered
        // inner legs. Step 22 disables the port again so no state is left
        // behind. See header section 4. Steps 17 and 18 are both COMPLETE legs
        // so there is nothing to bracket between them.
        // ---------------------------------------------------------------------

        // Step 16: SEPARATOR after step 15, and the arm at 285-286.
        step(16, $sformatf({"SEPARATOR: SetPortFeature(PORT_ENABLE) on port %0d - must ",
                            "COMPLETE (arms the SET_AND_TEST precondition for steps 17-18)"},
                           PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_SET_FEATURE,
                  FEAT_PORT_ENABLE, 16'(PORT_OK), 16'h0000,
                  "SetPortFeature_portEnable");
        check_setup_stalled(XFER_MUST_COMPLETE, "SetPortFeature_portEnable",
                            {"PORT_ENABLE is an accepted SetPortFeature selector, ",
                             "usb_app_hw_hub.m.vhdl:285-286"});

        // Step 17: BRANCH HOLE 1. The port has never been put into L1, so
        // hub_port_l1_int is 0 and the inner `if hub_port_l1_int = '1'` guard
        // at line 245 must take its FALSE leg: the L1 change bit must NOT be
        // set. PORT_L1 is an accepted ClearPortFeature selector (line 122), so
        // the request itself completes.
        step(17, $sformatf({"BRANCH HOLE: ClearPortFeature(PORT_L1) on port %0d which is ",
                            "NOT in L1 - must COMPLETE and must NOT set the L1 change bit"},
                           PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_PORT_L1, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_portL1_notInL1");
        check_setup_stalled(XFER_MUST_COMPLETE, "ClearPortFeature_portL1_notInL1",
                            {"PORT_L1 is an accepted ClearPortFeature selector and the ",
                             "inner guard must be FALSE, usb_app_hw_hub.m.vhdl:243-247"});

        // Step 18: BRANCH HOLE 2. SetAndTestPortFeature(PORT_L1) on the now
        // ENABLED port 1. The outer condition at line 305-306 is TRUE, so the
        // handler evaluates the inner LPM condition at 307-309 - and because
        // this is a hub-only test, hub_lpm_sup(0) (= dev0_lpm_sup) is 0, so
        // that condition is FALSE and the uncovered leg is taken: no L1 entry,
        // no L1 change. The request itself is accepted by PROC_CLASS_STALL
        // because wIndex[3:0] = 1 is a legal port and wValue IS 10.
        //
        // This is a control READ (USB 2.0 section 11.24.2.13) and returns ONE
        // port-L1 status byte, not a 4-byte status word - the row's ROM
        // wLength cap is 1 (usb_ep0_hub_descr.m.vhdl:423), so L1_STATUS_LEN
        // must be used here and NOT STATUS_LEN. See the L1_STATUS_LEN comment:
        // asking for 4 does not stall, it is silently clamped to 1, and the
        // first revision of this test failed exactly that way.
        //
        // The byte is reported, not asserted. hub_l1_status would be
        // C_LPM_STALL (0x30, line 406) with hub_lpm_sup = 0, but it is
        // selected by data_index, which latches on the same ep0_setupdone edge
        // that starts this transfer, so the byte actually on the wire is the
        // pre-update entry (measured: 0x00). Pinning it would couple this test
        // to LPM bring-up details it does not control.
        step(18, $sformatf({"BRANCH HOLE: SetAndTestPortFeature(PORT_L1) on ENABLED port %0d ",
                            "with LPM unsupported - must COMPLETE and must NOT enter L1"},
                           PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_SET_AND_TEST_FEATURE,
                     FEAT_PORT_L1, 16'(PORT_OK), L1_STATUS_LEN,
                     "SetAndTestPortFeature_lpmUnsupported");
        check_setup_stalled(XFER_MUST_COMPLETE, "SetAndTestPortFeature_lpmUnsupported",
                            {"legal port and wValue 10, but hub_lpm_sup is 0 so the inner ",
                             "LPM condition must be FALSE, usb_app_hw_hub.m.vhdl:305-315"});
        report_status_word("SetAndTestPortFeature_lpmUnsupported", PORT_OK, 1);

        // Step 19: the SET_AND_TEST stall condition, THIRD ORed term - the port
        // number is legal but the feature selector is not PORT_L1.
        //
        // L1_STATUS_LEN again: the length is immaterial on a leg that stalls
        // before any data stage, but asking for 4 on a cap-1 row would be
        // misleading to the next reader.
        step(19, $sformatf({"SetAndTestPortFeature with wValue %0d (not PORT_L1) on valid ",
                            "port %0d - must STALL"}, FEAT_UNSUPPORTED, PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_SET_AND_TEST_FEATURE,
                     FEAT_UNSUPPORTED, 16'(PORT_OK), L1_STATUS_LEN,
                     "SetAndTestPortFeature_badValue");
        check_setup_stalled(XFER_MUST_STALL, "SetAndTestPortFeature_badValue",
                            {"the feature selector is not PORT_L1, ",
                             "usb_app_hw_hub.m.vhdl:174-177"});

        // Step 20: SEPARATOR.
        step(20, $sformatf("SEPARATOR: LEGAL GetPortStatus(port %0d) - must COMPLETE", PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_OK), STATUS_LEN,
                     "GetPortStatus_sep20");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetPortStatus_sep20",
                            "a supported request must not be stalled");
        report_status_word("GetPortStatus_sep20", PORT_OK, 4);

        // Step 21: the SET_AND_TEST stall condition, FIRST ORed term -
        // wIndex[3:0] = 0. There is no "hub itself" form of SetAndTest, so
        // port 0 is illegal for it even though wValue IS PORT_L1. This is the
        // complement of step 19 and covers the other term at line 174.
        step(21, "SetAndTestPortFeature(PORT_L1) with port number 0 - must STALL");
        class_req_in(host_agent_h, usb_cfg, BREQ_SET_AND_TEST_FEATURE,
                     FEAT_PORT_L1, WINDEX_HUB_ITSELF, L1_STATUS_LEN,
                     "SetAndTestPortFeature_port0");
        check_setup_stalled(XFER_MUST_STALL, "SetAndTestPortFeature_port0",
                            {"wIndex[3:0] = 0 is illegal for SetAndTest, ",
                             "usb_app_hw_hub.m.vhdl:174"});

        // Step 22: SEPARATOR, and give the port back. Without this the enable
        // bit set by step 16 would outlive the sequence.
        step(22, $sformatf({"SEPARATOR: ClearPortFeature(PORT_ENABLE) on port %0d - restore ",
                            "the state step 16 changed"}, PORT_OK));
        class_req(host_agent_h, usb_cfg, BREQ_CLEAR_FEATURE,
                  FEAT_PORT_ENABLE, 16'(PORT_OK), 16'h0000,
                  "ClearPortFeature_portEnable_restore");
        check_setup_stalled(XFER_MUST_COMPLETE, "ClearPortFeature_portEnable_restore",
                            {"PORT_ENABLE is an accepted ClearPortFeature selector, ",
                             "usb_app_hw_hub.m.vhdl:238-239"});

        // ---------------------------------------------------------------------
        // Step 23: the final control leg.
        //
        // Every stall above is already bracketed by a COMPLETE leg, so this is
        // belt-and-braces rather than the sole recovery proof it used to be.
        // It still reports wPortChange, so a rejected request that had
        // nevertheless disturbed the port is visible here.
        // ---------------------------------------------------------------------
        step(23, $sformatf({"control leg - LEGAL GetPortStatus(port %0d) must COMPLETE, ",
                            "proving EP0 is not wedged and the port was not disturbed"},
                           PORT_OK));
        class_req_in(host_agent_h, usb_cfg, BREQ_GET_STATUS,
                     16'h0000, 16'(PORT_OK), STATUS_LEN,
                     "GetPortStatus_valid");
        check_setup_stalled(XFER_MUST_COMPLETE, "GetPortStatus_valid",
                            "a supported request must not be stalled");
        report_status_word("GetPortStatus_valid", PORT_OK, 4);

        `uvm_info(MSG_ID,
            $sformatf({"Hub unsupported port/feature sequence complete: %0d stalled ",
                       "legs, each one followed by a COMPLETE leg, EP0 still answering."},
                      STALL_LEG_COUNT),
            UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // HOST_TO_DEVICE hub class request with no data stage (Set / Clear).
    //
    // bmRequestType recipient is OTHER, which is what addresses a downstream
    // PORT as well as, with wIndex 0, the hub itself - the same encoding the
    // working port-suspend and status-change tests use.
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
    // DEVICE_TO_HOST hub class request (GetHubStatus, GetPortStatus,
    // SetAndTestPortFeature).
    //
    // SetAndTestPortFeature is a control READ in USB 2.0 section 11.24.2.13:
    // it returns the port L1 status byte, which is why it is issued here
    // rather than through class_req() above.
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
    // do_control_xfer(); the null guard is a uvm_fatal so a refactor that
    // drops that cast cannot silently disable this check.
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

        // ABORTED with results_status == 0 is NOT a device failure. The base
        // sequence documents it (caliptra_ss_usb_base_sequence.svh:550-575):
        // NOTIFY_USB_TRANSFER_ENDED is a protocol-layer-wide event, so a
        // caller can consume the pulse belonging to the PREVIOUS transfer and
        // sample this one mid-flight. Per svt_usb_transfer an all-zero
        // results_status means a successful transfer, so ABORTED with no
        // reason bit set is set_aborted_status() sweeping a still-active
        // transfer, not a stall and not an error from the DUT.
        //
        // The interleave rule in the header makes this unreachable by
        // construction (the hazard needs two control transfers back to back,
        // and no two stalls are adjacent here), so this branch is a named
        // diagnostic rather than an expected path. Report it as its own case
        // so a future occurrence self-diagnoses instead of sending someone
        // hunting a DUT bug.
        if (last_ctrl_seq_item.status == svt_sequence_item::ABORTED &&
            last_ctrl_seq_item.results_status == 0) begin
            `uvm_error(MSG_ID,
                $sformatf({"%s: ABORTED with results_status=0x0 - this is the MID-FLIGHT ",
                           "SAMPLE signature (base sequence lines 550-575), not a stall and ",
                           "not a DUT failure. Something broke the interleave rule: check ",
                           "that this leg is not issued back to back with another control ",
                           "transfer. Expected: %s"},
                          label, why_text))
        end
        else if (expect_stalled && !observed_stall) begin
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
    // Log the status word returned by a completing control READ.
    //
    // This is reported, not asserted. The point of these legs is that the
    // request COMPLETES - which check_setup_stalled() already requires - and
    // pinning exact status bits here would duplicate
    // caliptra_ss_usb_get_hub_status and couple this test to bring-up details
    // it does not control. A SHORT payload IS an error, because that would
    // mean the leg completed without actually returning the status.
    //
    // port_num is used only in the message: 0 means the hub itself.
    //
    // expected_bytes MUST be the ROM wLength cap of the row being read, not a
    // shared constant: 4 for GetHubStatus / GetPortStatus, 1 for
    // SetAndTestHubPortFeature (see the L1_STATUS_LEN comment). It is an
    // explicit argument rather than a hardcoded 4 precisely so that the
    // cap-1 row cannot silently be checked against the cap-4 expectation,
    // which is how the first revision of this test failed.
    // -------------------------------------------------------------------------
    function void report_status_word(string       label,
                                     int unsigned port_num,
                                     int unsigned expected_bytes);
        bit [31:0]   status_word;
        int unsigned nbytes;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured, so the status could not be read.",
                          label))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < expected_bytes) begin
            `uvm_error(MSG_ID,
                $sformatf({"%s: returned %0d payload byte(s), expected %0d. The transfer ",
                           "completed but did not deliver the status."},
                          label, nbytes, expected_bytes))
            return;
        end

        // Assemble only as many bytes as the row really returns, little endian.
        status_word = '0;
        for (int unsigned i = 0; i < expected_bytes; i++)
            status_word |= (32'(last_ctrl_seq_item.payload.data[i]) << (8 * i));

        if (expected_bytes >= 4) begin
            `uvm_info(MSG_ID,
                $sformatf({"%s: %s status word 0x%08x (low half 0x%04h, high half 0x%04h)."},
                          label,
                          (port_num == 0) ? "hub" : $sformatf("port %0d", port_num),
                          status_word, status_word[15:0], status_word[31:16]),
                UVM_LOW)
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf({"%s: %s returned %0d status byte(s) = 0x%0h (reported only, ",
                           "see the step-11 comment on why this is not asserted)."},
                          label,
                          (port_num == 0) ? "hub" : $sformatf("port %0d", port_num),
                          expected_bytes, status_word),
                UVM_LOW)
        end
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_SEQUENCE_SV
