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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_HS_HUB_PORT_L1_SEQUENCE_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_HS_HUB_PORT_L1_SEQUENCE_SV

// =============================================================================
// USB HS hub-request L1 sequence: SetAndTestPortFeature(PORT_L1) driven
// independently on downstream port 1 (USBDC0) and port 2 (USBDC1).
//
// THE TWO L1 SCENARIOS THIS IP HAS, AND WHICH TEST OWNS EACH
//
// There are exactly two ways to put a device behind this compound hub into L1,
// and each one targets A DEVICE - never the hub itself:
//
//   1. An EXT + LPM token addressed to the device's own bus address. Decoded by
//      usb_pie.m.vhdl. Covered by caliptra_ss_usb_hs_dev_lpm_l1 (USBDC0 only,
//      since that is the only controller with a software-visible LPM path for
//      the direct token).
//   2. SetAndTestPortFeature(PORT_L1) sent to the HUB but naming a DOWNSTREAM
//      PORT in wIndex[3:0]. Decoded by usb_app_hw_hub.m.vhdl. Covered by THIS
//      test, for both downstream devices.
//
// There is deliberately no third "hub-targeted L1" test, because no such
// request exists. SetAndTestPortFeature(PORT_L1) is only legal against a
// downstream port: usb_app_hw_hub.m.vhdl opens the C_CLASS_REQ_SET_AND_TEST
// case with
//
//   if to_integer(unsigned(ep0_windex(3 downto 0))) = 0 then
//     null; -- A stall will be returned upon this request
//
// i.e. a wIndex port field of 0, which is how a hub-class request addresses the
// hub itself, is rejected. That rejection is asserted below as a negative case
// rather than left as a comment, because it is the fact that makes "per-port"
// the whole of the hub-request story.
//
// WHAT THIS TEST COVERS
//
// (a) The request encoding and its validation (the negative cases below).
// (b) The response ladder - SUCCESS / NYET / STALL-code - selected per build by
//     the firmware's USB_HUB_L1_RESPONSE_MODE and declared to this sequence
//     with +usb_hub_l1_expect.
// (c) PER-PORT isolation, which is the claim the RTL makes most explicitly:
//
//   hub_port_l1_int, hub_port_l1_change   - vectors, one bit per port
//   hub_lpm_sup(0)          <= dev0_lpm_sup
//   hub_lpm_sup(1)          <= dev1_lpm_sup
//   hub_port_lpm_hird_sw(0) <= dev0_lpm_hird_sw
//   hub_port_lpm_hird_sw(1) <= dev1_lpm_hird_sw
//   dev0_lpm_suspend <= ... or hub_port_l1(0)
//   dev1_lpm_suspend <= ... or hub_port_l1(1)
//
// Each port has its own state bit, its own change bit, its own enable inputs,
// and its own device-side destination. The failure mode this catches is the one
// a single-port test cannot see: an RTL bug where the port index is dropped or
// mis-decoded, so putting port 1 into L1 also drops port 2 (or vice versa). On
// an IP whose whole purpose is to present two independent device controllers
// behind one PHY, cross-port leakage would be a serious defect.
//
// THE CHECK THAT ACTUALLY CARRIES THE TEST
//
// Not "both ports can enter L1" - that is just the single-port test run twice.
// The load-bearing checks are the ISOLATION ones:
//
//   after PORT_L1 on port 1:  port 1 L1=1, port 2 L1=0 AND C_PORT_L1=0
//   after clearing port 1:    both ports out of L1
//   after PORT_L1 on port 2:  port 2 L1=1, port 1 L1=0 AND C_PORT_L1=0
//
// Checking the untouched port's CHANGE bit matters as much as its state bit: a
// change bit that got set without the state bit ever moving would mean the
// index decode leaked into the change logic, which an EP1 status-change
// consumer would then misreport to the host.
//
// The second isolation check is also why port 1 is fully cleared (both PORT_L1
// and C_PORT_L1) before port 2 is exercised. Leaving port 1's change bit set
// would make "port 1 C_PORT_L1 is 0 while port 2 is in L1" untestable, and the
// test would silently lose half its value.
//
// WHY A DUAL-DEVICE FIRMWARE IMAGE IS REQUIRED
//
// The hub's per-port LPM enable inputs come from the DEVICE CSRs, so port 2's
// SUCCESS response depends on USBDC1 having been programmed with LPM_SUP set
// and HIRD_SW clear. A single-device image leaves USBDC1 unbooted, its
// dev1_lpm_sup at whatever reset value applies, and - more importantly - with
// no EP0 service, so USBDC1 would never enumerate and port 2 could not be
// brought up at all. The firmware for this test therefore boots BOTH
// controllers via usb_select_device() + boot_usb_core_hub(), the same pattern
// as caliptra_ss_usb_dual_device_hs_bulk_loopback.
//
// ADDRESSES
//   hub    -> 1
//   USBDC0 -> 2   (downstream port 1)
//   USBDC1 -> 3   (downstream port 2)
// Note USBDC1 is at 3, not 2: the two controllers are simultaneously
// enumerated here, so they must not share an address.
//
// NO DUT-SIDE SUSPEND CHECKER
//
// caliptra_ss_usb_suspend_resume_checker watches a single UTMI SuspendM, which
// is shared: there is one PHY for the whole compound. It cannot attribute a
// suspend to port 1 versus port 2, which is exactly the distinction this test
// is about, so arming it here would add no information and would couple this
// test to a checker whose verdict other tests depend on. The device-side
// reality of each port's L1 is instead evidenced by the per-device
// DEVCMDSTAT.LPM_SUS logging in the firmware (which sees the hub's per-port
// level through devN_lpm_suspend), and the hub-side reality by the port status
// words checked below. The "a low-power link state really was entered" claim
// against the shared SuspendM belongs to caliptra_ss_usb_hs_dev_lpm_l1.
//
// FLOW
//   1. Wait HS link ENABLED, start SOF, settle. SOF stays ON throughout.
//   2. Enumerate hub, then port 1 + USBDC0 at addr 2, then port 2 + USBDC1 at
//      addr 3.
//   3. Anchor on the hub. Baseline: both ports out of L1, no change bits.
//   4. Negative cases, all of which must STALL and must leave both ports idle:
//        - wIndex port field 0 (the hub itself - not a legal PORT_L1 target)
//        - wIndex port field 3 (beyond C_HUB_NB_PORTS)
//        - a feature selector that is not PORT_L1
//   5. Port 1 leg: SetAndTestPortFeature(PORT_L1) on port 1, expect the
//      response the build declares, then assert port 1's state and PORT 2
//      UNAFFECTED.
//   6. Clear port 1 fully (PORT_L1 then C_PORT_L1) and confirm both ports are
//      back to the baseline.
//   7. Port 2 leg: same request on port 2, then assert port 2's state and
//      PORT 1 UNAFFECTED.
//   8. Clear port 2 fully.
//   9. Both devices must still answer traffic (GetDescriptor to addr 2 and 3).
//
// In a refusal build (+usb_hub_l1_expect=1 or 2) steps 5-8 assert that NEITHER
// port ever entered L1; the isolation checks still run and are still valid,
// they just have a different expected value on the addressed port.
// =============================================================================

class caliptra_ss_usb_dual_device_hs_hub_port_l1_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_dual_device_hs_hub_port_l1_sequence)

    string MSG_ID = "USB_DUAL_HUB_PORT_L1_SEQ";

    // Hub, and the two downstream device addresses. USBDC0 and USBDC1 are both
    // enumerated at the same time, so their addresses MUST differ.
    localparam int unsigned HUB_ADDR    = 1;
    localparam int unsigned USBDC0_ADDR = 2;
    localparam int unsigned USBDC1_ADDR = 3;

    // Downstream ports. 1-based on the wire; the RTL forms
    // var_port := wIndex(3 downto 0) - 1, so port 1 is hub_port_*(0) = USBDC0.
    localparam int unsigned PORT_DEV0 = 1;
    localparam int unsigned PORT_DEV1 = 2;

    // Hub class request codes.
    localparam bit [7:0]  BREQ_GET_STATUS    = 8'h00;
    localparam bit [7:0]  BREQ_CLEAR_FEATURE = 8'h01;
    localparam bit [7:0]  BREQ_SET_AND_TEST  = 8'h0C;

    // Feature selectors: PORT_L1 = 10, C_PORT_L1 = 23.
    localparam bit [15:0] FEAT_PORT_L1   = 16'd10;
    localparam bit [15:0] FEAT_C_PORT_L1 = 16'd23;

    // Standard GetDescriptor(Device) for the post-L1 traffic checks.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100;
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    localparam bit [15:0] PORT_STATUS_LEN = 16'h0004;
    localparam bit [15:0] L1_STATUS_LEN   = 16'h0001;

    // Port status word bit positions (GEN_HUB_PORT_STATUS).
    localparam int unsigned BIT_PORT_L1   = 5;
    localparam int unsigned BIT_C_PORT_L1 = 21;

    // hub_l1_status response codes. 0x30 is a DATA byte meaning "the port
    // refused because hub_lpm_sup is clear" - it is NOT a protocol STALL, so it
    // arrives as a normal 1-byte data stage and must be decoded, not inferred
    // from the transfer status.
    localparam bit [7:0] L1_RSP_SUCCESS = 8'h00;
    localparam bit [7:0] L1_RSP_NYET    = 8'h10;
    localparam bit [7:0] L1_RSP_STALL   = 8'h30;

    // Negative-case parameters. Port 0 is how a hub-class request addresses the
    // HUB ITSELF; usb_app_hw_hub.m.vhdl rejects it outright for
    // SetAndTestPortFeature, which is the RTL statement that PORT_L1 is a
    // downstream-port-only operation. Port 3 is beyond C_HUB_NB_PORTS = 2.
    localparam int unsigned PORT_HUB_ITSELF = 0;
    localparam int unsigned PORT_OUT_OF_RANGE = 3;

    // Any feature selector other than 10 falls through the RTL's wValue check.
    // 2 is PORT_SUSPEND - a selector that is perfectly valid for
    // SetPortFeature but must not be honoured by SetAndTestPortFeature.
    localparam bit [15:0] FEAT_NOT_PORT_L1 = 16'd2;

    // svt_usb_transfer::results_status bit 4 is the STALL indication.
    // check_xfer_status() treats a STALL as a failure, so the expected-STALL
    // cases below must inspect this bit directly instead.
    localparam int unsigned RESULTS_STATUS_STALL_BIT = 4;

    // HIRD in wIndex[7:4]. Small to keep simulated L1 residency short. It must
    // also satisfy the RTL entry condition wIndex(7:4) >= hird_sw(port); the
    // firmware leaves HIRD_SW at 0 on BOTH devices, so any HIRD qualifies.
    localparam bit [3:0] L1_HIRD = 4'h1;

    // Remote-wake enable, wIndex[15]. Set so the L1 entered matches the other
    // L1 tests; the exits here are host-driven regardless.
    localparam bit L1_RW_ENABLE = 1'b1;

    // Post-reset settle, matching the other dual-device sequences
    // (dual_device_hs_bulk_loopback, dual_device_hs_dev0_hotplug): just long
    // enough for both controllers to re-arm EP0 after the bus reset that
    // brought the link to ENABLED. This used to be a 500 us empirical guard
    // band carried over from the L2 sequences; that approach is not used in
    // the newer tests and was ~34% of this test's runtime on its own.
    localparam realtime POST_RESET_SETTLE = 50us;

    localparam realtime ENUM_SETTLE   = 50us;
    localparam realtime STATUS_SETTLE = 10us;

    // Ceiling for the poll that confirms a port actually reached L1. This is a
    // TIMEOUT, not a dwell: the poll exits as soon as PORT_L1 reads back set.
    // Replaces a flat 100 us wait, which both cost time unconditionally and
    // masked a slow entry by making every observation late.
    localparam int unsigned L1_ENTRY_POLL_MAX = 20;

    localparam realtime POST_EXIT_SETTLE = 20us;

    function new(string name = "caliptra_ss_usb_dual_device_hs_hub_port_l1_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // wIndex packing for SetAndTestPortFeature(PORT_L1). Stated once.
    // Bits 14:8 are unused by the RTL and are driven to zero.
    // -------------------------------------------------------------------------
    function bit [15:0] make_l1_windex(int unsigned port, bit [3:0] hird, bit rw);
        return {rw, 7'b000_0000, hird, port[3:0]};
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        int unsigned          expect_mode;
        bit [7:0]             exp_rsp;
        bit                   expect_entry;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Which response the firmware build has arranged for. This MUST agree
        // with the firmware's USB_HUB_L1_RESPONSE_MODE: the hub resolves its
        // answer from the per-port DEVICE CSRs, so the firmware decides the
        // outcome before the request is ever sent and there is no way for the
        // host to discover it at run time. Default 0 = SUCCESS.
        expect_mode = 0;
        void'($value$plusargs("usb_hub_l1_expect=%d", expect_mode));

        case (expect_mode)
            1: begin exp_rsp = L1_RSP_NYET;    expect_entry = 1'b0; end
            2: begin exp_rsp = L1_RSP_STALL;   expect_entry = 1'b0; end
            default: begin
                if (expect_mode > 2)
                    `uvm_error(MSG_ID,
                        $sformatf("+usb_hub_l1_expect=%0d is not a valid response mode (0=SUCCESS, 1=NYET, 2=STALL-code). Treating as 0, which will misreport if the firmware was built for a refusal mode.",
                                  expect_mode))
                exp_rsp = L1_RSP_SUCCESS; expect_entry = 1'b1;
            end
        endcase

        `uvm_info(MSG_ID,
            $sformatf("Expecting SetAndTestPortFeature(PORT_L1) response 0x%02x and port entry=%0b (from +usb_hub_l1_expect=%0d). This must match the firmware's USB_HUB_L1_RESPONSE_MODE.",
                      exp_rsp, expect_entry, expect_mode), UVM_LOW)

        // Step 1: link first, then SOF. SOF stays on for the whole test: L1 is
        // entered by a request, so stopping SOF would produce an L2 suspend on
        // BOTH devices at once and destroy the per-port distinction entirely.
        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(MSG_ID,
                "Link never reached ENABLED; aborting dual-device hub PORT_L1 sequence.")
            return;
        end
        start_sof_generation();
        #POST_RESET_SETTLE;

        // Step 2: enumerate the hub once, then each port with its own device.
        hub_enum_stepA(host_agent_h, usb_cfg);

        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_DEV0));
        usbdc0_enum_stepC(.host_agent_h  (host_agent_h),
                          .usb_cfg       (usb_cfg),
                          .suffix        ("_dev0"),
                          .device_idx    (0),
                          .assign_address(USBDC0_ADDR[6:0]));

        // usbdc0_enum_stepC() left the anchor at USBDC0. hub_port_bringup_stepB
        // issues hub-class requests at address 1 and requires the anchor to be
        // the hub on entry, so re-anchor first - otherwise its device_address
        // WITH-constraint contradicts the VIP's anchored address and
        // randomize() fails with a constraint conflict rather than a useful
        // message. Same hazard as in the dual-device loopback sequence.
        set_anchor(host_agent_h, usb_cfg, HUB_ADDR);

        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_DEV1));
        usbdc0_enum_stepC(.host_agent_h  (host_agent_h),
                          .usb_cfg       (usb_cfg),
                          .suffix        ("_dev1"),
                          .device_idx    (1),
                          .assign_address(USBDC1_ADDR[6:0]));

        `uvm_info(MSG_ID,
            $sformatf("Dual-device enumeration complete: hub@%0d, USBDC0@%0d (port %0d), USBDC1@%0d (port %0d).",
                      HUB_ADDR, USBDC0_ADDR, PORT_DEV0, USBDC1_ADDR, PORT_DEV1),
            UVM_LOW)
        #ENUM_SETTLE;

        // Step 3: anchor on the hub for all the class requests below, and take
        // a baseline. Both ports must be out of L1 with no change bits, or the
        // isolation checks that follow would be unfalsifiable.
        set_anchor(host_agent_h, usb_cfg, HUB_ADDR);
        check_both_ports_idle(host_agent_h, usb_cfg, "baseline");

        // ------------------------------------------------------------------
        // Step 4: request validation. All three of these must STALL.
        //
        // The port-0 case is the important one: that is how a hub-class request
        // names the hub itself, and the RTL rejects it, so there is no such
        // thing as a hub-targeted L1. Asserting it here is what lets the rest
        // of the suite rely on "PORT_L1 is per-port, always".
        // ------------------------------------------------------------------
        expect_stalled_set_and_test(host_agent_h, usb_cfg, "hubItself",
            .wvalue(FEAT_PORT_L1),
            .windex(make_l1_windex(PORT_HUB_ITSELF, L1_HIRD, L1_RW_ENABLE)),
            .why("wIndex port field 0 addresses the hub itself; SetAndTestPortFeature(PORT_L1) is only legal against a downstream port"));

        expect_stalled_set_and_test(host_agent_h, usb_cfg, "portOutOfRange",
            .wvalue(FEAT_PORT_L1),
            .windex(make_l1_windex(PORT_OUT_OF_RANGE, L1_HIRD, L1_RW_ENABLE)),
            .why("wIndex port field 3 is beyond C_HUB_NB_PORTS = 2"));

        expect_stalled_set_and_test(host_agent_h, usb_cfg, "badFeature",
            .wvalue(FEAT_NOT_PORT_L1),
            .windex(make_l1_windex(PORT_DEV0, L1_HIRD, L1_RW_ENABLE)),
            .why("wValue is PORT_SUSPEND, not PORT_L1; SetAndTestPortFeature must only honour selector 10"));

        // A rejected request must not have disturbed anything. Without this,
        // a hub that STALLed the status stage but still latched hub_port_l1
        // would pass every check above.
        check_both_ports_idle(host_agent_h, usb_cfg, "afterNegativeCases");

        // ------------------------------------------------------------------
        // Step 5: port 1 (USBDC0) is addressed. Port 2 must not notice.
        // ------------------------------------------------------------------
        enter_port_l1(host_agent_h, usb_cfg, PORT_DEV0, "dev0", exp_rsp);

        // In the SUCCESS build, poll until the port reports L1 rather than
        // waiting a flat dwell. hub_port_l1 is a level driven off the control
        // transfer, so this normally returns on the first read; the ceiling
        // only bounds a failure. In a refusal build there is nothing to wait
        // for, so fall straight through to the checks below.
        if (expect_entry)
            wait_port_l1_set(host_agent_h, usb_cfg, PORT_DEV0, "dev0");

        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, "dev0_inL1",
                       BIT_PORT_L1, expect_entry, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, "dev0_inL1",
                       BIT_C_PORT_L1, expect_entry, "C_PORT_L1");

        // The isolation check. A failure here means the hub's port index did
        // not confine the effect to the requested port. This runs in every
        // response mode: in a refusal build the addressed port is expected to
        // be idle too, but "the OTHER port is idle" is still a real check and
        // still catches a cross-coupled index decode.
        `uvm_info(MSG_ID,
            $sformatf("Port %0d handled. Now asserting port %0d was NOT affected - this is the per-port isolation check this test exists for.",
                      PORT_DEV0, PORT_DEV1), UVM_LOW)
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, "dev0_inL1_other",
                       BIT_PORT_L1, 1'b0, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, "dev0_inL1_other",
                       BIT_C_PORT_L1, 1'b0, "C_PORT_L1");

        // Step 6: clear port 1 completely, including its change bit, so the
        // mirrored isolation check in step 7 is meaningful. Harmless in a
        // refusal mode (nothing was set), and still worth issuing so the
        // clear path is exercised identically in every build.
        exit_port_l1(host_agent_h, usb_cfg, PORT_DEV0, "dev0");
        check_both_ports_idle(host_agent_h, usb_cfg, "afterDev0Clear");

        // ------------------------------------------------------------------
        // Step 7: port 2 (USBDC1) is addressed. Port 1 must not notice.
        // ------------------------------------------------------------------
        enter_port_l1(host_agent_h, usb_cfg, PORT_DEV1, "dev1", exp_rsp);

        if (expect_entry)
            wait_port_l1_set(host_agent_h, usb_cfg, PORT_DEV1, "dev1");

        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, "dev1_inL1",
                       BIT_PORT_L1, expect_entry, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, "dev1_inL1",
                       BIT_C_PORT_L1, expect_entry, "C_PORT_L1");

        `uvm_info(MSG_ID,
            $sformatf("Port %0d handled. Now asserting port %0d was NOT affected (mirror of the step 5 check).",
                      PORT_DEV1, PORT_DEV0), UVM_LOW)
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, "dev1_inL1_other",
                       BIT_PORT_L1, 1'b0, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, "dev1_inL1_other",
                       BIT_C_PORT_L1, 1'b0, "C_PORT_L1");

        // Step 8: clear port 2 completely.
        exit_port_l1(host_agent_h, usb_cfg, PORT_DEV1, "dev1");
        check_both_ports_idle(host_agent_h, usb_cfg, "afterDev1Clear");

        // Step 9: both devices must still work. Without this the test would
        // only be reading back bits the hub itself latched.
        #POST_EXIT_SETTLE;
        post_l1_traffic_check(host_agent_h, usb_cfg, USBDC0_ADDR, PORT_DEV0);
        post_l1_traffic_check(host_agent_h, usb_cfg, USBDC1_ADDR, PORT_DEV1);
        set_anchor(host_agent_h, usb_cfg, HUB_ADDR);

        `uvm_info(MSG_ID,
            "caliptra_ss_usb_dual_device_hs_hub_port_l1_sequence complete.", UVM_LOW)

    endtask

    // -------------------------------------------------------------------------
    // Re-anchor the VIP remote-device model. do_control_xfer() constrains
    // device_address and svt_usb_transfer ties that to the anchored remote
    // device's configured address, so the two must move together.
    // -------------------------------------------------------------------------
    task set_anchor(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                    int unsigned addr);
        usb_cfg.remote_device_cfg[0].device_address = addr[6:0];
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID, $sformatf("VIP anchor set to address %0d.", addr), UVM_HIGH)
    endtask

    // -------------------------------------------------------------------------
    // Drive SetAndTestPortFeature(PORT_L1) on one port and require the response
    // the build declared.
    //
    // The expected code is REQUIRED, not merely logged, because every check
    // downstream is derived from it. If a build meant to see SUCCESS silently
    // got a NYET, the port would stay out of L1 and the "other port
    // unaffected" check would pass trivially - the quietest possible way for
    // this test to stop testing anything.
    // -------------------------------------------------------------------------
    task enter_port_l1(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                       int unsigned port, string tag, bit [7:0] exp_rsp);
        string     label = {"SetAndTestPortFeature_PORT_L1_", tag};
        bit [15:0] windex = make_l1_windex(port, L1_HIRD, L1_RW_ENABLE);

        `uvm_info(MSG_ID,
            $sformatf("Driving SetAndTestPortFeature(PORT_L1) on port %0d (wIndex=0x%04x, HIRD=0x%0h, RW=%0b), expecting response 0x%02x.",
                      port, windex, L1_HIRD, L1_RW_ENABLE, exp_rsp), UVM_LOW)

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_SET_AND_TEST, FEAT_PORT_L1,
            windex, L1_STATUS_LEN, HUB_ADDR, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);

        check_l1_response(port, exp_rsp);
        #STATUS_SETTLE;
    endtask

    // -------------------------------------------------------------------------
    // Drive a SetAndTestPortFeature that the hub must reject with a protocol
    // STALL, and require that it did.
    //
    // Note this is a PROTOCOL stall, which is a different thing from the 0x30
    // "STALL-code" data byte that hub_l1_status can return for an enabled but
    // LPM-incapable port. These cases never reach the response logic at all -
    // the RTL discards the request in its wIndex/wValue decode.
    //
    // check_xfer_status() cannot be used here: it treats results_status bit 4
    // as a failure, which is exactly the outcome being required. So the bit is
    // inspected directly, and the ABSENCE of the STALL is the error. Getting
    // that polarity backwards would turn these into checks that can never
    // fail.
    // -------------------------------------------------------------------------
    task expect_stalled_set_and_test(svt_usb_agent host_agent_h,
                                     svt_usb_configuration usb_cfg,
                                     string tag,
                                     bit [15:0] wvalue,
                                     bit [15:0] windex,
                                     string why);
        string label = {"SetAndTestPortFeature_neg_", tag};

        `uvm_info(MSG_ID,
            $sformatf("Negative case '%s': SetAndTestPortFeature wValue=0x%04x wIndex=0x%04x must STALL (%s).",
                      tag, wvalue, windex, why), UVM_LOW)

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_SET_AND_TEST, wvalue, windex,
            L1_STATUS_LEN, HUB_ADDR, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("Negative case '%s': no control transfer item captured, so it could not be confirmed that the hub STALLed the request. This check must not be skipped silently.",
                          tag))
            return;
        end

        if (last_ctrl_seq_item.results_status[RESULTS_STATUS_STALL_BIT] !== 1'b1) begin
            `uvm_error(MSG_ID,
                $sformatf("Negative case '%s': the hub did NOT stall SetAndTestPortFeature wValue=0x%04x wIndex=0x%04x (results_status=0x%0x). It must, because %s. An accepted request here means the hub's request validation in usb_app_hw_hub.m.vhdl is too permissive.",
                          tag, wvalue, windex,
                          last_ctrl_seq_item.results_status, why))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("Negative case '%s': correctly STALLed.", tag), UVM_LOW)
        end

        #STATUS_SETTLE;
    endtask

    // -------------------------------------------------------------------------
    // Take one port out of L1 and acknowledge its change bit.
    //
    // Both steps matter. ClearPortFeature(PORT_L1) drops the state bit;
    // ClearPortFeature(C_PORT_L1) is what a host does next, and clearing it
    // here is what makes the next port's isolation check able to distinguish
    // "untouched" from "left over from the previous leg".
    // -------------------------------------------------------------------------
    task exit_port_l1(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                      int unsigned port, string tag);
        string lbl_l1   = {"ClearPortFeature_PORT_L1_", tag};
        string lbl_cl1  = {"ClearPortFeature_C_PORT_L1_", tag};

        `uvm_info(MSG_ID,
            $sformatf("Driving ClearPortFeature(PORT_L1) then ClearPortFeature(C_PORT_L1) on port %0d.",
                      port), UVM_LOW)

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_CLEAR_FEATURE, FEAT_PORT_L1,
            16'(port), 16'h0000, HUB_ADDR, lbl_l1, usb_cfg);
        wait_xfer_done(host_agent_h, lbl_l1);
        #STATUS_SETTLE;

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_CLEAR_FEATURE, FEAT_C_PORT_L1,
            16'(port), 16'h0000, HUB_ADDR, lbl_cl1, usb_cfg);
        wait_xfer_done(host_agent_h, lbl_cl1);
        #STATUS_SETTLE;
    endtask

    // -------------------------------------------------------------------------
    // Poll GetPortStatus until one port reports PORT_L1 set, bounded by
    // L1_ENTRY_POLL_MAX reads.
    //
    // This replaces a flat dwell. hub_port_l1_int is set in the same clocked
    // branch that handles the SetAndTestPortFeature request, so by the time the
    // control transfer has completed the level is already up and the first read
    // normally succeeds - no wait at all in the passing case.
    //
    // Timing out here is NOT reported as an error: the very next thing the
    // caller does is check_port_bit() on the same bit, which produces the
    // precise, actionable failure. Erroring here as well would double-report a
    // single defect. What this task must never do is return early in a way that
    // makes the caller's check pass - it only ever shortens the wait.
    //
    // The read itself is a real control transfer, so each iteration costs a few
    // microseconds of bus time; no extra delay is needed to pace the loop.
    // -------------------------------------------------------------------------
    task wait_port_l1_set(svt_usb_agent host_agent_h,
                          svt_usb_configuration usb_cfg,
                          int unsigned port, string tag);
        bit          is_set;
        int unsigned attempts;

        for (attempts = 1; attempts <= L1_ENTRY_POLL_MAX; attempts++) begin
            read_port_status_bit(host_agent_h, usb_cfg, port,
                                 {tag, "_l1poll"}, BIT_PORT_L1, is_set);
            if (is_set) begin
                `uvm_info(MSG_ID,
                    $sformatf("Port %0d reported PORT_L1 set after %0d GetPortStatus read(s).",
                              port, attempts), UVM_HIGH)
                return;
            end
        end

        `uvm_info(MSG_ID,
            $sformatf("Port %0d did not report PORT_L1 within %0d GetPortStatus reads; proceeding to the explicit check, which will report the failure.",
                      port, L1_ENTRY_POLL_MAX), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // GetPortStatus on one port and hand back one bit, without judging it.
    //
    // Used by the entry poll above, where a cleared bit is an expected
    // intermediate state rather than a failure. An unusable response yields 0,
    // which keeps the poll going and leaves the verdict to check_port_bit().
    // -------------------------------------------------------------------------
    task read_port_status_bit(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg,
                              int unsigned port, string tag,
                              int unsigned bit_idx, output bit bit_val);
        string     label = $sformatf("GetPortStatus_p%0d_%s", port, tag);
        bit [31:0] status_word;

        bit_val = 1'b0;

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_GET_STATUS, 16'h0000,
            16'(port), PORT_STATUS_LEN, HUB_ADDR, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);

        if (last_ctrl_seq_item == null) return;
        if (last_ctrl_seq_item.payload_byte_count() < 4) return;

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};
        bit_val = status_word[bit_idx];
    endtask

    // -------------------------------------------------------------------------
    // Assert both ports are out of L1 with no pending change bits.
    // -------------------------------------------------------------------------
    task check_both_ports_idle(svt_usb_agent host_agent_h,
                               svt_usb_configuration usb_cfg, string tag);
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, tag,
                       BIT_PORT_L1,   1'b0, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV0, tag,
                       BIT_C_PORT_L1, 1'b0, "C_PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, tag,
                       BIT_PORT_L1,   1'b0, "PORT_L1");
        check_port_bit(host_agent_h, usb_cfg, PORT_DEV1, tag,
                       BIT_C_PORT_L1, 1'b0, "C_PORT_L1");
    endtask

    // -------------------------------------------------------------------------
    // GetPortStatus on one port and compare one bit.
    //
    // Fused into a single task - rather than the get-then-check pair used in
    // the single-port sequences - because this test interleaves reads of two
    // different ports. With a separate checker reading last_ctrl_seq_item, it
    // would be far too easy to check port 2's expected value against a status
    // word that was actually fetched for port 1, and the test would report a
    // pass or a phantom failure with no indication anything was wrong.
    //
    // A short or missing payload is an error, not a silent skip.
    // -------------------------------------------------------------------------
    task check_port_bit(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                        int unsigned port, string tag,
                        int unsigned bit_idx, bit exp_val, string bit_name);
        string       label = $sformatf("GetPortStatus_p%0d_%s", port, tag);
        bit [31:0]   status_word;
        int unsigned nbytes;

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_GET_STATUS, 16'h0000,
            16'(port), PORT_STATUS_LEN, HUB_ADDR, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured for port %0d, so %s could not be checked. This check must not be skipped silently.",
                          tag, port, bit_name))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 4) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: GetPortStatus on port %0d returned %0d payload bytes, expected 4, so %s could not be checked.",
                          tag, port, nbytes, bit_name))
            return;
        end

        // 4 bytes little-endian: wPortStatus in bytes 0-1, wPortChange in 2-3.
        // The concatenation reproduces the RTL hub_status word so bit numbers
        // 0..31 are used directly.
        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};

        if (status_word[bit_idx] !== exp_val) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) is %0b, expected %0b. Full status word 0x%08x. If this is an 'other port' check, the hub applied a PORT_L1 request to a port it was not addressed to - hub_port_l1/hub_port_l1_change are per-port vectors in usb_app_hw_hub.m.vhdl and must not be cross-coupled.",
                          tag, port, bit_idx, bit_name,
                          status_word[bit_idx], exp_val, status_word))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) = %0b as expected. Full status word 0x%08x.",
                          tag, port, bit_idx, bit_name, exp_val, status_word),
                UVM_LOW)
        end
    endtask

    // -------------------------------------------------------------------------
    // Check the one-byte status returned by SetAndTestPortFeature(PORT_L1).
    // -------------------------------------------------------------------------
    function void check_l1_response(int unsigned port, bit [7:0] exp);
        int unsigned nbytes;
        bit [7:0]    got;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("SetAndTestPortFeature(PORT_L1) on port %0d: no control transfer item captured, so the L1 response code could not be checked.",
                          port))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 1) begin
            `uvm_error(MSG_ID,
                $sformatf("SetAndTestPortFeature(PORT_L1) on port %0d returned %0d payload bytes, expected at least 1, so the L1 response code could not be checked.",
                          port, nbytes))
            return;
        end

        got = last_ctrl_seq_item.payload.data[0];
        if (got !== exp) begin
            `uvm_error(MSG_ID,
                $sformatf("SetAndTestPortFeature(PORT_L1) on port %0d returned 0x%02x, expected 0x%02x. Decode against hub_l1_status in usb_app_hw_hub.m.vhdl: 0x00 SUCCESS, 0x10 NYET (hird_sw > hird_hw, or data pending), 0x30 STALL-code (hub_lpm_sup clear). Those inputs come from the per-port DEVICE CSRs (dev%0d), so the two usual causes are (a) the firmware's USB_HUB_L1_RESPONSE_MODE disagreeing with +usb_hub_l1_expect, or (b) that controller not having been programmed with LPM_SUP set and HIRD_SW clear - check the dual-device firmware booted BOTH controllers.",
                          port, got, exp, port - 1))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("SetAndTestPortFeature(PORT_L1) on port %0d returned 0x%02x as expected.",
                          port, got), UVM_LOW)
        end
    endfunction

    // -------------------------------------------------------------------------
    // Post-L1 traffic check on one device.
    //
    // Re-anchors on the device and requires a well-formed 18-byte device
    // descriptor. Both length and bDescriptorType are checked: a transfer that
    // ended but returned nothing, or returned something that is not a device
    // descriptor, must not count as the device still working.
    //
    // A control transfer is used rather than bulk because the firmware for this
    // test services EP0 only and does not arm EP1, so a bulk OUT would be NAKed
    // forever and would fail for a reason unrelated to L1.
    // -------------------------------------------------------------------------
    task post_l1_traffic_check(svt_usb_agent host_agent_h,
                               svt_usb_configuration usb_cfg,
                               int unsigned dev_addr, int unsigned port);
        string       label = $sformatf("PostL1_GetDescriptor_addr%0d", dev_addr);
        int unsigned nbytes;

        set_anchor(host_agent_h, usb_cfg, dev_addr);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, BREQ_GET_DESCRIPTOR, DESC_DEVICE_W_VALUE,
            16'h0000, DEV_DESC_LEN, dev_addr, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("postL1: no control transfer item captured for address %0d, so it could not be confirmed that the device behind port %0d still answers traffic.",
                          dev_addr, port))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < DEV_DESC_LEN) begin
            `uvm_error(MSG_ID,
                $sformatf("postL1: GetDescriptor(Device) to address %0d returned %0d payload bytes, expected %0d. The device behind hub port %0d is not answering correctly after the PORT_L1 entry/exit cycle.",
                          dev_addr, nbytes, DEV_DESC_LEN, port))
        end
        else if (last_ctrl_seq_item.payload.data[1] !== DESC_TYPE_DEVICE) begin
            `uvm_error(MSG_ID,
                $sformatf("postL1: GetDescriptor(Device) to address %0d returned bDescriptorType 0x%02x, expected 0x%02x. The device answered but the descriptor is not a device descriptor.",
                          dev_addr, last_ctrl_seq_item.payload.data[1],
                          DESC_TYPE_DEVICE))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("postL1: device at address %0d (hub port %0d) returned a valid %0d-byte device descriptor, so it is still able to receive and answer traffic.",
                          dev_addr, port, nbytes), UVM_LOW)
        end
    endtask

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_HS_HUB_PORT_L1_SEQUENCE_SV
