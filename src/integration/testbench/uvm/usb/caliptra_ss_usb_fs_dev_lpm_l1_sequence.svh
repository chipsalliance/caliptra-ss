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

`ifndef CALIPTRA_SS_USB_FS_DEV_LPM_L1_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_LPM_L1_SEQUENCE_SV

// =============================================================================
// USB FS device L1 (LPM Sleep) entry / exit sequence (hub-composite IP).
//
// FULL-SPEED BRANCH of caliptra_ss_usb_hs_dev_lpm_l1_sequence. It is a copy
// rather than a reuse, deliberately: the HS sequence is proven in simulation
// and in the waveforms, so FS-specific experiments are kept out of it. Apart
// from ENABLED_POLL_MAX_US and the step-8 verdict split described below, this
// file tracks the HS one. Keep any future LPM fix in step with it.
//
// FS BEHAVIOUR AT STEP 8, AND WHAT THE 51 ms IN THE WAVEFORM ACTUALLY IS.
//
// The device half of this test works at FS: the DUT requests wakeup,
// CHK_DEVICE_WAKEUP_K passes, and USBDC0 answers the post-resume
// GetDescriptor. What used to fail was step 8, with
// "Timeout waiting for ENABLED after L1 exit; link=L1SUSPENDED".
//
// That timeout was the step-8 poll ceiling expiring, nothing more. With the
// old ENABLED_POLL_MAX_US = 50000 the arithmetic is exact:
//
//   step-8 poll starts   1025267.605 ns
//   + 50 ms ceiling    = 51025267.605 ns  <- the reported timeout, to the ps
//
// The link resume visible in the waveform at ~51 ms (PIE leaving
// BUS_EVENT_SW_WAKEUP_3 for FS_IDLE) is therefore NOT a late host resume. It
// happens just AFTER the poll gives up, when this sequence moves on, restarts
// SOF and issues PostL1_GetDescriptor - ordinary bus traffic is what unparks
// the PIE. Since resuming traffic is sufficient, waiting longer buys nothing,
// so the ceiling is now 200 us and the step-8 miss is not an error on the
// device-driven leg (see both comments at step 8).
//
// CORRECTION - A PREVIOUS VERSION OF THIS HEADER WAS WRONG. It claimed the VIP
// refuses the host takeover because of this warning:
//
//   svt_usb_link_20.svp(1335) [handle_link_service_channel_commands]
//   Model can only transition to resuming state from the suspended state when
//   it receives a CleartPortFeature(CLEAR_PORT_SUSPEND) request (11.5.1.10).
//   Current state is L1RESUMING. Ignoring current command.
//
// Check the timestamp: that warning is at 51125267.605 ns, i.e. AFTER step 8
// expired, not at the takeover. The clear_suspend issued by K_RESPONDER at
// ~1015 us was accepted - it returned, host_takeover_done was set by
// 1015267 ns, and a K pulse followed at 1085437 ns. So
// "the VIP ignores clear_suspend from the L1 state group" is NOT supported by
// the log and must not be restated as fact.
//
// STILL OPEN: the host resume K is far shorter than requested. The two
// tdrsmdn_check errors measure 16.7 ns and 23.9 ns of K against the 200 us
// HOST_L1_RESUME_K_PS asks for, despite reconfigure() being called. Note also
// that the check's own threshold is inflated by this suite's config rather
// than by spec - it reports tdrsmdn_min=2000000.000 ns (spec=2000.000 ns),
// which is exactly the cfg.*.tddis = 2_000_000_000 ps that
// caliptra_ss_usb_fs_dev_lpm_l1_test sets and the HS test does not set at all.
// Both of those want investigating together.
//
// RULED OUT by experiment, do not retry without new evidence:
//   - tinactivity. Tightening it to 20 us across the L1 window so the VIP
//     would reach SUSPENDED was tried and had NO effect: the run was
//     bit-identical, same two tdrsmdn errors at the same timestamps. The
//     suspend-timer value is not the gate.
//   - Moving the post-L1 sof_on restart above the step-8 ENABLED poll. Also
//     no effect on this failure.
//   - Treating the post-L1 resume check's 200 us ceiling as "too short". It
//     is not a duration problem. The queued CLEAR_PORT_SUSPEND is consumed
//     when the first post-L1 TRANSFER IS PREPARED, and the resume then
//     completes 85.67 us after that. So any check placed before
//     do_control_xfer() can only ever time out, and raising its ceiling just
//     delays the trigger by the same amount because the poll blocks the very
//     thread that would issue the transfer. The check now sits after
//     wait_xfer_done() - see the long comment there for the timestamps.
//   - Believing reconfigure() is the trigger. Tried, and DISPROVEN: moving
//     the check to just after host_agent_h.reconfigure() left the failure at
//     exactly the same timestamp (1525350.945 ns) even though reconfigure()
//     had moved to 1325350.945 ns. What made this look true was a
//     coincidence - the 200 us poll expired in the same delta the transfer
//     was later queued.
//   - Suppressing tdrsmdn_check in the test. That only hid the symptom; the
//     check is the measurement of whether K was driven. See the note in
//     caliptra_ss_usb_fs_dev_lpm_l1_test.

//
// How this differs from caliptra_ss_usb_hs_dev_global_suspend_L2_sequence.
// L2 entry is the ABSENCE of bus activity: the host stops SOF and the device
// times out into suspend. L1 entry is a PACKET: the host sends an EXT token
// followed by an LPM token carrying bLinkState=1 (L1), a 4-bit HIRD and
// bRemoteWake. Therefore this sequence must NOT use sof_off - SOF generation
// stays on for the whole test, and the L1 transition is caused by
// svt_usb_protocol_service_usb_20_lpm_sequence on prot_service_sequencer.
//
// WHAT THIS SEQUENCE COVERS, AND WHAT THE HUB-LEVEL L1 TEST COVERS INSTEAD
//
// This is the device-controller / PIE-level LPM path: the LPM token is
// addressed to USBDC0 and decoded by the device controller behind the hub.
//
// Since release_2.6 the hub front-end ALSO advertises and implements LPM, so
// the old rationale for this sequence ("a real host would never try LPM here")
// no longer holds and must not be re-asserted:
//   - the hub DEVICE descriptor reports bcdUSB=0x0210 and the hub returns a
//     12-byte BOS with a USB 2.0 Extension capability whose bmAttributes bit 1
//     (LPM) is set (usb_ep0_hub_descr.m.vhdl), so a host IS permitted to use
//     LPM on this device. That advertisement is checked separately by
//     caliptra_ss_usb_{hs,fs}_dev_get_bos_descriptor.
//   - usb_app_hw_hub.m.vhdl implements SetAndTestPortFeature(PORT_L1), so the
//     host can also drive L1 through the hub.
//
// Sending the token directly is still the right stimulus for THIS sequence,
// because it is the only way to exercise the device controller's own LPM
// decode: a hub-class PORT_L1 request is handled by usb_app_hw_hub and reaches
// the device as a level on hub_port_l1(N), never as an LPM token. The two are
// different mechanisms and are kept as different tests. There are exactly TWO
// ways into L1 in this IP, and both of them name a DEVICE:
//   caliptra_ss_usb_hs_dev_lpm_l1 (this one)    - EXT + LPM token addressed to
//                                                 USBDC0's bus address, decoded
//                                                 by the PIE
//   caliptra_ss_usb_dual_device_hs_hub_port_l1  - SetAndTestPortFeature(PORT_L1)
//                                                 to the hub naming downstream
//                                                 port 1 (DEV0) then port 2
//                                                 (DEV1), plus the
//                                                 SUCCESS/NYET/STALL-code
//                                                 response ladder
//
// There is deliberately NO third "hub-targeted L1" test, because no such
// request exists. SetAndTestPortFeature(PORT_L1) is legal only against a
// downstream port: usb_app_hw_hub.m.vhdl answers a wIndex[3:0] port field of 0
// - i.e. the hub itself - with a protocol STALL
// ("null; -- A stall will be returned upon this request"), and hub_port_l1 is a
// per-port vector (C_HUB_NB_PORTS-1 downto 0) with no broadcast encoding.
// Do not re-add a "global L1" test on the strength of the word "global".
// See docs/usb_l1_lpm_test_feasibility_report.md for the original RTL audit.
//
// DIRECT-TOKEN PATH IS DEV0 ONLY. DEV1 has no software-visible LPM control of
// its own, so there is no DEV1 variant of THIS sequence. That is not a gap in
// L1 coverage any more: hub_port_lpm_sup(1) <= dev1_lpm_sup and hub_port_l1(1)
// feeds dev1_lpm_suspend, so DEV1's L1 behaviour is reachable through the hub
// and is covered by caliptra_ss_usb_dual_device_hs_hub_port_l1.

//
// Sequence flow:
//   1. Wait for the HS host link to reach ENABLED, then start SOF.
//   2. Settling delay (same failure mode as the L2 test: acting on the link
//      while the VIP SM is still walking TRANSMIT -> ENABLED can knock it to
//      DISCONNECTED).
//   3. Enumerate hub + USBDC0 so the device answers at LPM_DEV_ADDRESS. The
//      LPM token is addressed, so this is a prerequisite, not decoration.
//   4. Arm the DUT-side suspend/resume checker.
//   5. Send the LPM token (bLinkState=L1, HIRD=LPM_HIRD, bRemoteWake=1).
//   6. Wait for the DUT to enter the low-power state (usb_dut_suspend_seen,
//      bounded by L1_DWELL_MAX).
//   7. Exit L1. Host-driven by default via
//      svt_usb_link_service_clear_l1suspend_sequence on
//      link_service_sequencer; skipped when +usb_lpm_dev_wakeup=1, in which
//      case the firmware build with USB_LPM_DEVICE_INITIATED_EXIT=1 drives
//      the exit from the device side instead.
//   8. Wait for the DUT to leave the low-power state, short observation
//      window, then close the checker window.
//
// The DUT-side verdict lives in caliptra_ss_usb_suspend_resume_checker
// (+usb_suspend_resume_check) plus the firmware's own DEVCMDSTAT.LPM_SUS /
// LPM_REWP / LPM.HIRD_HW logging. This sequence drives the host side and
// bounds the waits; its own uvm_errors are not the whole check.
// =============================================================================

class caliptra_ss_usb_fs_dev_lpm_l1_sequence extends caliptra_ss_usb_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_fs_dev_lpm_l1_sequence)

    // -------------------------------------------------------------------------
    // Timing and stimulus knobs. Tagged the same way as the L2 sequence:
    // "physics/VIP bound" values must not be reduced below their protocol
    // bound; "empirical margin" values are headroom and are the first place to
    // look for runtime reduction once a baseline log exists.
    // -------------------------------------------------------------------------

    // Post-reset settle: long enough for the controller to re-arm EP0 after
    // the bus reset that brought the link to ENABLED. 50 us, matching the
    // newer sequences (dual_device_hs_bulk_loopback,
    // dual_device_hs_dev0_hotplug). This was a 500 us empirical guard band
    // carried over from the L2 sequences; that approach is no longer used, and
    // here it was the entire gap between "SOF generation started" and
    // "Enumerating hub and USBDC0" in the log.
    localparam realtime POST_RESET_SETTLE = 50us;

    // Lets enumeration traffic drain and the firmware finish its
    // post-enumeration register writes (usb_allow_clock_stop, LPM_SUP check)
    // before the LPM token arrives. Unlike the settle above this one is
    // waiting on the MCU polling loop, which the host cannot observe, so it
    // stays a fixed delay - but 50 us is the same order as the enumeration
    // settle used elsewhere and is ample for the handful of register writes
    // involved.
    localparam realtime PRE_LPM_SETTLE = 50us;

    // Timeout ceiling, not a dwell: the wait ends on usb_dut_suspend_seen. L1
    // entry latency is microseconds, not milliseconds, because it is driven by
    // a packet rather than by a 3 ms idle timer - so this ceiling is far larger
    // than the expected value and only bounds the failing case.
    localparam realtime L1_DWELL_MAX = 500us;

    // Timeout ceiling for the DUT leaving L1 after the exit is driven.
    //
    // 100 us, NOT 500 us. This arm waits on usb_dut_resume_seen, which is
    // UNFIREABLE on the L1 path (see the long comment at the post-exit verdict
    // below: it is gated on a falling SuspendM edge that L1 never produces).
    // So this ceiling is always taken in full, and it sits BEFORE the
    // post-resume traffic check that actually decides the test.
    //
    // At 500 us that pushed the verdict past the end of the simulation. The
    // MCU halted at 515105 ns and the base test releases its objection on
    // halt; step 8 completed at 534379 ns, so the verdict would not have run
    // until 1034379 ns, but the run ended at 990671 ns. The result was no
    // PASS and no FAIL message at all - the log simply stopped, which reads
    // like a hang but is a truncation.
    //
    // 100 us keeps the verdict inside the MCU's lifetime while still leaving
    // room for the ~90 us L1 wakeup budget (T_60us K + T_TxENDDELAY). Do not
    // raise this without also extending the MCU's post-test dwell, or the
    // verdict disappears again.
    localparam realtime L1_EXIT_WAIT_MAX = 100us;


    // -------------------------------------------------------------------------
    // Device-initiated L1 exit (+usb_lpm_dev_wakeup=1) only. Unused by the
    // host-driven default path.
    // -------------------------------------------------------------------------

    // Ceiling for the DEVICE to START driving resume K upstream after the
    // firmware rings the usbreg_lpmremotewakeup doorbell.
    //
    // This is a ceiling, not a dwell: the wait ends on usb_dut_wakeup_k_seen,
    // published by caliptra_ss_usb_device_wakeup_checker once the DUT has held
    // UTMI TXValid with linestate=K for its K_MIN_HOLD (20 us). Exceeding this
    // ceiling means the DUT never requested wakeup at all, which is reported
    // here and owned as a verdict by CHK_DEVICE_WAKEUP_K.
    //
    // Dominated by the MCU polling loop that notices LPM_SUS and issues the
    // doorbell write, not by any bus timer, so it is deliberately generous.
    //
    // Expressed in whole microseconds because step 7 polls the responder's
    // done-flag rather than re-waiting on the one-shot event (a second
    // wait_trigger() on an event that has already fired would block forever).
    localparam int unsigned DEV_K_WAIT_MAX_US = 500;

    // Grace window for the forked responder to finish driving the terminating
    // SE0 once it has seen the K. Only bounds the failing case.
    localparam int unsigned TAKEOVER_DONE_MAX_US = 200;

    // Host resume-K duration for the L1 takeover, in ps, written to
    // svt_usb_configuration::tdrsmdn (the VIP RESUMING -> SEND_EOR dwell).
    //
    // Same mechanism as HOST_RESUME_K_PS in
    // caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence, but sized for
    // the L1 timers instead of the L2 ones. The host K must be CONTINUOUS with
    // the device K and only the terminating SE0/EOP may be late, so the K is
    // stretched until it lands inside BUS_EVENT_SW_WAKEUP_3 - the state that
    // waits on ls_filt = LINESTATE_SE0 and has NO timeout arm.
    //
    // L1 budget from usb_pie.m.vhdl, 60 MHz pie_clk:
    //   BUS_EVENT_LPM_SW_WAKEUP_1 : T_60us       = 3600 cycles  =  60 us
    //   BUS_EVENT_SW_WAKEUP_2     : T_TxENDDELAY = 1800 cycles  =  30 us
    // so the DUT is out of WAKEUP_2 and parked in WAKEUP_3 about 90 us after
    // its first K bit. 200 us leaves ~110 us of margin. Longer is safe here,
    // shorter is not.
    //
    // NOTE this is far shorter than the L2 value (3.2 ms) because the L1 device
    // K is T_60us rather than T_3ms.
    localparam real HOST_L1_RESUME_K_PS = 200_000_000.0; // 200 us in ps

    // Empirical margin. Gives the MCU polling loop room to sample DEVCMDSTAT
    // once more and log the exit-side event before the checker window closes.
    localparam realtime POST_EXIT_OBS = 200us;

    // Poll ceiling in 1 us steps. Timeout only.
    //
    // WHY THIS IS 200 AND NOT 50000 ON THE FS BRANCH.
    //
    // At FS the host VIP does not return to ENABLED on its own after a
    // device-initiated L1 exit, so this poll always ran to its ceiling. With
    // the old 50000 that burned a full 50 ms of simulated time for nothing:
    // the poll started at 1025267 ns and timed out at exactly 51025267 ns.
    //
    // What the waveform shows at ~51 ms is NOT a late host resume. It is this
    // poll giving up: the sequence then moves on, restarts SOF and issues
    // PostL1_GetDescriptor, and it is that ordinary bus traffic which unparks
    // the PIE from BUS_EVENT_SW_WAKEUP_3 into FS_IDLE. Resuming traffic is
    // sufficient to bring the link back, so there is no value in waiting
    // longer - 200 us is comfortably past the ~90 us L1 wakeup budget
    // documented at HOST_L1_RESUME_K_PS and keeps the runtime sane.
    localparam int unsigned ENABLED_POLL_MAX_US = 200;



    // -------------------------------------------------------------------------
    // LPM token payload.
    //
    // LPM_DEV_ADDRESS must match the address the base-sequence enumeration
    // assigns to USBDC0 (step C leaves it at 2). An LPM token to the wrong
    // address is simply ignored by the device, which would show up as "no L1
    // entry" and look like a DUT bug.
    //
    // LPM_HIRD is the host-initiated resume duration. usb_host_pie.m.vhdl
    // decodes it as 50 us + 75 us per step (0 -> 50 us ... 15 -> 1175 us), so a
    // small value is chosen deliberately to keep simulated time down per
    // docs/SIM_RUNTIME_OPTIMIZATION.md.
    //
    // The firmware LOGS the device's read-only LPM[3:0] HIRD_HW field but does
    // NOT compare it against this value, and must not be changed to do so on
    // this path. HIRD_HW always reads 0 at the device here, whatever is sent:
    // in ip_xxx_3511_hs_mem_compound_structure.a.vhdl
    //
    //   dev0_lpm_hird_hw <= hub_port_lpm_hird_hw(3 downto 0)
    //                       when hub_enable_q = '1'
    //                       else sync_sieint_lpm_hird_hw;
    //
    // and boot_usb_core_hub() always sets HUB_EN, so the mux selects
    // hub_port_lpm_hird_hw - whose only writer (usb_app_hw_hub.m.vhdl) runs
    // exclusively under SetAndTestPortFeature(PORT_L1). The direct LPM token
    // never writes it. The HIRD the token carried IS captured by the PIE
    // (lpm_hird_hw_r <= rxdata(7 downto 4)) and is visible at the hub's own
    // ep0_mem(C_HUB_LPM)(3 downto 0), just not at the device.
    //
    // So HIRD_HW = 0 in this suite's log is correct and expected, not a DUT
    // bug and not a reason to retune this constant. Checking a non-zero
    // HIRD_HW belongs to caliptra_ss_usb_dual_device_hs_hub_port_l1, which
    // reaches the field through the hub request that actually writes it.
    //
    // LPM_BREMOTEWAKE must be 1 for the device-initiated exit variant to be
    // legal at all: the RTL gates usbreg_lpmremotewakeup on
    // reg_dev_lpm_remote_wake, which is this bit as received. It is left at 1
    // in both variants so the two runs differ only in who drives the exit.
    // -------------------------------------------------------------------------
    localparam bit [6:0] LPM_DEV_ADDRESS  = 7'd2;
    localparam bit [3:0] LPM_BLINKSTATE   = 4'h1;   // 1 = L1
    localparam bit [3:0] LPM_HIRD         = 4'h1;   // -> 125 us resume
    localparam bit       LPM_BREMOTEWAKE  = 1'b1;

    // -------------------------------------------------------------------------
    // Global uvm_event names shared with caliptra_ss_usb_suspend_resume_checker.
    // Duplicated verbatim there on purpose: a uvm_sequence cannot reach into
    // testbench scope and the checker must not depend on the UVM package. Keep
    // both copies in sync.
    //
    // Note the checker watches UTMI SuspendM, which this IP asserts for any
    // low-power link state, so the same suspend/resume events serve L1 here.
    // The L1-vs-L2 distinction is made on the firmware side from
    // DEVCMDSTAT.LPM_SUS.
    // -------------------------------------------------------------------------
    localparam string OBS_WINDOW_EVENT  = "usb_suspend_resume_obs_window_done";
    localparam string DUT_SUSPEND_EVENT = "usb_dut_suspend_seen";
    localparam string DUT_RESUME_EVENT  = "usb_dut_resume_seen";
    localparam string ARM_EVENT         = "usb_suspend_stimulus_armed";

    // Published by caliptra_ss_usb_device_wakeup_checker (+usb_device_wakeup_check)
    // when the DUT has driven UTMI TXValid with linestate=K for K_MIN_HOLD.
    //
    // This is the self-detection hook for the device-initiated variant: the
    // host half is triggered BY this event rather than by a scheduled delay, so
    // a DUT that never requests wakeup cannot be masked by a well-timed host
    // resume. The checker keys on a DUT OUTPUT (txvalid), so nothing the host
    // or the VIP does can forge it.
    localparam string DUT_WAKEUP_K_EVENT = "usb_dut_wakeup_k_seen";

    // Opcode and ack timeout for the MCU STOP handshake below. The opcode must
    // match MCU_COMMAND_STOP in caliptra_ss_usb_legacy_ep0_observer_if and
    // USB_LEGACY_EP0_COMMAND_STOP in libs/usb/usb.h - all three are the same
    // number and must be changed together.
    localparam bit [3:0] MCU_STOP_OPCODE     = 4'h7;
    localparam realtime  MCU_STOP_ACK_MAX    = 200us;

    function new(string name = "caliptra_ss_usb_fs_dev_lpm_l1_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Tell the MCU it may halt now.
    //
    // WHY THIS EXISTS. The firmware used to call csr_write_mpmc_halt() as soon
    // as it had seen its own L1 entry and exit, which on the FS run was
    // 1006380 ns - about 319 us BEFORE this sequence issued
    // PostL1_GetDescriptor at 1325334 ns. EP0 on this device is serviced by
    // the firmware ISR, so once main() returns nothing re-arms EP0 and the
    // controller NAKs every IN token for ever. Measured on that run: 188 IN
    // tokens and 306 NAKs for a single SETUP, and the transfer only "ended"
    // when the VIP's retry budget expired, 2.4 ms later. Every other FS
    // control transfer in the same run cost 20-50 us.
    //
    // That was bad twice over. It dominated the runtime, and it made the
    // post-L1 traffic check a FALSE PASS: the check reads
    // xfer_wait_timed_out, which was false because the VIP gave up rather
    // than timing out, so a halted device looked the same as a healthy one.
    //
    // So the MCU is now held alive until the host side is finished with it and
    // released explicitly here. The transport is the existing MCI generic-wire
    // command channel from the OCP-recovery work - this adds no new mechanism:
    //   host_mcu_command -> MCI GENERIC_INPUT_WIRES_1 -> firmware polls it
    //   firmware acks via GENERIC_OUTPUT_WIRES_1 -> fw_snapshot_header
    // issue_mcu_command_bounded() holds the command asserted until that ack
    // arrives, so polling firmware cannot miss a pulse.
    //
    // FAILURE HANDLING IS DELIBERATELY SOFT. A missing ack is reported as a
    // uvm_info, not an error: the firmware still has its own bounded wait and
    // halts on its own when that expires, and the base test's MCU-halt monitor
    // has its own timeout on top. Erroring here would turn a slow MCU into a
    // test failure for something that is not the DUT's behaviour. The real
    // verdicts are CHK_DEVICE_WAKEUP_K, CHK_POST_L1_LINK_RESUMED and the
    // post-L1 transfer.
    //
    // The observer interface is fetched optionally, matching
    // caliptra_ss_usb_init_sequence: if a testbench configuration does not
    // wire it, the handshake is skipped and the firmware falls back to its own
    // bounded wait.
    // -------------------------------------------------------------------------
    virtual task request_mcu_stop();
        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        bit acknowledged;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_info("USB_LPM_L1_SEQ",
                "No legacy EP0 observer interface in this testbench configuration, so the MCU STOP handshake is skipped. The firmware falls back to its own bounded post-test wait before halting.",
                UVM_LOW)
            return;
        end

        observer_vif.issue_mcu_command_bounded(
            .opcode(MCU_STOP_OPCODE),
            .generation(16'h0001),
            .expected_legacy_dispatch_delta(4'h0),
            .timeout(MCU_STOP_ACK_MAX),
            .acknowledged(acknowledged));

        if (acknowledged)
            `uvm_info("USB_LPM_L1_SEQ",
                "MCU STOP acknowledged: the firmware kept EP0 serviced across the post-L1 window and is now free to halt.",
                UVM_LOW)
        else
            `uvm_info("USB_LPM_L1_SEQ",
                $sformatf("MCU STOP was not acknowledged within %0t. Not failed here: the firmware has its own bounded wait and halts without the command, and the base test's MCU-halt monitor still applies. If the post-L1 transfer above was also slow, suspect the firmware was not built with the STOP wait.",
                    MCU_STOP_ACK_MAX),
                UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        uvm_event dut_suspend_ev;
        uvm_event dut_resume_ev;
        uvm_event obs_window_ev;
        uvm_event arm_ev;
        uvm_event dut_wakeup_k_ev;

        bit dev_driven_exit = 0;

        // Device-initiated path bookkeeping. device_k_seen marks that the DUT
        // really did request wakeup on the wire; device_k_seen_time is used to
        // report the host takeover latency, which is the number that tells a
        // late takeover apart from a missing one.
        bit      device_k_seen      = 1'b0;
        realtime device_k_seen_time = 0;

        // Set by the forked K-responder once it has driven the terminating
        // SE0. Lets step 7 tell "the device never asked" from "the device
        // asked and the host answered".
        bit      host_takeover_done = 1'b0;

        // Resolve the shared events up front: get_global() creates on first
        // use, so resolving before the stimulus removes any race with the
        // checker triggering them.
        dut_suspend_ev = uvm_event_pool::get_global(DUT_SUSPEND_EVENT);
        dut_resume_ev  = uvm_event_pool::get_global(DUT_RESUME_EVENT);
        obs_window_ev  = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
        arm_ev         = uvm_event_pool::get_global(ARM_EVENT);

        // Resolved unconditionally even on the host-driven path: get_global()
        // creates on first use, and resolving it here (before ARM_EVENT is
        // triggered at step 4) means the device-wakeup checker and this
        // sequence are looking at the same object no matter which side wins
        // the race to create it.
        dut_wakeup_k_ev = uvm_event_pool::get_global(DUT_WAKEUP_K_EVENT);

        host_agent_h  = resolve_host_agent();
        usb_cfg       = resolve_usb_cfg();
        shared_status = resolve_shared_status();

        // Selects who drives the L1 exit. Must agree with how the firmware was
        // built: +usb_lpm_dev_wakeup=1 requires a firmware image compiled with
        // USB_LPM_DEVICE_INITIATED_EXIT=1, otherwise nobody drives the exit
        // and the DUT sits in L1 until the dwell ceiling.
        void'($value$plusargs("usb_lpm_dev_wakeup=%d", dev_driven_exit));

        // Step 1: link up first, SOF second. The suspend/resume checker arms on
        // the first SOF, so SOF must not start before the link is up.
        wait_for_link_enabled(shared_status, "HS host link");
        start_sof_generation();

        // Step 2: settling delay. See POST_RESET_SETTLE.
        #POST_RESET_SETTLE;

        // Step 3: enumerate hub + USBDC0. The LPM token is addressed to
        // LPM_DEV_ADDRESS, which is the address step C assigns here.
        `uvm_info("USB_LPM_L1_SEQ", "Enumerating hub and USBDC0 before LPM...", UVM_LOW)
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg, "_lpm_l1");
        `uvm_info("USB_LPM_L1_SEQ", "Enumeration complete.", UVM_LOW)

        #PRE_LPM_SETTLE;

        // Step 4: arm the DUT-side checker. Earliest point at which a SuspendM
        // change is attributable to this stimulus - before this, SuspendM
        // activity belongs to boot (it is held low out of reset while the PHY
        // clocks are gated and rises inside boot_usb_core).
        arm_ev.trigger();
        `uvm_info("USB_LPM_L1_SEQ",
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to the LPM stimulus.",
            UVM_LOW)

        // Stop periodic SOF generation before requesting L1.
        // The LPM transaction below remains the intended L1-entry stimulus.
        begin
            svt_usb_protocol_service_20_sof_off_sequence sof_off;
            sof_off =
                svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
                    "sof_off_before_lpm"
                );
            sof_off.start(p_sequencer.prot_service_sequencer);
        end

        // ---------------------------------------------------------------------
        // Step 4a (device-initiated leg only): start the K-responder BEFORE the
        // LPM token, as a detached thread.
        //
        // WHY THIS MUST BE FORKED HERE AND NOT INLINE AT STEP 7.
        // The device K is a short pulse on the DUT's own schedule: 60 us
        // (T_60us), after which SW_WAKEUP_2 releases it in a further 30 us
        // (T_TxENDDELAY). The host has to answer inside that window.
        //
        // The first version of this code did the wait inline at step 7, which
        // put it BEHIND step 6's wait on usb_dut_suspend_seen. That event is a
        // falling edge of UTMI SuspendM and is NOT generated on this L1 path -
        // the suspend checker arms at SuspendM level 1 and never sees an edge -
        // so step 6 always burned its full L1_DWELL_MAX ceiling first. Measured
        // result: the DUT drove K at 504 us, the checker published the event at
        // 524 us, and the takeover did not run until 1001 us - 477 us late, by
        // which time the K had ended and the MCU had already halted.
        //
        // Forking here decouples the response from step 6 entirely: the
        // responder is blocked only on the K event, so it reacts within one
        // delta of the event being published, about 20 us after the DUT's first
        // K bit (the checker's K_MIN_HOLD) and about 40 us before the K ends.
        //
        // This is still REACTIVE, not scheduled. The thread does nothing at all
        // until usb_dut_wakeup_k_seen fires, so a DUT that never requests
        // wakeup gets no host resume and case (i) is reported. Forking early
        // only removes latency; it does not weaken the check. It also matches
        // the L2 precedent, which forks sample_device_remote_wakeup() at its
        // step 4a for exactly this reason.
        // ---------------------------------------------------------------------
        if (dev_driven_exit) begin
            fork
                begin: K_RESPONDER
                    dut_wakeup_k_ev.wait_trigger();
                    device_k_seen      = 1'b1;
                    device_k_seen_time = $realtime;
                    `uvm_info("USB_LPM_L1_SEQ",
                        "Device half done: the DUT drove resume K upstream on its own UTMI TXValid (see CHK_DEVICE_WAKEUP_K). Answering immediately - this thread was armed before the LPM token so it is not queued behind any other wait.",
                        UVM_LOW)

                    // Stretch the host K so the terminating SE0 lands inside
                    // BUS_EVENT_SW_WAKEUP_3. Configured before the link
                    // service sequence starts.
                    usb_cfg.tdrsmdn = HOST_L1_RESUME_K_PS;
                    host_agent_h.reconfigure(usb_cfg);

                    // Host half of the handshake, issued in RESPONSE to the
                    // device and with tdrsmdn stretched.
                    //
                    // WHY clear_suspend (the NON-L1 sequence) AND NOT
                    // clear_l1suspend HERE.
                    //
                    // This mirrors the L2 device-initiated test
                    // caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence,
                    // which answers a device-driven resume with
                    // svt_usb_link_service_clear_suspend_sequence. The reason
                    // that is the right choice here too is about WHO is
                    // resuming, not about which low-power state was entered:
                    //
                    //   - clear_l1suspend originates a HOST-initiated L1 exit.
                    //     It is correct on the host-driven branch below, where
                    //     the host is the party that decides to leave L1.
                    //   - on THIS leg the DEVICE has already started the
                    //     resume; the host only has to join the K already on
                    //     the bus and terminate it with SE0. That is the same
                    //     job clear_suspend does in the L2 test, and the L2
                    //     test is the only device-initiated resume in this
                    //     environment with a known-good shape.
                    //
                    // Two earlier attempts here are recorded so they are not
                    // repeated:
                    //   - clear_l1suspend: returned in 0 ns and left
                    //     link_svc_trace with a single row (START_LPM only).
                    //   - remote_wakeup_after_l1suspend: identical result,
                    //     also a single row.
                    // Both completed without driving anything, so neither was
                    // ever answering the device. Note the comparison against
                    // the host-driven twin that originally motivated the
                    // second attempt was invalid (that run used a modified
                    // yml), so "clear_l1suspend behaves differently on the two
                    // legs" is NOT an established fact - it was withdrawn.
                    //
                    // HOW TO TELL IF THIS ONE WORKS: look for a SECOND row in
                    // env.host_agent.link_mon.link_svc_trace after the
                    // USB_20_PORT_START_LPM row, and for host drive activity
                    // in the physical service trace AFTER the device-K
                    // timestamp. Do not trust the log text - all three of
                    // these sequences report success whether or not they
                    // touched the bus.
                    begin
                        svt_usb_link_service_clear_suspend_sequence clr_susp_dev;
                        clr_susp_dev =
                            svt_usb_link_service_clear_suspend_sequence::type_id::create(
                                "clr_susp_dev_takeover"
                            );
                        clr_susp_dev.start(p_sequencer.link_service_sequencer);
                    end



                    host_takeover_done = 1'b1;
                    `uvm_info("USB_LPM_L1_SEQ",
                        $sformatf("Host resume takeover complete; terminating SE0 driven %0t after the device-wakeup-K event (the DUT's first K bit is about K_MIN_HOLD = 20 us earlier still). For reference the device holds K for T_60us = 60 us and reaches SW_WAKEUP_3 about 90 us after that first bit, so this latency must stay well inside 90 us.",
                                  $realtime - device_k_seen_time),
                        UVM_LOW)
                end
            join_none
        end

        // Step 5: send the LPM token. This, not the absence of SOF, is what
        // puts the link into L1. SOF generation is deliberately left running.
        `uvm_info("USB_LPM_L1_SEQ",
            $sformatf("Sending LPM token: addr=%0d bLinkState=%0h HIRD=%0h bRemoteWake=%0b",
                      LPM_DEV_ADDRESS, LPM_BLINKSTATE, LPM_HIRD, LPM_BREMOTEWAKE),
            UVM_LOW)
        begin
            svt_usb_protocol_service_usb_20_lpm_sequence lpm_seq;
            lpm_seq = svt_usb_protocol_service_usb_20_lpm_sequence::type_id::create("lpm_seq");
            lpm_seq.blinkstate      = LPM_BLINKSTATE;
            lpm_seq.dev_address     = LPM_DEV_ADDRESS;
            lpm_seq.lpm_hird        = LPM_HIRD;
            lpm_seq.lpm_bremotewake = LPM_BREMOTEWAKE;
            lpm_seq.start(p_sequencer.prot_service_sequencer);
        end
        `uvm_info("USB_LPM_L1_SEQ", "LPM token sent.", UVM_LOW)

        // Step 6: wait for the DUT to enter the low-power state. Ends early on
        // usb_dut_suspend_seen. The timeout arm is not an error here: whether
        // the DUT entered L1 is the checker's CHK_SUSPEND_SEEN plus the
        // firmware's LPM_SUS log, and reporting it once keeps one failure from
        // producing three messages.
        //
        // THIRD ARM, AND WHY IT IS NEEDED. On this L1 path usb_dut_suspend_seen
        // is frequently never triggered at all: the suspend checker fires on a
        // FALLING edge of UTMI SuspendM, and in L1 the controller may hold
        // SuspendM high throughout (the checker's own arming line reports the
        // current level, and it has been observed as 1). Without a third arm
        // this fork then always ran to the full L1_DWELL_MAX ceiling, which is
        // harmless for the host-driven leg but used to delay the device-driven
        // takeover past the end of the device K.
        //
        // The responder is now forked at step 4a so it is no longer affected,
        // but the K event is still a positive indication that the DUT was in
        // L1 and has already started its exit - there is nothing left to wait
        // for - so it releases this fork too. That keeps the two legs' logs
        // comparable and removes a dead 500 us from the device-driven run.
        fork
            begin: WAIT_DUT_L1
                dut_suspend_ev.wait_trigger();
                `uvm_info("USB_LPM_L1_SEQ",
                    "DUT entered low-power state after LPM token (UTMI SuspendM low).", UVM_LOW)
                disable L1_DWELL_TIMEOUT;
                disable WAIT_DEV_K_EXIT;
            end
            begin: WAIT_DEV_K_EXIT
                // Only meaningful on the device-driven leg. On the host-driven
                // leg device_k_seen is never set, so this arm simply never
                // completes and the other two decide the outcome.
                //
                // This POLLS the flag the step-4a responder sets, rather than
                // calling dut_wakeup_k_ev.wait_trigger() a second time. Two
                // waiters on one uvm_event are only both released if both were
                // already blocked when trigger() ran; if the doorbell is fast
                // enough that the K event fires before this fork is scheduled,
                // a wait here would never return and would silently fall back
                // to the 500 us dwell ceiling - exactly the latency this change
                // exists to remove. Polling a flag has no such ordering
                // dependency.
                while (!device_k_seen) #1us;
                `uvm_info("USB_LPM_L1_SEQ",
                    "Device-driven leg: the DUT has already begun its own L1 exit (resume K seen), so there is nothing further to wait for here. Releasing the L1-entry wait without burning the dwell ceiling; the forked step-4a responder is driving the host half.",
                    UVM_LOW)
                disable L1_DWELL_TIMEOUT;
                disable WAIT_DUT_L1;
            end
            begin: L1_DWELL_TIMEOUT
                #L1_DWELL_MAX;
                `uvm_info("USB_LPM_L1_SEQ",
                    "L1 dwell ceiling reached without the DUT entering a low-power state; continuing. Checked as CHK_SUSPEND_SEEN and by the firmware LPM_SUS log.",
                    UVM_LOW)
                disable WAIT_DUT_L1;
                disable WAIT_DEV_K_EXIT;
            end
        join_any

        #10us;

        // Step 7: exit L1.
        if (dev_driven_exit) begin
            // -----------------------------------------------------------------
            // Device-initiated L1 exit, host-completed.
            //
            // The firmware rings the doorbell: it writes DEVCMDSTAT with bit 19
            // low while the read-only LPM_SUS (19) and LPM_REWP (20) are both
            // set, which sets the separate flop usbreg_lpmremotewakeup
            // (usb_reg_if.m.vhdl:645-647). The PIE then walks
            // LPM_SW_WAKEUP_WF_CLK -> LPM_SW_WAKEUP_1 (T_60us K) ->
            // SW_WAKEUP_2 (T_TxENDDELAY) -> SW_WAKEUP_3.
            //
            // BUS_EVENT_SW_WAKEUP_3 waits on ls_filt = LINESTATE_SE0 and has NO
            // timeout arm. If the host never terminates the resume the DUT
            // parks there forever. So the host MUST respond - but it must
            // respond REACTIVELY, only after the device has actually asked.
            //
            // WHY THIS IS NOT A TIMED RESUME. The wait below is on
            // usb_dut_wakeup_k_seen, published by
            // caliptra_ss_usb_device_wakeup_checker only after the DUT has held
            // its own UTMI TXValid output with linestate=K for K_MIN_HOLD. The
            // host half is therefore caused by the device's request, not
            // scheduled alongside it. A DUT that never requests wakeup cannot
            // be rescued by a well-timed host resume: the event never fires,
            // the takeover is skipped, and case (i) below is reported. That is
            // the whole point of doing it this way.
            //
            // REQUIRES +usb_device_wakeup_check. Without it the checker is
            // disabled, the event never fires, and this path degenerates to
            // "no host response" - the original stall. The yml sets it.
            // -----------------------------------------------------------------

            // The takeover itself is NOT performed here. It is performed by the
            // K_RESPONDER thread forked at step 4a, for the latency reason
            // documented there. This block only OBSERVES that thread, so the
            // one-shot event is consumed in exactly one place.
            //
            // Polling flags rather than re-waiting the event is deliberate:
            // uvm_event::wait_trigger() on an event that has ALREADY fired
            // blocks until the next trigger, and this event fires once per run,
            // so a second wait here would hang forever. device_k_seen and
            // host_takeover_done are set by the responder thread.
            begin: OBSERVE_TAKEOVER
                int unsigned waited_us = 0;

                // Phase 1: did the device ask at all?
                while (!device_k_seen && waited_us < DEV_K_WAIT_MAX_US) begin
                    #1us; waited_us++;
                end

                // Phase 2: if it did, give the responder room to finish
                // driving the terminating SE0.
                if (device_k_seen) begin
                    waited_us = 0;
                    while (!host_takeover_done && waited_us < TAKEOVER_DONE_MAX_US) begin
                        #1us; waited_us++;
                    end
                end
            end

            if (!device_k_seen) begin
                // Case (i): the device never asked. This is the real failure
                // and it is an error here as well as in the checker, because
                // the whole purpose of this variant is the device's request.
                // Deliberately NO host resume was driven: driving one would
                // move the DUT out of L1 and make the run look healthy.
                `uvm_error("USB_LPM_L1_SEQ",
                    $sformatf("Device-initiated L1 exit FAILED at the device half: the DUT never drove resume K within %0d us of L1 entry, so usbreg_lpmremotewakeup was never acted on. Check, in order: that +usb_device_wakeup_check is on (without it this can never pass); that the firmware was built with USB_LPM_DEVICE_INITIATED_EXIT=1; that DEVCMDSTAT.LPM_SUS and LPM_REWP were both set when the doorbell write was issued, since the write is only decoded in that state and is not latched; and that LPM_BREMOTEWAKE was 1 in the LPM token. No host resume was driven, on purpose.",
                              DEV_K_WAIT_MAX_US))
            end else if (!host_takeover_done) begin
                // The device asked and the responder started, but the link
                // service sequence had not returned within the grace window.
                // Distinct from the post-resume traffic failure below: there
                // the host half completed and the handshake still did not
                // take, here the host half did not even finish.
                `uvm_error("USB_LPM_L1_SEQ",
                    $sformatf("Device-initiated L1 exit: the DUT requested wakeup at %0t (CHK_DEVICE_WAKEUP_K satisfied) but the host takeover did not complete within %0d us of being triggered, i.e. clear_suspend was started and did not return. Note that both sequences tried here before (clear_l1suspend and remote_wakeup_after_l1suspend) always returned immediately, so if this fires it is new behaviour. Likely causes: the link service sequencer was busy, or the VIP link was in a state whose get_usb_20_link_start_state() precondition this sequence blocks on. This is a HOST-side testbench issue, not a device remote-wakeup failure: the device half already passed.",
                              device_k_seen_time, TAKEOVER_DONE_MAX_US))


            end else begin
                `uvm_info("USB_LPM_L1_SEQ",
                    "Device half and host takeover both complete; waiting for the DUT to leave the low-power state.",
                    UVM_LOW)
            end
        end else begin
            `uvm_info("USB_LPM_L1_SEQ", "Host driving L1 exit (clear_l1suspend)...", UVM_LOW)
            begin
                svt_usb_link_service_clear_l1suspend_sequence clr_l1;
                clr_l1 = svt_usb_link_service_clear_l1suspend_sequence::type_id::create("clr_l1");
                clr_l1.start(p_sequencer.link_service_sequencer);
            end
            `uvm_info("USB_LPM_L1_SEQ", "Host L1 exit complete.", UVM_LOW)
        end

        // Step 8: confirm the link is back to ENABLED. Timeout ceiling only.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED
                   && poll_cnt < ENABLED_POLL_MAX_US) begin
                #1us; poll_cnt++;
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                `uvm_info("USB_LPM_L1_SEQ",
                    $sformatf("Link ENABLED again %0d us after L1 exit.", poll_cnt), UVM_LOW)
            else if (dev_driven_exit)
                // NOT an error on the device-driven leg. This is a level check
                // on the HOST VIP's view of the link, and the comment at the
                // post-exit verdict below already records that it is unsound
                // here: it passes trivially if the VIP never moved to
                // L1SUSPENDED in its own view, and at FS the VIP stays in
                // L1SUSPENDED and never returns to ENABLED by itself after a
                // device-initiated exit. The link does come back - the
                // PostL1_GetDescriptor below resumes bus traffic and that is
                // what unparks the PIE - so failing here would reject a run
                // that then goes on to prove the exit end-to-end. The real
                // verdicts on this leg are CHK_DEVICE_WAKEUP_K and the
                // post-resume traffic check.
                `uvm_info("USB_LPM_L1_SEQ",
                    $sformatf("Link not ENABLED in the host VIP's view %0d us after the device-initiated L1 exit (link=%0s); continuing. Not failed here on purpose - the post-resume traffic check below is the verdict for this leg.",
                        poll_cnt, shared_status.link_usb_20_state.name()),
                    UVM_LOW)
            else
                // Host-driven leg: the host originated the exit, so the host
                // VIP is expected to be back in ENABLED and this remains a
                // real failure.
                `uvm_error("USB_LPM_L1_SEQ",
                    $sformatf("Timeout waiting for ENABLED after L1 exit; link=%0s",
                        shared_status.link_usb_20_state.name()))

        end

        // Wait for the DUT to leave the low-power state. Same shape as step 6.
        fork
            begin: WAIT_DUT_L1_EXIT
                dut_resume_ev.wait_trigger();
                `uvm_info("USB_LPM_L1_SEQ",
                    "DUT left low-power state (UTMI SuspendM high again).", UVM_LOW)
                disable L1_EXIT_TIMEOUT;
            end
            begin: L1_EXIT_TIMEOUT
                #L1_EXIT_WAIT_MAX;
                `uvm_info("USB_LPM_L1_SEQ",
                    "L1 exit wait ceiling reached without the DUT leaving the low-power state; continuing. Checked as CHK_RESUME_SEEN.",
                    UVM_LOW)
                disable WAIT_DUT_L1_EXIT;
            end
        join_any

        // ---------------------------------------------------------------------
        // Device-initiated path only: prove the link really came back.
        //
        // WHAT THIS DELIBERATELY DOES NOT USE, AND WHY. An earlier revision
        // keyed the verdict on dut_resume_ev.is_on(). That was WRONG and gave a
        // false failure on a healthy run. In caliptra_ss_usb_suspend_resume_checker
        // the resume edge is gated on suspend_seen:
        //
        //     if (suspendm_prev === 1'b0 && suspendm === 1'b1
        //         && suspend_seen && !resume_seen)
        //
        // and suspend_seen needs a FALLING SuspendM edge. On this L1 path
        // SuspendM never drops - the checker arms at level 1 and no
        // "DUT entered low-power state" line is ever produced - so
        // usb_dut_resume_seen is UNFIREABLE and the old test was false by
        // construction, regardless of what the DUT or the host did.
        //
        // Two other tempting indicators are also unsound here:
        //   - step 8's link_usb_20_state == ENABLED is the HOST VIP's view, and
        //     is a level check rather than a transition, so it passes trivially
        //     if the VIP never moved to L1SUSPENDED in its own view.
        //   - DEVCMDSTAT.LPM_SUS falling marks the PIE ENTERING the wakeup FSM,
        //     not completing it. It was observed dropping 14 us BEFORE the host
        //     responded at all, so the PIE can still be parked in SW_WAKEUP_3
        //     with LPM_SUS already 0.
        //
        // So the verdict is end-to-end instead: if the device really completed
        // its own resume, it answers traffic afterwards. That needs no internal
        // signals and cannot pass while the PIE is stuck in SW_WAKEUP_3, since
        // a parked device cannot service a control transfer. Same approach as
        // post_resume_traffic_check() in
        // caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence.
        // ---------------------------------------------------------------------
        if (dev_driven_exit) begin
            if (!device_k_seen) begin
                `uvm_info("USB_LPM_L1_SEQ",
                    "Skipping the post-resume traffic check: the DUT was never seen driving resume K, so there was no device-initiated resume for it to survive. That failure is already reported above and as CHK_DEVICE_WAKEUP_K.",
                    UVM_LOW)
            end else begin
                // RESTART SOF FIRST. Step 4 stopped SOF generation before the
                // LPM token and nothing has restarted it since, so by this
                // point the host has been idle for well over 100 us and the
                // host VIP's own inactivity timer has taken the link to
                // SUSPENDED. A control transfer issued into a suspended link
                // is never granted and simply times out, which produced a
                // misleading "device never answered" failure on a run where
                // the device was fine.
                //
                // Measured: with SOF off from 491379 ns, the physical trace
                // shows the host driving a fresh suspend/resume pair at
                // 815998 ns, i.e. the link really did drop out from under the
                // transfer. The base sequence's own timeout message calls this
                // out ("Check whether the link went SUSPENDED - tinactivity
                // must stay longer than the largest idle gap").
                //
                // NOTE ON ORDERING. This sits AFTER step 8's ENABLED check, so
                // step 8 polls a bus with no SOF on it. That is tolerated
                // rather than ideal: at HS the takeover leaves the link
                // already ENABLED on the first sample (poll_cnt = 0) and step 8
                // passes immediately. Moving the restart above step 8 was tried
                // and is NOT an improvement - it does not help the FS case,
                // whose real problem is that the MCU halts before the verdict
                // below is reached, and it perturbs a known-good HS flow. Leave
                // it here.
                //
                // The L2 analogue does the same thing for the same reason -
                // see the sof_on2 restart in
                // caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence
                // immediately before its post_resume_traffic_check().
                begin
                    svt_usb_protocol_service_20_sof_on_sequence sof_on_post;
                    sof_on_post =
                        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                            "sof_on_after_l1_exit"
                        );
                    sof_on_post.start(p_sequencer.prot_service_sequencer);
                end
                `uvm_info("USB_LPM_L1_SEQ",
                    "SOF generation restarted after the L1 exit. Without this the host link goes SUSPENDED on inactivity and the post-resume transfer below can never be granted, which looks exactly like a device that stopped answering.",
                    UVM_LOW)

                // Re-anchor on USBDC0 and ask for its device descriptor. A
                // successful, correctly-sized answer is the proof that the
                // K -> host takeover -> terminating SE0 -> SW_WAKEUP_3 exit
                // handshake actually completed.
                usb_cfg.remote_device_cfg[0].device_address = LPM_DEV_ADDRESS;
                host_agent_h.reconfigure(usb_cfg);

                `uvm_info("USB_LPM_L1_SEQ",
                    "postL1: issuing GetDescriptor(Device) to USBDC0 to confirm the device still answers traffic after waking itself. This, not any SuspendM event, is the case (iii) verdict.",
                    UVM_LOW)

                do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
                    svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100,
                    16'h0000, 16'd18, LPM_DEV_ADDRESS,
                    "PostL1_GetDescriptor", usb_cfg);
                wait_xfer_done(host_agent_h, "PostL1_GetDescriptor");

                if (xfer_wait_timed_out) begin
                    `uvm_error("USB_LPM_L1_SEQ",
                        $sformatf("Device-initiated L1 exit FAILED to complete: the DUT drove resume K at %0t (CHK_DEVICE_WAKEUP_K satisfied) and the host answered, but USBDC0 never completed a GetDescriptor afterwards. The device half worked and the exit handshake did not, so the most likely state is the PIE still parked in BUS_EVENT_SW_WAKEUP_3 waiting on ls_filt = LINESTATE_SE0 - i.e. the terminating SE0 did not land inside that state. Check the takeover latency logged above against the ~90 us budget (T_60us K + T_TxENDDELAY), and consider raising HOST_L1_RESUME_K_PS (currently %0.0f ps). Do NOT pre-schedule the host resume to work around this: that would stop the test proving the device can request wakeup.",
                                  device_k_seen_time, HOST_L1_RESUME_K_PS))
                end else begin
                    `uvm_info("USB_LPM_L1_SEQ",
                        $sformatf("Device-initiated L1 exit PASS: the DUT requested wakeup itself at %0t, the host answered reactively, and USBDC0 answered post-resume traffic - so the full exit handshake completed and the device survived its own remote wakeup. CHK_DEVICE_WAKEUP_K remains the device-side verdict.",
                                  device_k_seen_time),
                        UVM_LOW)
                end

                // POST-RESUME LINK STATE CHECK.
                //
                // Link-level verdict for the device-driven leg, and a
                // companion to the transfer check above rather than a
                // replacement: the transfer check proves the DEVICE answered,
                // this one proves the host VIP's link state machine actually
                // walked the L1-exit path instead of the traffic merely
                // sneaking through.
                //
                // IT MUST SIT AFTER wait_xfer_done, AND THE PLACEMENT WAS
                // ESTABLISHED THE HARD WAY. At FS the queued
                // CLEAR_PORT_SUSPEND is consumed when the first post-L1
                // TRANSFER IS PREPARED - not by the SOF restart, not by
                // reconfigure(), and not by elapsed time. From the transcript:
                //
                //   1325350.945 ns  sof_on_after_l1_exit, then reconfigure();
                //                   link still L1SUSPENDED, nothing consumed
                //   1525350.945 ns  protocol_processor [prepare_transaction]
                //                   "Preparing SETUP" AND, in the same delta,
                //                   L1SUSPENDED -> L1RESUMING
                //   1600350.945 ns  L1RESUMING -> SEND_EOR   (+75.000 us)
                //   1611020.538 ns  SEND_EOR   -> ENABLED    (+10.670 us)
                //   1618304.454 ns  SETUP token completes, device answers
                //
                // So the resume takes 85.67 us from the transfer being queued,
                // and the transfer then completes on the resumed link. Two
                // earlier placements were therefore both unpassable, and each
                // produced the identical error at 1525350.945 ns:
                //   - before the SOF restart / before reconfigure(): the
                //     trigger had not happened yet.
                //   - after reconfigure() but before do_control_xfer(): still
                //     before the trigger. This one also looked deceptively
                //     like proof that reconfigure() was the trigger, because
                //     the 200 us poll happened to expire in the same delta the
                //     transfer was later queued. That inference was WRONG;
                //     moving reconfigure() earlier left the error timestamp
                //     unchanged, which is what disproved it.
                // Raising ENABLED_POLL_MAX_US cannot fix either case - the
                // poll blocks the thread that would issue the transfer, so a
                // longer ceiling just delays the trigger by the same amount.
                //
                // By this point ENABLED is already reached, so the loop below
                // normally exits at resume_poll_cnt = 0 and costs nothing. It
                // is kept as a loop rather than a bare sample only to tolerate
                // a late SEND_EOR -> ENABLED edge.
                //
                // L1RESUMING and SEND_EOR are intermediate, not terminal; they
                // are named in the failure message only so it can distinguish
                // a resume that started and stalled from one that never
                // started.
                begin
                    int unsigned resume_poll_cnt = 0;
                    while (shared_status.link_usb_20_state != svt_usb_types::ENABLED
                           && resume_poll_cnt < ENABLED_POLL_MAX_US) begin
                        #1us; resume_poll_cnt++;
                    end
                    if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                        `uvm_info("USB_LPM_L1_SEQ",
                            $sformatf("CHK_POST_L1_LINK_RESUMED PASSED: host VIP link is ENABLED (settled %0d us after the post-L1 transfer completed), so the L1 exit completed at the link level and not just at the device - the VIP walked L1SUSPENDED -> L1RESUMING -> SEND_EOR -> ENABLED.",
                                resume_poll_cnt),
                            UVM_LOW)
                    else
                        `uvm_error("USB_LPM_L1_SEQ",
                            $sformatf("CHK_POST_L1_LINK_RESUMED FAILED: the host VIP link is still %0s %0d us after the post-L1 transfer completed. Since the transfer is what consumes the queued CLEAR_PORT_SUSPEND, reaching here means the transfer finished without the link leaving the L1 state group. L1RESUMING or SEND_EOR means the resume started and stalled; L1SUSPENDED means it never started at all.",
                                shared_status.link_usb_20_state.name(), ENABLED_POLL_MAX_US))
                end

                // Release the MCU so it can halt now that the post-L1 traffic
                // check is done. See the long comment at request_mcu_stop().
                request_mcu_stop();
            end
        end

        // Observation window for the firmware to log the exit-side event.
        #POST_EXIT_OBS;

        // Closing the window is mandatory, not cosmetic: the checker evaluates
        // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN only on this event, so without
        // the trigger neither check runs and the test would pass regardless of
        // what the DUT did.
        obs_window_ev.trigger();

        `uvm_info("CALIPTRA_SS_USB_LPM_L1",
            "caliptra_ss_usb_fs_dev_lpm_l1_sequence complete.", UVM_LOW)

    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_LPM_L1_SEQUENCE_SV
