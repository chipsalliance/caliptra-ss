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

`ifndef CALIPTRA_SS_USB_HS_DEV_LPM_L1_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_LPM_L1_SEQUENCE_SV

// =============================================================================
// USB HS device L1 (LPM Sleep) entry / exit sequence (hub-composite IP).
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

class caliptra_ss_usb_hs_dev_lpm_l1_sequence extends caliptra_ss_usb_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_dev_lpm_l1_sequence)

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
    localparam realtime L1_EXIT_WAIT_MAX = 500us;

    // Empirical margin. Gives the MCU polling loop room to sample DEVCMDSTAT
    // once more and log the exit-side event before the checker window closes.
    localparam realtime POST_EXIT_OBS = 200us;

    // Poll ceiling in 1 us steps. Timeout only.
    localparam int unsigned ENABLED_POLL_MAX_US = 50000;

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
    // docs/SIM_RUNTIME_OPTIMIZATION.md. The firmware cross-checks this value
    // against the read-only LPM[3:0] HIRD_HW field, so changing it here means
    // changing the expected value in the log.
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

    function new(string name = "caliptra_ss_usb_hs_dev_lpm_l1_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        uvm_event dut_suspend_ev;
        uvm_event dut_resume_ev;
        uvm_event obs_window_ev;
        uvm_event arm_ev;

        bit dev_driven_exit = 0;

        // Resolve the shared events up front: get_global() creates on first
        // use, so resolving before the stimulus removes any race with the
        // checker triggering them.
        dut_suspend_ev = uvm_event_pool::get_global(DUT_SUSPEND_EVENT);
        dut_resume_ev  = uvm_event_pool::get_global(DUT_RESUME_EVENT);
        obs_window_ev  = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
        arm_ev         = uvm_event_pool::get_global(ARM_EVENT);

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
        fork
            begin: WAIT_DUT_L1
                dut_suspend_ev.wait_trigger();
                `uvm_info("USB_LPM_L1_SEQ",
                    "DUT entered low-power state after LPM token (UTMI SuspendM low).", UVM_LOW)
                disable L1_DWELL_TIMEOUT;
            end
            begin: L1_DWELL_TIMEOUT
                #L1_DWELL_MAX;
                `uvm_info("USB_LPM_L1_SEQ",
                    "L1 dwell ceiling reached without the DUT entering a low-power state; continuing. Checked as CHK_SUSPEND_SEEN and by the firmware LPM_SUS log.",
                    UVM_LOW)
                disable WAIT_DUT_L1;
            end
        join_any

        // Step 7: exit L1.
        if (dev_driven_exit) begin
            // Device-driven: the firmware asserts usbreg_lpmremotewakeup by
            // writing DEVCMDSTAT with bit 19 low while bits 19 and 20 are set.
            // The host must stay quiet here; driving a resume as well would
            // make the two indistinguishable in the log. Same warning as
            // caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence.
            `uvm_info("USB_LPM_L1_SEQ",
                "+usb_lpm_dev_wakeup=1: host will NOT drive L1 exit; expecting device-initiated wakeup from firmware built with USB_LPM_DEVICE_INITIATED_EXIT=1.",
                UVM_LOW)
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
            else
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

        // Observation window for the firmware to log the exit-side event.
        #POST_EXIT_OBS;

        // Closing the window is mandatory, not cosmetic: the checker evaluates
        // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN only on this event, so without
        // the trigger neither check runs and the test would pass regardless of
        // what the DUT did.
        obs_window_ev.trigger();

        `uvm_info("CALIPTRA_SS_USB_LPM_L1",
            "caliptra_ss_usb_hs_dev_lpm_l1_sequence complete.", UVM_LOW)

    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_LPM_L1_SEQUENCE_SV
