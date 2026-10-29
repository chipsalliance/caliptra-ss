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
// Why the LPM token is sent unconditionally rather than after a capability
// handshake: the hub front-end of this IP does not advertise LPM at all -
// usb_ep0_hub_descr.m.vhdl hardcodes bcdUSB=0x0200 and there is no BOS
// descriptor anywhere in the design - and the hub implements no
// SetPortFeature(PORT_L1). A real host would therefore never try LPM here.
// The device controller behind the hub, however, does implement LPM and its
// LPM state is genuinely wired out to SW-visible registers, so driving the
// token directly is both necessary and sufficient to exercise it. See
// docs/usb_l1_lpm_test_feasibility_report.md for the full RTL audit.
//
// DEV0 ONLY. DEV1's LPM control ports are tied "=> open" in
// ip_xxx_3511_hs_mem_compound_structure.a.vhdl, so a DEV1 variant of this
// test would be reporting an IP gap, not verifying a feature.
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

    // Empirical margin, identical rationale to the L2 sequence: acting on the
    // link before the VIP SM has settled in ENABLED can push it to
    // DISCONNECTED and start an unintended second bus-reset cycle.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Empirical margin. Lets enumeration traffic drain and the firmware finish
    // its post-enumeration register writes (usb_allow_clock_stop, LPM_SUP
    // check) before the LPM token arrives.
    localparam realtime PRE_LPM_SETTLE = 100us;

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

        // Step 2: settling delay. See LINK_SETTLE_DELAY.
        #LINK_SETTLE_DELAY;

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
