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

`ifndef CALIPTRA_SS_USB_HS_DEV_SANITY_SUSPEND_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_SANITY_SUSPEND_SEQUENCE_SV

// =============================================================================
// USB HS device suspend/resume sanity sequence (hub-composite IP).
//
// Naming note: renamed from caliptra_ss_usb_hs_dev_remote_wakeup_sequence. The
// scenario is host-driven - the host stops SOF to suspend the link and then
// drives resume K-state itself - so the device never initiates a wakeup and the
// old name was misleading. Device-initiated remote wakeup is covered by
// caliptra_ss_usb_hs_host_remotewakeup_fromdevice.
//
// Topology note: the DUT is an on-chip 2-port USB hub with an embedded
// downstream device controller (USBDC0). The upstream link only comes up after
// the MCU firmware performs the two-phase hub bring-up: boot_usb_core_hub()
// sets HUB_CTRL.HUB_EN, then usb_hub_connect() sets HUB_CONNECT. Only after
// HUB_CONNECT does the hub present itself on the bus, so the host sees
// connect / reset / HS chirp and the link reaches ENABLED. If the firmware
// omits usb_hub_connect() the link can never reach ENABLED and step 1 below
// reports it by name rather than hanging.
//
// Sequence flow:
//   1. Wait for the HS host link to reach ENABLED (bounded).
//   2. Start SOF generation to keep the HS link alive.
//   3. Settling delay to allow the VIP link SM to stabilise in ENABLED.
//   4. Host drives SUSPEND signaling (SOF_OFF).
//   5. Wait for the VIP link SM to reach SUSPENDED.
//  5b. Arm the DUT-side checker (uvm_event usb_suspend_stimulus_armed). Before
//      this point SuspendM activity belongs to boot, not to this stimulus, so
//      the checker must not score it. See ARM_EVENT below.
//   6. Wait for the DUT itself to enter suspend (uvm_event usb_dut_suspend_seen
//      from caliptra_ss_usb_suspend_resume_checker), bounded by SUSPEND_DWELL.
//   7. Host drives resume K-state via svt_usb_link_service_clear_suspend_sequence
//      on link_service_sequencer. This is the only VIP sequence that actually
//      drives K-state on the bus; resume_transfer_processing_sequence must NOT
//      be used here because it drives zero bus activity and returns instantly.
//   8. Restart SOF generation to hold the link ENABLED after resume.
//   9. Poll for link ENABLED after resume, then wait for the DUT to leave
//      suspend (uvm_event usb_dut_resume_seen), bounded by RESUME_WAIT_MAX.
//  10. Short observation window, then close the checker observation window by
//      triggering uvm_event usb_suspend_resume_obs_window_done. Without that
//      trigger the checker never evaluates either check, so this step is a
//      functional requirement, not just reporting.
//
// DUT-side verdict: the pass/fail decision lives in
// caliptra_ss_usb_suspend_resume_checker (enabled by +usb_suspend_resume_check,
// set in the test .mk and .yml), which watches the DUT UTMI SuspendM output.
// This sequence drives the host side and reports VIP-link timing only.
// =============================================================================

class caliptra_ss_usb_hs_dev_sanity_suspend_sequence extends caliptra_ss_usb_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_dev_sanity_suspend_sequence)

    // -------------------------------------------------------------------------
    // Sequence timing knobs. Values match the passing HS reference
    // caliptra_ss_usb_hs_dev_global_suspend_L2_sequence; keep them in step.
    // -------------------------------------------------------------------------

    // Empirical margin. Guards a real failure mode: driving SOF_OFF while the
    // VIP link SM is still walking TRANSMIT -> ENABLED makes the link go
    // DISCONNECTED and starts an unintended second bus-reset cycle.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling, not a dwell. The wait ends as soon as the checker
    // reports the DUT drove UTMI SuspendM low, so in the passing case this
    // costs nothing. The device decides the bus is suspended from the
    // T_SUSPEND_DET timer in usb_pie.m.vhdl, which is 200 us with
    // G_SIM_CHIRP_TIMERS=1 (the setting used in caliptra_ss_top_tb.sv). Against
    // a spec-timer build (3.072 ms) this ceiling must be raised first.
    localparam realtime SUSPEND_DWELL = 2ms;

    // Minimum time the DUT must be left in suspend before the host resumes it.
    //
    // This is a functional requirement, not a margin. The suspend/resume
    // checker triggers usb_dut_suspend_seen the instant UTMI SuspendM falls,
    // and both the clear_suspend link-service item and the SOF restart complete
    // without advancing simulation time. Without a hold here the whole resume
    // is driven in the same time step as the suspend, and a measured run showed
    // the device suspended for 1 ps (SuspendM low at 1087845.354 ns, high again
    // at 1087845.355 ns).
    //
    // A 1 ps suspend is not a meaningful stimulus whatever is being observed,
    // and it also let the shared checker report PASS on a degenerate event.
    // With this hold in place the measured window is a real 57.5 us of
    // PIE_SUSPEND. 50 us is small against the ~100 us the suspend detect
    // already costs, so it is cheap.
    //
    // Note what this hold did NOT fix. The firmware still observes zero
    // DEVCMDSTAT.DSUS_C events, because the on-chip hub does not propagate
    // upstream global suspend to its downstream port: USBDC0's own sync_suspend
    // stayed flat 0 for the whole window. That is a documented architectural
    // limitation, not a timing problem - see the observability note at the top
    // of caliptra_ss_usb_hs_dev_sanity_suspend.c. Do not raise this value hoping
    // to make DSUS_C appear.
    localparam realtime MIN_SUSPEND_HOLD = 50us;

    // Timeout ceiling for the DUT leaving suspend after the host drove resume
    // K-state. Same structure as SUSPEND_DWELL: ends early on the checker event.
    localparam realtime RESUME_WAIT_MAX = 500us;

    // Empirical margin. Lets the MCU polling loop sample DEVCMDSTAT once more
    // and print the resume-side suspend-change event, and gives the DUT slack
    // past the resume edge before the checker observation window is closed.
    localparam realtime POST_RESUME_OBS = 200us;

    // Poll ceilings in 1 us steps. Timeouts only: the loops exit as soon as the
    // state is reached, so they cost nothing in the passing case.
    localparam int unsigned SUSPEND_POLL_MAX_US = 10000;  // 10 ms ceiling
    localparam int unsigned ENABLED_POLL_MAX_US = 50000;  // 50 ms ceiling

    // Ceiling for the initial link bring-up. Sized well above the observed
    // bring-up (bus reset at ~240 us, enumeration done under 1 ms) so that a
    // timeout here means the device never connected at all.
    localparam int unsigned LINK_UP_TIMEOUT_US  = 3000;   // 3 ms ceiling

    // -------------------------------------------------------------------------
    // Global uvm_event names shared with caliptra_ss_usb_suspend_resume_checker.
    // These strings are the only coupling between this sequence and the
    // testbench-scope checker module, and are duplicated verbatim there: a
    // uvm_sequence cannot reach into testbench scope and the checker must not
    // depend on the UVM package. Keep both copies in sync.
    // -------------------------------------------------------------------------
    // Triggered by this sequence to tell the checker its observation window has
    // closed and both checks may now be evaluated.
    localparam string OBS_WINDOW_EVENT  = "usb_suspend_resume_obs_window_done";
    // Triggered by the checker when the DUT drives UTMI SuspendM low / high.
    localparam string DUT_SUSPEND_EVENT = "usb_dut_suspend_seen";
    localparam string DUT_RESUME_EVENT  = "usb_dut_resume_seen";
    // Triggered by this sequence to arm the checker's SuspendM edge detector.
    // Must not be triggered before the host has actually driven suspend: out of
    // reset the DUT holds SuspendM low by design (usb_pie.m.vhdl BUS_EVENT_INIT
    // drives suspendm from usbreg_pll_on or usbreg_dev_connect, both 0 until
    // firmware writes DEVCMDSTAT), and it rises again inside boot_usb_core. A
    // checker watching from time zero latches that boot-time low-then-high as a
    // complete suspend/resume cycle, which is a false PASS.
    localparam string ARM_EVENT = "usb_suspend_stimulus_armed";

    function new(string name = "caliptra_ss_usb_hs_dev_sanity_suspend_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent    host_agent_h;
        svt_usb_status   shared_status;

        // Handles to the events shared with the DUT-side checker. Resolved up
        // front: get_global() creates the event on first use, so resolving the
        // DUT-reaction events before the suspend is driven removes any race
        // with the checker triggering them.
        uvm_event dut_suspend_ev;
        uvm_event dut_resume_ev;
        uvm_event obs_window_ev;
        uvm_event arm_ev;

        dut_suspend_ev = uvm_event_pool::get_global(DUT_SUSPEND_EVENT);
        dut_resume_ev  = uvm_event_pool::get_global(DUT_RESUME_EVENT);
        obs_window_ev  = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
        arm_ev         = uvm_event_pool::get_global(ARM_EVENT);

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();

        // Step 1: Wait for HS link ENABLED.
        // Bounded on purpose. The previous shape was an unbounded
        // wait (link_usb_20_state == ENABLED) inside a fork/join, which turned
        // a firmware bring-up failure into a silent hang with zero UVM_ERROR.
        // wait_for_link_enabled() reports the timeout and names hub bring-up
        // (HUB_EN / HUB_CONNECT) as the thing to check.
        //
        // Ordering is deliberately link-first, SOF-second: the suspend/resume
        // checker arms on the first SOF, so SOF must not start before link-up.
        wait_for_link_enabled(shared_status, "HS host link", LINK_UP_TIMEOUT_US);

        // Step 2: Start SOF generation.
        start_sof_generation();

        // Step 3: Settling delay after link-up. See LINK_SETTLE_DELAY above.
        #LINK_SETTLE_DELAY;

        // Step 4: Host drives SUSPEND signaling.
        `uvm_info("USB_HS_DEV_SS_SEQ", "Suspending link...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_SS_SEQ", "SUSPEND signaling complete.", UVM_LOW)

        // Step 5: Wait for the VIP link SM to reach SUSPENDED.
        // SOF_OFF returns immediately; the USB 2.0 idle timer runs inside the
        // VIP. Confirm SUSPENDED before proceeding so that the MCU has a real
        // suspended-bus condition to observe.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::SUSPENDED
                   && poll_cnt < SUSPEND_POLL_MAX_US) begin
                #1us; poll_cnt++;
            end
            if (shared_status.link_usb_20_state == svt_usb_types::SUSPENDED)
                `uvm_info("USB_HS_DEV_SS_SEQ",
                    $sformatf("VIP link SUSPENDED after %0d us.", poll_cnt), UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_SS_SEQ", "Timeout waiting for VIP link SUSPENDED.")
        end

        // Step 5b: Arm the DUT-side checker.
        //
        // This is the earliest point at which a change on the DUT SuspendM
        // output can be attributed to this stimulus: the host has stopped SOF
        // traffic and the VIP link has confirmed SUSPENDED, so any subsequent
        // SuspendM low is the device controller reacting to bus idle.
        // Everything before this is boot. See ARM_EVENT above.
        arm_ev.trigger();
        `uvm_info("USB_HS_DEV_SS_SEQ",
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to this stimulus.",
            UVM_LOW)

        // Step 6: Wait for the DUT to enter suspend.
        //
        // This replaces an unconditional dwell. The timeout arm is deliberately
        // not an error: whether the DUT suspended at all is the checker's
        // CHK_SUSPEND_SEEN, and reporting it in one place keeps a single
        // failure from producing two messages. On timeout the flow continues so
        // the log shows how the rest of the sequence behaved.
        // Note on the idiom, which matters here and is easy to get wrong.
        // uvm_event::trigger() is momentary: it only releases a wait that is
        // already pending at that instant. wait_ptrigger() does NOT fix this -
        // it only returns early for a trigger in the same time slice, so across
        // any elapsed time it blocks exactly like wait_trigger(). The sticky
        // state is is_on(), set by trigger() and cleared only by reset(), so the
        // test has to be hoisted out of the fork. See note 24 section 7.5.
        if (dut_suspend_ev.is_on()) begin
            `uvm_info("USB_HS_DEV_SS_SEQ",
                "DUT had already entered suspend (UTMI SuspendM low) before this wait; not forking.",
                UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_SUSPEND
                    dut_suspend_ev.wait_trigger();
                    `uvm_info("USB_HS_DEV_SS_SEQ",
                        "DUT entered suspend (UTMI SuspendM low); ending suspend dwell early.",
                        UVM_LOW)
                    disable SUSPEND_DWELL_TIMEOUT;
                end
                begin: SUSPEND_DWELL_TIMEOUT
                    #SUSPEND_DWELL;
                    `uvm_info("USB_HS_DEV_SS_SEQ",
                        "Suspend dwell ceiling reached without the DUT entering suspend; continuing. The checker reports this as CHK_SUSPEND_SEEN.",
                        UVM_LOW)
                    disable WAIT_DUT_SUSPEND;
                end
            join_any
        end

        // Step 6b: Hold the DUT in suspend. See MIN_SUSPEND_HOLD above: the
        // resume below costs no simulation time, so without this the device
        // leaves suspend in the same time step it entered and DEVCMDSTAT.DSUS_C
        // never registers.
        #MIN_SUSPEND_HOLD;
        `uvm_info("USB_HS_DEV_SS_SEQ",
            $sformatf("Held the DUT in suspend for %0t before resuming.", MIN_SUSPEND_HOLD),
            UVM_LOW)

        // Step 7: Host drives resume K-state on the bus.
        `uvm_info("USB_HS_DEV_SS_SEQ", "Host driving resume K-state (clear_suspend)...", UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence clr_susp;
            clr_susp = svt_usb_link_service_clear_suspend_sequence::type_id::create("clr_susp");
            clr_susp.start(p_sequencer.link_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_SS_SEQ", "Host resume K-state complete.", UVM_LOW)

        // Step 8: Restart SOF generation after resume.
        // Without SOF the VIP link SM re-enters SUSPEND after the keepalive
        // timeout, so SOF must be restarted immediately after clear_suspend.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on2;
            sof_on2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on2");
            sof_on2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DEV_SS_SEQ", "SOF restarted after resume.", UVM_LOW)
        end

        // Step 9: Poll for link ENABLED after resume. Ceiling only.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED
                   && poll_cnt < ENABLED_POLL_MAX_US) begin
                #1us; poll_cnt++;
                `uvm_info("USB_HS_DEV_SS_SEQ",
                    $sformatf("Waiting ENABLED: link=%0s cnt=%0d",
                        shared_status.link_usb_20_state.name(), poll_cnt), UVM_HIGH)
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                `uvm_info("USB_HS_DEV_SS_SEQ",
                    "Host resume complete - link ENABLED.", UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_SS_SEQ",
                    $sformatf("Timeout waiting for ENABLED; link=%0s",
                        shared_status.link_usb_20_state.name()))
        end

        // Step 9b: Wait for the DUT to leave suspend.
        // Same shape as step 6; the checker owns CHK_RESUME_SEEN.
        // Same is_on() hoist as step 6, and this is the step where it was
        // measured to matter: step 9's ENABLED poll above consumed 22 us before
        // this point, by which time the resume event had long since fired. The
        // previous shape therefore paid the whole 500 us RESUME_WAIT_MAX and
        // printed the ceiling message at 1659845 ns - 500 us *after* it had
        // already printed "Host resume complete - link ENABLED" at
        // 1109845 ns. Two contradictory lines about one event.
        if (dut_resume_ev.is_on()) begin
            `uvm_info("USB_HS_DEV_SS_SEQ",
                "DUT had already left suspend (UTMI SuspendM high again) before this wait; not forking.",
                UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_RESUME
                    dut_resume_ev.wait_trigger();
                    `uvm_info("USB_HS_DEV_SS_SEQ",
                        "DUT left suspend (UTMI SuspendM high again).", UVM_LOW)
                    disable RESUME_WAIT_TIMEOUT;
                end
                begin: RESUME_WAIT_TIMEOUT
                    #RESUME_WAIT_MAX;
                    `uvm_info("USB_HS_DEV_SS_SEQ",
                        "Resume wait ceiling reached without the DUT leaving suspend; continuing. The checker reports this as CHK_RESUME_SEEN.",
                        UVM_LOW)
                    disable WAIT_DUT_RESUME;
                end
            join_any
        end

        // Step 10: Observation window for the MCU firmware to log the
        // resume-side DSUS_C event. See POST_RESUME_OBS above.
        #POST_RESUME_OBS;

        // Close the checker observation window. This is mandatory, not
        // cosmetic: caliptra_ss_usb_suspend_resume_checker evaluates
        // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN only on this event, so without
        // the trigger neither check runs and the test would report PASSED
        // whatever the DUT did.
        obs_window_ev.trigger();

        `uvm_info("CALIPTRA_SS_USB_HS_D",
            "caliptra_ss_usb_hs_dev_sanity_suspend_sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_SANITY_SUSPEND_SEQUENCE_SV
