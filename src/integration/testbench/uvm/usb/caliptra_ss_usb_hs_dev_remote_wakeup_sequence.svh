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

`ifndef CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV

// =============================================================================
// USB HS device suspend / resume sequence (hub-composite IP).
//
// Topology note: on the hub-composite IP
// (ip_xxx_3511_hs_mem_compound_wrapper) the DUT is an on-chip 2-port USB hub
// with an embedded downstream device controller (USBDC0). The upstream link
// only comes up after the MCU firmware performs the two-phase hub bring-up:
// boot_usb_core() sets HUB_EN, then usb_hub_connect() sets HUB_CONNECT. Only
// after HUB_CONNECT does the hub present itself on the bus, so the host sees
// connect / reset / HS chirp and the link reaches ENABLED.
//
// This sequence drives and observes only the UPSTREAM link (host <-> hub), so
// it is unchanged in intent from the legacy flow. What the firmware can still
// observe on USBDC0 is a separate question: a hub is not required to propagate
// upstream suspend to a downstream port (that is normally per-port, via
// SetPortFeature(PORT_SUSPEND) addressed to the hub). See the test README
// "Scope and limitations".
//
// Naming note: despite "remote_wakeup", the resume here is HOST-initiated
// (clear_suspend below). The device does not signal wakeup upstream.
//
// Sequence flow:
//   1. Wait for HS host link to reach ENABLED.
//   2. Start SOF generation to keep the HS link alive.
//   3. Settling delay to allow VIP link SM to stabilize in ENABLED before SUSPEND.
//   4. Host drives SUSPEND signaling (SOF_OFF).
//   5. Wait for VIP link SM to reach SUSPENDED state.
//  5b. Arm the DUT-side checker (uvm_event usb_suspend_stimulus_armed). Before
//      this point SuspendM activity belongs to boot, not to this stimulus, so
//      the checker must not score it. See ARM_EVENT below.
//   6. Suspend dwell: wait until the DUT itself enters suspend, reported by
//      caliptra_ss_usb_suspend_resume_checker over the global uvm_event
//      usb_dut_suspend_seen, bounded by SUSPEND_DWELL as a timeout ceiling.
//   7. Host drives resume K-state via svt_usb_link_service_clear_suspend_sequence

//      on link_service_sequencer. This is the only VIP sequence that actually
//      drives K-state on the bus; resume_transfer_processing_sequence must NOT
//      be used here because it drives zero bus activity and returns instantly.
//   8. Restart SOF generation to hold link ENABLED after resume.
//   9. Poll for link ENABLED after resume, then wait for the DUT to leave
//      suspend (uvm_event usb_dut_resume_seen), bounded by RESUME_WAIT_MAX.
//  10. Short observation window, then close the checker observation window by
//      triggering uvm_event usb_suspend_resume_obs_window_done. Without that
//      trigger the checker never evaluates either check, so this step is a
//      functional requirement, not just reporting.
//
// DUT-side verdict: the pass/fail decision for this test lives in
// caliptra_ss_usb_suspend_resume_checker (enabled by +usb_suspend_resume_check),
// which watches the DUT UTMI SuspendM output. This sequence only drives the
// host side and reports timing; do not treat its own uvm_errors as the whole
// check.
// =============================================================================


class caliptra_ss_usb_hs_dev_remote_wakeup_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_dev_remote_wakeup_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    // -------------------------------------------------------------------------
    // Sequence timing knobs.
    //
    // These were literals inline in body(); they are hoisted here because they
    // dominate the simulated time of this test. Each is tagged
    // either "physics/VIP bound" (the value is set by a real protocol or
    // VIP-internal timer and must not go below that bound) or "empirical
    // margin" (a guess with generous headroom, and therefore the first
    // candidate for runtime reduction once a baseline log gives the real
    // timestamps).
    //
    // Do not retune these in the same change as a topology or firmware change:
    // a resulting failure could not be attributed to either.
    // -------------------------------------------------------------------------

    // Empirical margin. Guards a real failure mode: driving SOF_OFF while the
    // VIP link SM is still walking TRANSMIT -> ENABLED makes the link go
    // DISCONNECTED and starts an unintended second bus-reset cycle. The
    // observed settle is a few microseconds, so most of this is headroom.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling, not a dwell. The sequence now waits on the uvm_event
    // usb_dut_suspend_seen published by caliptra_ss_usb_suspend_resume_checker
    // and moves on the moment the DUT drives UTMI SuspendM low, so in the
    // passing case this value costs nothing. It only bounds how long we sit
    // there when the DUT never suspends at all, which is exactly the failure
    // the checker reports. Previously this was an unconditional 2 ms dwell.
    //
    // Sizing, and a build-dependent caveat. The device decides the bus is
    // suspended from absence of bus activity, using the T_SUSPEND_DET timer in
    // usb_pie.m.vhdl. In this testbench the DUT is elaborated with
    // G_SIM_CHIRP_TIMERS=1 (see caliptra_ss_top_tb.sv), so T_SUSPEND_DET is
    // 200 us and the 2 ms ceiling here has ample margin. In a build with
    // G_SIM_CHIRP_TIMERS=0 the device uses the spec value of 3.072 ms, which is
    // longer than this ceiling, so the wait would time out before the DUT could
    // physically react and CHK_SUSPEND_SEEN would fail for a reason that is not
    // a DUT bug. If this test is ever run against a spec-timer build, raise
    // this ceiling above 3.072 ms first.
    localparam realtime SUSPEND_DWELL = 2ms;

    // Timeout ceiling for the DUT leaving suspend after the host drove resume
    // K-state. Same structure as SUSPEND_DWELL: the wait ends early on
    // usb_dut_resume_seen.
    localparam realtime RESUME_WAIT_MAX = 500us;

    // Empirical margin. Lets the MCU polling loop sample DEVCMDSTAT once more
    // and print the resume-side suspend-change event before the sequence ends,
    // and gives the DUT a little slack past the resume edge before the checker
    // observation window is closed.
    localparam realtime POST_RESUME_OBS = 200us;


    // Poll ceilings, in 1 us steps. Timeouts only: the loops exit as soon as
    // the state is reached, so they cost nothing in the passing case and must
    // not be trimmed for runtime.
    localparam int unsigned SUSPEND_POLL_MAX_US = 10000;  // 10 ms ceiling
    localparam int unsigned ENABLED_POLL_MAX_US = 50000;  // 50 ms ceiling

    // -------------------------------------------------------------------------
    // Global uvm_event names shared with caliptra_ss_usb_suspend_resume_checker.
    // These strings are the only coupling between this sequence and the
    // testbench-scope checker module, which is why they are kept together here
    // and duplicated verbatim there: a uvm_sequence cannot reach into testbench
    // scope, and the checker must not depend on the UVM package.
    // Keep both copies in sync.
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
    // complete suspend/resume cycle, which produced a false PASS and also made
    // the sequence sit out the full SUSPEND_DWELL and RESUME_WAIT_MAX ceilings
    // because uvm_event::trigger() is momentary and had already fired.
    localparam string ARM_EVENT = "usb_suspend_stimulus_armed";


    function new(string name = "caliptra_ss_usb_hs_dev_remote_wakeup_sequence");
        super.new(name);
    endfunction

    virtual task pre_start();
        uvm_phase phase;
        super.pre_start();
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.raise_objection(this);
    endtask

    virtual task post_start();
        uvm_phase phase;
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.drop_objection(this);
    endtask

    virtual task body();
        svt_usb_agent    host_agent_h;
        uvm_component    parent_comp;
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

        parent_comp = p_sequencer.get_parent();

        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("CALIPTRA_SS_USB_HS_D",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("CALIPTRA_SS_USB_HS_D", "get_shared_status returned null.")

        // Step 1: Wait for HS link ENABLED.
        fork
            begin: WE
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable RE;
            end
            begin: RE
                forever begin
                    #10us `uvm_info("CALIPTRA_SS_USB_HS_D",
                        $sformatf("link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("CALIPTRA_SS_USB_HS_D", "HS link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on;
            sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
            sof_on.start(p_sequencer.prot_service_sequencer);
            `uvm_info("CALIPTRA_SS_USB_HS_D", "SOF generation started.", UVM_LOW)
        end

        // Step 3: Settling delay after link-up.
        // The VIP link SM transitions through TRANSMIT -> ENABLED in the first
        // few microseconds after bus reset. Issuing SOF_OFF inside that window
        // causes the link to go DISCONNECTED and trigger an unintended second
        // bus-reset cycle. See LINK_SETTLE_DELAY above.
        #LINK_SETTLE_DELAY;

        // Step 4: Host drives SUSPEND signaling.
        `uvm_info("USB_HS_DEV_RW_SEQ", "Suspending link...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_RW_SEQ", "SUSPEND signaling complete.", UVM_LOW)

        // Step 5: Wait for VIP link SM to reach SUSPENDED state.
        // SOF_OFF returns immediately; the 3ms USB 2.0 idle timer runs inside
        // the VIP. We must confirm SUSPENDED before proceeding so that the
        // MCU has a real suspended-bus condition to observe.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::SUSPENDED
                   && poll_cnt < SUSPEND_POLL_MAX_US) begin
                #1us; poll_cnt++;
            end
            if (shared_status.link_usb_20_state == svt_usb_types::SUSPENDED)
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    $sformatf("VIP link SUSPENDED after %0d us.", poll_cnt), UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_RW_SEQ", "Timeout waiting for VIP link SUSPENDED.")
        end

        // Step 5b: Arm the DUT-side checker.
        //
        // This is the point, and the earliest point, at which a change on the
        // DUT SuspendM output can be attributed to this stimulus: the host has
        // stopped SOF traffic and the VIP link has confirmed SUSPENDED, so any
        // subsequent SuspendM low is the device controller reacting to bus
        // idle. Everything before this is boot: SuspendM is held low out of
        // reset while the PHY clocks are gated off, and rises when firmware
        // writes DEVCMDSTAT in boot_usb_core. The checker ignores SuspendM
        // until this event and re-seeds its edge history from the level present
        // here, so that boot activity cannot be scored. See ARM_EVENT above.
        arm_ev.trigger();
        `uvm_info("USB_HS_DEV_RW_SEQ",
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to this stimulus.",
            UVM_LOW)

        // Step 6: Wait for the DUT to enter suspend.
        //
        // This used to be an unconditional "#2ms" dwell chosen to be safely
        // longer than the MCU polling loop. It is now a wait on the DUT itself:
        // caliptra_ss_usb_suspend_resume_checker triggers usb_dut_suspend_seen
        // when the device controller drives UTMI SuspendM low. In the passing
        // case that happens far sooner than SUSPEND_DWELL, so the dwell ends
        // because the DUT reacted rather than because a timer expired, and the
        // simulated time of the test drops accordingly.
        //
        // The timeout arm is deliberately not an error here. Whether the DUT
        // suspended at all is the checker's CHK_SUSPEND_SEEN, and reporting it
        // in one place keeps a single failure from producing two messages. On
        // timeout we still continue and drive the resume, so the log shows how
        // the rest of the flow behaved.
        fork
            begin: WAIT_DUT_SUSPEND
                dut_suspend_ev.wait_trigger();
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "DUT entered suspend (UTMI SuspendM low); ending suspend dwell early.",
                    UVM_LOW)
                disable SUSPEND_DWELL_TIMEOUT;
            end
            begin: SUSPEND_DWELL_TIMEOUT
                #SUSPEND_DWELL;
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "Suspend dwell ceiling reached without the DUT entering suspend; continuing. The checker reports this as CHK_SUSPEND_SEEN.",
                    UVM_LOW)
                disable WAIT_DUT_SUSPEND;
            end
        join_any


        // Step 7: Host drives resume K-state on the bus.
        // svt_usb_link_service_clear_suspend_sequence is the correct sequence:
        // it drives K-state from the host side and transitions the link SM
        // SUSPENDED -> S_RESUME -> ENABLED.
        // svt_usb_protocol_service_resume_transfer_processing_sequence must NOT
        // be used here: it drives no bus activity and returns at zero sim-time.
        `uvm_info("USB_HS_DEV_RW_SEQ", "Host driving resume K-state (clear_suspend)...", UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence clr_susp;
            clr_susp = svt_usb_link_service_clear_suspend_sequence::type_id::create("clr_susp");
            clr_susp.start(p_sequencer.link_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_RW_SEQ", "Host resume K-state complete.", UVM_LOW)

        // Step 8: Restart SOF generation after resume.
        // Without SOF the VIP link SM re-enters SUSPEND after the keepalive
        // timeout (~3ms). SOF must be restarted immediately after clear_suspend.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on2;
            sof_on2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on2");
            sof_on2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DEV_RW_SEQ", "SOF restarted after resume.", UVM_LOW)
        end

        // Step 9: Poll for link ENABLED after resume.
        // Timeout ceiling only; exits as soon as ENABLED is observed.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED
                   && poll_cnt < ENABLED_POLL_MAX_US) begin
                #1us; poll_cnt++;
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    $sformatf("Waiting ENABLED: link=%0s cnt=%0d",
                        shared_status.link_usb_20_state.name(), poll_cnt), UVM_HIGH)
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "Remote wakeup complete - link ENABLED.", UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_RW_SEQ",
                    $sformatf("Timeout waiting for ENABLED; link=%0s",
                        shared_status.link_usb_20_state.name()))
        end

        // Step 9b: Wait for the DUT to leave suspend.
        // Same shape as step 6: ends early on usb_dut_resume_seen, bounded by
        // RESUME_WAIT_MAX, and does not report its own error because the
        // checker owns CHK_RESUME_SEEN.
        fork
            begin: WAIT_DUT_RESUME
                dut_resume_ev.wait_trigger();
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "DUT left suspend (UTMI SuspendM high again).", UVM_LOW)
                disable RESUME_WAIT_TIMEOUT;
            end
            begin: RESUME_WAIT_TIMEOUT
                #RESUME_WAIT_MAX;
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "Resume wait ceiling reached without the DUT leaving suspend; continuing. The checker reports this as CHK_RESUME_SEEN.",
                    UVM_LOW)
                disable WAIT_DUT_RESUME;
            end
        join_any

        // Step 10: Observation window for MCU firmware to log DSUS_C resume event.
        // See POST_RESUME_OBS above: enough iterations of the MCU polling loop
        // to sample DEVCMDSTAT and print "Suspend change event 2".
        #POST_RESUME_OBS;

        // Close the checker observation window. This is mandatory, not
        // cosmetic: caliptra_ss_usb_suspend_resume_checker evaluates
        // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN only on this event, so without
        // the trigger neither check runs and the test would report PASSED
        // whatever the DUT did.
        obs_window_ev.trigger();

        `uvm_info("CALIPTRA_SS_USB_HS_D",
            "caliptra_ss_usb_hs_dev_remote_wakeup_sequence complete.", UVM_LOW)

    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV
