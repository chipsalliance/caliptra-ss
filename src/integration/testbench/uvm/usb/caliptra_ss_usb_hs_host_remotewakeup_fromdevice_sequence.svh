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

`ifndef CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV

// =============================================================================
// Device-initiated remote wakeup, HIGH SPEED, hub-composite IP.
//
// The only test pair in which the resume is STARTED by the device: the MCU
// firmware calls usb_request_remote_wakeup(), USBDC0 drives resume K upstream,
// and the host must then take over and terminate it with a low-speed EOP.
//
// Verdict: CHK_DEVICE_WAKEUP_K in caliptra_ss_usb_device_wakeup_checker (DUT
// TXValid + linestate=K). Not any VIP status field.
//
// Design notes, flow description, constant derivations, the pie resume timeline
// and the fork/disable idiom all live in a single note. Read it before changing
// anything here:
//   caliptra_ss_nxp_dv_accessories/docs/handover/claude_md/
//       25_usb_remotewakeup_fromdevice_design_notes.md
// The FS -> HS port record and the measured HS failure are in note 24 of the
// same directory.
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence)

    string MSG_ID = "USB_HS_RW_FROMDEV_SEQ";

    // Hub downstream port under test. wIndex is 1-based on the wire.
    localparam int unsigned PORT_UT = 1;

    // Device address usbdc0_enum_stepC leaves USBDC0 at.
    localparam int unsigned DEV_ADDR = 2;

    // Standard GetDescriptor(Device) for the post-resume traffic check.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100; // type 1, index 0
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    // Keeps SOF_OFF away from an unsettled VIP link SM. Speed-neutral.
    // Note 25 section 5.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling for the DUT entering suspend, not a dwell. HS value:
    // the DUT suspend-detect path is ~300 us here against ~1200 us at FS.
    // Note 25 section 5.
    localparam realtime SUSPEND_DWELL = 1ms;

    // Timeout ceiling for the device to START signalling wakeup. Speed-neutral;
    // exceeding it is not an error here. Note 25 section 5.
    localparam realtime REMOTE_WAKEUP_WAIT_MAX = 500us;

    // Sampling step for the VIP status bit; must stay far below the ~3.07 ms K.
    localparam realtime REMOTE_WAKEUP_POLL_STEP = 100ns;

    // Ceiling for UTMI SuspendM to rise again. NOT "the resume finished" - see
    // note 25 section 5 before retargeting this wait.
    localparam realtime RESUME_WAIT_MAX = 500us;

    // How long the host VIP holds its own resume K before emitting the
    // terminating low-speed EOP, in ps, written to svt_usb_configuration::tdrsmdn.
    //
    // The host half must START within 1 ms of the device K and must be
    // CONTINUOUS with it (USB 2.0 section 7.1.7.7; see the header comment of
    // caliptra_ss_usb_device_wakeup_checker.sv). Only the terminating EOP may be
    // late: BUS_EVENT_SW_WAKEUP_3 has no timer and its single exit arc is an
    // SE0, so an EOP delivered early is simply useless while an EOP delivered
    // late still works. clear_suspend is therefore started immediately on the
    // checker event and the EOP is pushed out by sizing the host K instead of
    // by delaying the whole host resume.
    //
    // Sizing, measured from the START of the device K (the host K joins it about
    // K_MIN_HOLD = 20 us in, which is when the checker event fires):
    //   T_3ms (3.072 ms, BUS_EVENT_SW_WAKEUP_1)
    // + T_TxENDDELAY (30 us, BUS_EVENT_SW_WAKEUP_2)
    // + ~100 us margin
    // = 3.2 ms, so the EOP lands comfortably inside BUS_EVENT_SW_WAKEUP_3.
    // There is no risk in making this longer; without an SE0 the pie cannot
    // leave that state at all.
    //
    // The VIP consumes this value as the RESUMING -> SEND_EOR dwell of the host
    // link state machine (svt_usb_status: "transition to SEND_EOR on tdrsmdn
    // timer expire"), so it is exactly the host-K duration knob. Fallback if a
    // future VIP revision ignores a reconfigured value on the
    // USB_20_CLEAR_PORT_SUSPEND path: the host K stays at the VIP default
    // SVT_USB_TDRSMDN_NOM = 20 ms, which still starts promptly and still places
    // the EOP after SW_WAKEUP_3, so only simulated time would be at stake and
    // not correctness. Note 25 sections 3 and 5.
    localparam real HOST_RESUME_K_PS = 3_200_000_000.0; // 3.2 ms in ps

    // Settling time after clear_suspend returns, covering the host K itself plus
    // the pie walking out of SW_WAKEUP_3 into idle and the VIP link granting the
    // link to a queued transfer. Same value as FS now that the 3.072 ms is paid
    // after clear_suspend starts instead of before it, so net simulated time is
    // unchanged. Still well inside the firmware grace window
    // USB_POST_RESUME_GRACE_POLLS = 70000 (~5.6 ms). Note 25 section 5.
    localparam realtime POST_RESUME_SETTLE = 3.3ms;

    // Timeout for the post-resume hub GetPortStatus probe, in us, as expected by
    // wait_xfer_done. Short on purpose: the probe only has to answer whether the
    // host VIP transmits at all, and a dead host should not cost the full 2000 us
    // default twice. 200 us is many control-transfer durations at either speed.
    localparam int unsigned POST_RESUME_PROBE_TIMEOUT_US = 200;

    // Ceiling and step for the post-resume poll that waits for the VIP host
    // link to report ENABLED again. Modelled on the passing
    // caliptra_ss_usb_hs_dev_global_suspend_L2 sequence, which polls the same
    // way after its SOF restart. Without this poll the sequence can issue
    // control transfers while the VIP link is still SUSPENDED, and such a
    // transfer is a silent no-op: the VIP logs started and done at the same
    // timestamp and never fires NOTIFY_USB_TRANSFER_ENDED, so the only symptom
    // is a transfer timeout with no traffic on the wire. Note 24 section 10.
    localparam int unsigned ENABLED_POLL_MAX_US = 50000;
    localparam realtime     ENABLED_POLL_STEP   = 1us;



    // -------------------------------------------------------------------------
    // Sticky latches written by the forked sampler and read by the main flow.
    // Class properties, not locals: the sampler outlives the statement that
    // spawned it. Both are evidence for the log only, never a verdict.
    // Note 25 section 9.
    // -------------------------------------------------------------------------
    bit       device_wakeup_latched;
    realtime  device_wakeup_time;

    bit       vip_link_suspend_seen;
    realtime  vip_link_suspend_time;

    // The relaxed tinactivity installed by the test class, saved just before the
    // suspend window tightens it so it can be put back afterwards. A class
    // property for symmetry with the latches above; the tighten and the restore
    // are in different steps of body(). Note 24 section 10.
    real      tinactivity_relaxed_ps;

    // Simulation time at which the main flow learned the device half was under
    // way (step 6). Used only to log the host takeover latency, which must stay
    // below 1 ms; the checker back-dates its own wakeup_k_time by K_MIN_HOLD, so
    // the true latency from the first K bit is about 20 us larger than what is
    // printed here.
    realtime  device_k_seen_time;



    // -------------------------------------------------------------------------
    // Global uvm_event names shared with the testbench-scope checkers. These
    // strings are duplicated verbatim in caliptra_ss_usb_suspend_resume_checker
    // and caliptra_ss_usb_device_wakeup_checker, because a uvm_sequence cannot
    // reach into testbench scope and the checkers must not depend on UVM. Keep
    // both copies in sync.
    // -------------------------------------------------------------------------
    localparam string OBS_WINDOW_EVENT  = "usb_suspend_resume_obs_window_done";
    localparam string DUT_SUSPEND_EVENT = "usb_dut_suspend_seen";
    localparam string DUT_RESUME_EVENT  = "usb_dut_resume_seen";
    // Must not be triggered before enumeration; see note 25 section 2.
    localparam string ARM_EVENT         = "usb_suspend_stimulus_armed";
    localparam string DUT_WAKEUP_K_EVENT = "usb_dut_wakeup_k_seen";

    // Tightened tinactivity for the suspend window only, in ps. HS window is
    // only ~175 us wide (>125 us HS microframe, <~300 us DUT suspend-detect).
    // Measured inert in practice - do not debug it. Note 25 section 6.
    localparam real TINACTIVITY_SUSPEND_WINDOW_PS = 200_000_000.0; // 200 us in ps

    function new(string name = "caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        // Resolved up front: uvm_event_pool::get_global() creates the event on
        // first use, so resolving before any stimulus removes the race with the
        // checker triggering them.
        uvm_event dut_suspend_ev;
        uvm_event dut_resume_ev;
        uvm_event dut_wakeup_k_ev;
        uvm_event obs_window_ev;
        uvm_event arm_ev;

        dut_suspend_ev  = uvm_event_pool::get_global(DUT_SUSPEND_EVENT);
        dut_resume_ev   = uvm_event_pool::get_global(DUT_RESUME_EVENT);
        dut_wakeup_k_ev = uvm_event_pool::get_global(DUT_WAKEUP_K_EVENT);
        obs_window_ev   = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
        arm_ev          = uvm_event_pool::get_global(ARM_EVENT);

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        device_wakeup_latched = 1'b0;
        device_wakeup_time    = 0;
        vip_link_suspend_seen = 1'b0;
        vip_link_suspend_time = 0;
        device_k_seen_time    = 0;

        // Step 1: link first, then SOF. The suspend/resume checker arms on the
        // first SOF, so SOF must not start before the link is up.
        wait_for_link_enabled(shared_status, "HS host link");
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Step 2: hub-aware enumeration. Needed because step 9 addresses USBDC0
        // directly, which requires it to have an address first.
        hub_enum_stepA(host_agent_h, usb_cfg);
        // port_num by name: the positional parameters after usb_cfg are suffix
        // and no_queue_and_hold, so positional would bring up the wrong port.
        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_UT));
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info(MSG_ID, "Hub-aware enumeration done (hub at addr 1, USBDC0 at addr 2).", UVM_LOW)

        // Step 3: arm the DUT-side checkers before the suspend stimulus.
        arm_ev.trigger();
        `uvm_info(MSG_ID,
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to this stimulus.",
            UVM_LOW)

        // Step 4a: start the wakeup sampler BEFORE the stimulus; the device K is
        // a short pulse on the DUT's own schedule. Note 25 section 9.
        fork
            sample_device_remote_wakeup(shared_status);
        join_none

        // Step 4b-pre: tighten tinactivity only now, for the suspend window.
        // The relaxed enumeration value is set in the test class; the tight one
        // cannot be in force during enumeration. Note that usb_cfg here is the
        // agent's own configuration, on which tinactivity is a direct member -
        // usb_cfg.host_cfg does not compile. Note 25 section 6.
        //
        // The previous value is saved here and put back at the top of step 7:
        // it must NOT stay in force past the suspend window, because every idle
        // gap after the resume (the multi-millisecond host resume K and the
        // POST_RESUME_SETTLE that follows it above all) is longer than 200 us
        // and would drop the VIP link straight back into SUSPENDED, making all
        // post-resume traffic a silent no-op. Note 24 section 10.
        tinactivity_relaxed_ps = usb_cfg.tinactivity;
        usb_cfg.tinactivity    = TINACTIVITY_SUSPEND_WINDOW_PS;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf("tinactivity lowered to 200 us for the HS suspend window (enumeration ran with the relaxed value %0.0f ps, which is restored before the post-resume phase).",
                      tinactivity_relaxed_ps), UVM_LOW)

        // Step 4b: stop SOF to put the bus into global L2 suspend. The only
        // stimulus the host contributes; ending the suspend is the device's job.
        `uvm_info(MSG_ID, "Stopping SOF to suspend the bus...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end

        // Step 5: wait for the DUT itself to enter suspend. Gated on the DUT
        // event, never on the VIP link state. Timeout is not an error here -
        // CHK_SUSPEND_SEEN owns that verdict.
        //
        // The is_on() test is OUTSIDE the fork, and that placement is a fix for
        // a measured defect rather than style: inside the fork it would reach
        // "disable <sibling>" before the sibling was scheduled, which is a
        // no-op, and the sequence would pay the whole ceiling and print a
        // contradictory timeout message. "disable fork" is not usable instead.
        // Note 25 section 7.
        if (dut_suspend_ev.is_on()) begin
            `uvm_info(MSG_ID,
                $sformatf("DUT had already entered suspend (UTMI SuspendM low) before this wait was reached; not waiting. VIP link state is %0s (informational; not gated on).",
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_SUSPEND
                    dut_suspend_ev.wait_trigger();
                    `uvm_info(MSG_ID,
                        $sformatf("DUT entered suspend (UTMI SuspendM low). VIP link state is %0s (informational; not gated on).",
                                  shared_status.link_usb_20_state.name()), UVM_LOW)
                    disable SUSPEND_DWELL_TIMEOUT;
                end
                begin: SUSPEND_DWELL_TIMEOUT
                    #SUSPEND_DWELL;
                    `uvm_info(MSG_ID,
                        "Suspend dwell ceiling reached without the DUT entering suspend; continuing. The checker reports this as CHK_SUSPEND_SEEN.",
                        UVM_LOW)
                    disable WAIT_DUT_SUSPEND;
                end
            join_any
        end

        // Step 6: wait for the DEVICE half on the DUT's own pins. This wait
        // exists to ORDER the host half after the device half, which matters
        // both for the check (a host-first resume could hide a missing device K)
        // and for the protocol (the host must not take over a resume that has
        // not started). Timeout is not an error - CHK_DEVICE_WAKEUP_K owns it
        // and can additionally tell "never drove K" from "drove K too briefly".
        // Pre-fork is_on() test for the reason given at step 5; here the
        // already-fired path is the normal one.
        if (dut_wakeup_k_ev.is_on()) begin
            device_k_seen_time = $realtime;
            `uvm_info(MSG_ID,
                "Device half was already done before this wait was reached: the DUT is driving resume K upstream on the UTMI pins (see CHK_DEVICE_WAKEUP_K). Not waiting; proceeding to the host half.",
                UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_WAKEUP_K
                    dut_wakeup_k_ev.wait_trigger();
                    device_k_seen_time = $realtime;
                    `uvm_info(MSG_ID,
                        "Device half done: the DUT is driving resume K upstream on the UTMI pins (see CHK_DEVICE_WAKEUP_K). Driving the host half of the handshake now.",
                        UVM_LOW)
                    disable WAKEUP_K_TIMEOUT;
                end
                begin: WAKEUP_K_TIMEOUT
                    #REMOTE_WAKEUP_WAIT_MAX;
                    `uvm_info(MSG_ID,
                        "Device-wakeup-K ceiling reached without the DUT driving resume K; continuing so the observation window still closes. The checker reports this as CHK_DEVICE_WAKEUP_K.",
                        UVM_LOW)
                    disable WAIT_DUT_WAKEUP_K;
                end
            join_any
        end

        // Informational only, read after the wait so the log carries both views
        // side by side.
        report_vip_wakeup_view(shared_status);

        // Step 7: the HOST half. Ordering inside this step is protocol, not
        // preference (note 25 section 4):
        //   7-pre. configuration only, no delay: restore the relaxed
        //          tinactivity and program the host resume-K duration
        //          (tdrsmdn = HOST_RESUME_K_PS) in one reconfigure();
        //   7a.    clear_suspend starts the host resume K IMMEDIATELY, so the
        //          host K is continuous with the device K and begins well inside
        //          the 1 ms takeover window required by USB 2.0 section 7.1.7.7
        //          (see caliptra_ss_usb_device_wakeup_checker.sv). Only the
        //          terminating low-speed EOP has to be late, and it is pushed
        //          out by the configured host-K duration rather than by delaying
        //          the whole host resume. It cannot forge the verdict:
        //          CHK_DEVICE_WAKEUP_K needs the DUT's own TXValid;
        //   7b.    SOF restart, or the VIP link falls straight back into suspend
        //          on its inactivity timer.
        //
        // The tinactivity restore has to happen BEFORE clear_suspend: with the
        // 200 us suspend-window value still in force, the multi-millisecond
        // resume and post-resume settle gaps are each on their own enough to put
        // the VIP link back into SUSPENDED, and nothing later in step 7 brings
        // it out again. Note 24 section 10.
        usb_cfg.tinactivity = tinactivity_relaxed_ps;
        usb_cfg.tdrsmdn     = HOST_RESUME_K_PS;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf("tinactivity restored to %0.0f ps and the host resume-K duration (tdrsmdn) set to %0.0f ps before the host half; the suspend window is over and the remaining idle gaps are longer than the tightened tinactivity.",
                      tinactivity_relaxed_ps, HOST_RESUME_K_PS), UVM_LOW)

        `uvm_info(MSG_ID,
            $sformatf("Taking over the resume %0t after the device-wakeup-K event (the first K bit is about K_MIN_HOLD = 20 us earlier still). This latency must stay below 1 ms: the host K has to be continuous with the device K. Only the terminating EOP is deliberately late, carried out to %0.0f ps by tdrsmdn so it lands inside BUS_EVENT_SW_WAKEUP_3.",
                      $realtime - device_k_seen_time, HOST_RESUME_K_PS), UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence clr_susp;
            clr_susp = svt_usb_link_service_clear_suspend_sequence::type_id::create("clr_susp");
            clr_susp.start(p_sequencer.link_service_sequencer);
            `uvm_info(MSG_ID,
                "Host took over the resume and terminated it with the low-speed EOP, completing the device-initiated wakeup handshake.",
                UVM_LOW)
        end
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on2;
            sof_on2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on2");
            sof_on2.start(p_sequencer.prot_service_sequencer);
            `uvm_info(MSG_ID, "SOF restarted so the link stays out of suspend.", UVM_LOW)
        end

        // Step 7c: the VIP host link must report ENABLED again before any
        // transfer is issued. Same poll the passing
        // caliptra_ss_usb_hs_dev_global_suspend_L2 sequence does after its SOF
        // restart. A transfer issued on a link the VIP still holds in SUSPENDED
        // is dropped silently, so without this poll the only symptom is a
        // transfer timeout with nothing on the wire. Note 24 section 10.
        wait_for_vip_link_enabled(shared_status);

        // Step 8: wait for the DUT to leave suspend. The event is always already
        // on here by construction, because SuspendM rises on the raw wakeup
        // request, i.e. at the START of the device K, which is before step 7
        // runs at all. Pre-fork is_on() test for the reason given at step 5;
        // this is the wait where that defect was actually measured.
        // Note 25 section 7.
        if (dut_resume_ev.is_on()) begin
            `uvm_info(MSG_ID,
                $sformatf("DUT had already left suspend (UTMI SuspendM high again) before this wait was reached; not waiting. This is expected on a healthy run: the pie releases the PHY low-power request on the raw wakeup request, so SuspendM rises at the START of the device K, before step 6 even returns and well before the host half of step 7. VIP link state is %0s.",
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_RESUME
                    dut_resume_ev.wait_trigger();
                    `uvm_info(MSG_ID,
                        $sformatf("DUT left suspend (UTMI SuspendM high again). VIP link state is %0s.",
                                  shared_status.link_usb_20_state.name()), UVM_LOW)
                    disable RESUME_WAIT_TIMEOUT;
                end
                begin: RESUME_WAIT_TIMEOUT
                    #RESUME_WAIT_MAX;
                    `uvm_info(MSG_ID,
                        "Resume wait ceiling reached without the DUT leaving suspend; continuing. The checker reports this as CHK_RESUME_SEEN.",
                        UVM_LOW)
                    disable WAIT_DUT_RESUME;
                end
            join_any
        end

        // Step 9: the device must still be usable after waking itself. Gated on
        // the DUT-side K event, NOT on the VIP status latch - the latch is
        // expected to stay 0 even on a healthy DUT, so gating on it would
        // silently skip this check on every run. Note 25 section 4.
        if (dut_wakeup_k_ev.is_on()) begin
            #POST_RESUME_SETTLE;
            post_resume_traffic_check(host_agent_h, usb_cfg);
        end
        else begin
            `uvm_info(MSG_ID,
                "Skipping the post-resume traffic check: the DUT was never seen driving resume K, so there was no device-initiated resume for the device to survive. CHK_DEVICE_WAKEUP_K reports that failure.",
                UVM_LOW)
        end

        // Step 10: close the checker observation window. Mandatory, not
        // cosmetic: without this trigger the checkers never evaluate and the
        // test reports PASSED whatever the DUT did. Note 25 section 2.
        obs_window_ev.trigger();

        `uvm_info(MSG_ID,
            "caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Forked sampler: latch the VIP's view of the device remote wakeup the
    // moment it appears, plus whether the VIP link was ever seen SUSPENDED.
    // Records only; nothing here can fail the test. Terminates on the first
    // assertion; if the wakeup never happens the thread is still spinning when
    // body() returns, which is harmless. Note 25 section 9.
    // -------------------------------------------------------------------------
    task sample_device_remote_wakeup(svt_usb_status shared_status);
        forever begin
            if (!vip_link_suspend_seen
                && (shared_status.link_usb_20_state == svt_usb_types::SUSPENDED)) begin
                vip_link_suspend_seen = 1'b1;
                vip_link_suspend_time = $realtime;
            end
            if (shared_status.device_remote_wakeup_in_progress) begin
                device_wakeup_latched = 1'b1;
                device_wakeup_time    = $realtime;
                return;
            end
            #REMOTE_WAKEUP_POLL_STEP;
        end
    endtask

    // -------------------------------------------------------------------------
    // Report what the HOST VIP made of the wakeup. Informational only: the field
    // was measured staying 0 through a full, correct device K, so as a verdict
    // it produced a false FAIL on a working DUT. Every branch below is uvm_info
    // by construction. Note 25 section 2.
    // -------------------------------------------------------------------------
    task report_vip_wakeup_view(svt_usb_status shared_status);
        if (device_wakeup_latched) begin
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: device_remote_wakeup_in_progress asserted at %0t, so the VIP agreed a device remote wakeup was on the bus. Link state %0s.",
                          device_wakeup_time,
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else if (!vip_link_suspend_seen) begin
            // This branch prints on every run of both tests, including the
            // passing FS one, so on its own it is not a diagnosis.
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: device_remote_wakeup_in_progress never asserted, and the VIP link was never once seen in SUSPENDED (it is %0s now), so the VIP could not have reported a wakeup even from a perfectly correct device. This says nothing about the DUT; CHK_DEVICE_WAKEUP_K is the verdict.",
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: the VIP link did reach SUSPENDED (at %0t) but device_remote_wakeup_in_progress still never asserted. This is known VIP behaviour and is expected even on a working DUT; it is not a failure. Read CHK_DEVICE_WAKEUP_K for the actual verdict. Link state %0s.",
                          vip_link_suspend_time,
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
    endtask

    // -------------------------------------------------------------------------
    // Bounded poll for the VIP host link to report ENABLED again after the
    // resume. A control transfer issued while the VIP still holds the link in
    // SUSPENDED is dropped without any bus activity, and the VIP still logs it
    // as started and done, so the failure surfaces one timeout later as an
    // unexplained transfer timeout with nothing on the wire. Failing here
    // instead names the real cause. The passing
    // caliptra_ss_usb_hs_dev_global_suspend_L2 sequence polls the same way
    // after its SOF restart. Note 24 section 10.
    // -------------------------------------------------------------------------
    task wait_for_vip_link_enabled(svt_usb_status shared_status);
        int unsigned waited_us;
        waited_us = 0;
        while ((shared_status.link_usb_20_state != svt_usb_types::ENABLED)
               && (waited_us < ENABLED_POLL_MAX_US)) begin
            #ENABLED_POLL_STEP;
            waited_us++;
        end
        if (shared_status.link_usb_20_state != svt_usb_types::ENABLED) begin
            `uvm_error(MSG_ID,
                $sformatf("VIP host link is still %0s %0d us after the SOF restart, so it never came back to ENABLED after the device-initiated resume. Any transfer issued from here is dropped silently by the VIP, which is what the post-resume probe timeouts were really reporting.",
                          shared_status.link_usb_20_state.name(), waited_us))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("VIP host link is ENABLED again %0d us after the SOF restart; post-resume traffic can be issued.",
                          waited_us), UVM_LOW)
        end
    endtask

    // -------------------------------------------------------------------------
    // Post-resume traffic check. Re-anchors the VIP on USBDC0, issues a standard
    // GetDescriptor(Device) and requires a well-formed 18-byte device descriptor
    // back; both the length and bDescriptorType are checked, because a transfer
    // that ended but returned nothing must not count as the device working.
    //
    // A hub GetPortStatus probe runs first, after explicitly re-anchoring the
    // VIP onto the hub at address 1 (the anchor is left at 2 by
    // usbdc0_enum_stepC, so the re-anchor is required, not optional - see the
    // comment at the call below). It exists purely to classify the failure mode when the
    // GetDescriptor below times out, and it answers one question: does the host
    // VIP drive anything at all on the wire after the resume?
    //
    //   probe completes, GetDescriptor times out
    //     -> the host is transmitting and the hub is answering, so the fault is
    //        confined to the downstream port or to USBDC0 itself (for example
    //        the port was left disabled by the resume, or the device never
    //        re-synchronised to the bus speed in force after the wakeup).
    //   probe also times out
    //     -> the host VIP is inert. clear_suspend on a link the VIP still
    //        believes is ENABLED is a no-op, so no EOP, no SOF and no token
    //        ever reach the wire. This was measured on the failing HS run:
    //        after the device K ended there was exactly one transition on the
    //        UTMI pins (K to J) and then nothing for the remaining 2.2 ms,
    //        while the VIP still logged the transfer as started and done.
    //        Nothing downstream can complete in that state and no amount of
    //        DUT-side debug will help. Note 24 section 7.
    //
    // The probe is deliberately bounded well below the GetDescriptor timeout so
    // a dead host costs little simulated time, and it is left as a plain
    // wait_xfer_done so a timeout is visible in the log rather than swallowed.
    // -------------------------------------------------------------------------
    task post_resume_traffic_check(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        int unsigned nbytes;

        // Hub-class GetPortStatus on port 1, addressed to the hub at address 1.
        // do_control_xfer calls fix_anchors(0,0,0), which pins the VIP
        // dev_anchor to whatever remote_device_cfg[0].device_address currently
        // holds. It must therefore be set to 1 before this call, or the VIP
        // constraint (device_address == dev_anchor.device_address) contradicts
        // the WITH constraint (device_address == device_addr) and the solver
        // fails with a UVM_FATAL. usbdc0_enum_stepC leaves the anchor at 2
        // (USBDC0), so this re-anchor is mandatory here. See the constraint
        // note in caliptra_ss_usb_base_sequence.svh and note 24 section 9.6.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            "postWakeup: probing the hub with GetPortStatus(port 1) before the device GetDescriptor, to separate an inert host VIP from a downstream-only fault.",
            UVM_LOW)
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "PostWakeup_GetPortStatus_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "PostWakeup_GetPortStatus_Port1",
                       POST_RESUME_PROBE_TIMEOUT_US);

        usb_cfg.remote_device_cfg[0].device_address = 7'(DEV_ADDR);
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, BREQ_GET_DESCRIPTOR, DESC_DEVICE_W_VALUE,
            16'h0000, DEV_DESC_LEN, DEV_ADDR, "PostWakeup_GetDescriptor", usb_cfg);
        wait_xfer_done(host_agent_h, "PostWakeup_GetDescriptor");

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                "postWakeup: no control transfer item captured, so it could not be confirmed that the device still answers traffic after waking itself. This check must not be skipped silently.")
        end
        else begin
            nbytes = last_ctrl_seq_item.payload_byte_count();
            if (nbytes < DEV_DESC_LEN) begin
                `uvm_error(MSG_ID,
                    $sformatf("postWakeup: GetDescriptor(Device) to address %0d returned %0d payload bytes, expected %0d. The device is not answering correctly after its own remote wakeup.",
                              DEV_ADDR, nbytes, DEV_DESC_LEN))
            end
            else if (last_ctrl_seq_item.payload.data[1] !== DESC_TYPE_DEVICE) begin
                `uvm_error(MSG_ID,
                    $sformatf("postWakeup: GetDescriptor(Device) to address %0d returned bDescriptorType 0x%02x, expected 0x%02x. The device answered but the descriptor is not a device descriptor.",
                              DEV_ADDR, last_ctrl_seq_item.payload.data[1], DESC_TYPE_DEVICE))
            end
            else begin
                `uvm_info(MSG_ID,
                    $sformatf("postWakeup: device at address %0d returned a valid %0d-byte device descriptor after the device-initiated resume, so it is still able to receive and answer traffic.",
                              DEV_ADDR, nbytes), UVM_LOW)
            end
        end

        // Leave the anchor on the hub, where the hub-class helpers expect it.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
