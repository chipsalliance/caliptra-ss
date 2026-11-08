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
// The resume is STARTED by the device: MCU firmware calls
// usb_request_remote_wakeup() and USBDC0 drives resume K upstream. The DUT then
// parks in BUS_EVENT_SW_WAKEUP_3 until it sees an SE0, which the restarted SOF
// stream supplies as a frame EOP.
//
// Verdict: CHK_DEVICE_WAKEUP_K in caliptra_ss_usb_device_wakeup_checker (DUT
// TXValid + linestate=K), plus the post-resume GetDescriptor. Not any VIP
// status field.
//
// SCOPE LIMIT, measured and deliberate. This test proves that the DEVICE can
// initiate a wakeup and survives being woken. It does NOT prove USB 2.0
// section 7.1.7.7 host conformance, because the host half never actually drives
// a continuous resume K:
//
//   - clear_suspend carries prereq_link_20_state == SUSPEND, and the device's
//     own K pulls the VIP receiver out of SUSPENDED before the sequence can
//     react. CHK_DEVICE_WAKEUP_K needs K_MIN_HOLD = 20 us of sustained K first,
//     so the responder fires ~19 us after the first K bit, by which point the
//     precondition has already lapsed and the sequence is discarded in zero
//     simulation time. A takeover latency of 0 ns in the log is that discard.
//   - tdrsmdn, which would stretch a host resume, has MIN == NOM == 20 ms and
//     cannot be lowered (see the localparam note below).
//
// Making this conformant needs the takeover armed on a raw TXValid/linestate=K
// edge rather than on the debounced checker event, and the firmware grace
// window widened past the resulting ~21.5 ms EOP. See claude_md note 36 s9.
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence)

    string MSG_ID = "USB_HS_RW_FROMDEV_SEQ";

    // Hub downstream port under test. wIndex is 1-based on the wire.
    localparam int unsigned PORT_UT = 1;

    // Device address usbdc0_enum_stepC leaves USBDC0 at.
    localparam int unsigned DEV_ADDR = 2;

    // SET_FEATURE(DEVICE_REMOTE_WAKEUP) to the HUB at address 1. Mandatory in
    // hub mode: see claude_md/33_hub_remote_wakeup_enable_gate.md. 0x03 is
    // SET_FEATURE - 0x01 is CLEAR_FEATURE and would shut the gate again.
    localparam bit [7:0]  BREQ_SET_FEATURE          = 8'h03;
    localparam bit [15:0] FEAT_DEVICE_REMOTE_WAKEUP = 16'h0001;

    // Gap before a SETUP token so the firmware can re-arm EP0 OUT.
    localparam realtime CTRL_PACING_GAP = 10us;

    // Standard GetDescriptor(Device) for the post-resume traffic check.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100; // type 1, index 0
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    // Keeps SOF_OFF away from an unsettled VIP link SM. Speed-neutral.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling for the DUT entering suspend, not a dwell. The HS
    // suspend-detect path is ~300 us against ~1200 us at FS.
    localparam realtime SUSPEND_DWELL = 1ms;

    // Sampling step for the VIP status bit; must stay far below the ~3.07 ms K.
    localparam realtime REMOTE_WAKEUP_POLL_STEP = 100ns;

    // Ceiling for UTMI SuspendM to rise again. NOT "the resume finished".
    localparam realtime RESUME_WAIT_MAX = 500us;

    // svt_usb_configuration::tdrsmdn is deliberately NOT touched, here or in
    // the test class. SVT_USB_TDRSMDN_MIN == NOM == 20 ms
    // (svt_usb_timing_defines.svi:21-22) with no MAX, so any smaller value is
    // below the VIP floor and is rejected - which is why an earlier 3.2 ms
    // override measured 28.03 us on the wire. The untouched 20 ms default is
    // longer than the ~3.1 ms the DUT needs, so it already works.

    // Settling time for the VIP to grant the link to a queued transfer, counted
    // from the SOF restart. The device K is NOT covered here - step 7b-wait
    // below already blocks until the DUT stops driving K, so by this point the
    // DUT is in SW_WAKEUP_3 and SOF is supplying frame EOPs.
    //
    // Sizing: SOF restarts at ~4570 us, so the transfer is issued at ~5570 us,
    // inside the firmware grace window that closes at ~7178 us. Do not raise it
    // much past 2 ms or the GetDescriptor lands after the firmware has stopped
    // polling and fails for an unrelated reason.
    localparam realtime POST_RESUME_SETTLE = 1ms;

    // Ceiling for the DUT to stop driving its own resume K, polled before the
    // SOF restart. The device holds K for T_3ms (3.072 ms) and this is a
    // ceiling, not a dwell: the wait ends as soon as TXValid falls. 4 ms gives
    // ~0.9 ms of margin. Exceeding it means the DUT never stopped driving K,
    // which would be a genuine DUT fault and is reported as such.
    localparam int unsigned K_END_WAIT_MAX_US = 4000;

    // Guard after TXValid falls, so the DUT is definitely past SW_WAKEUP_2 and
    // has armed its ls_filt SE0 detector in SW_WAKEUP_3 before SOF resumes.
    // T_TxENDDELAY is 1800 pie_clk cycles = 30 us at 60 MHz; 50 us covers it.
    localparam realtime SW_WAKEUP_3_ARM_GUARD = 50us;

    // Ceiling for the DEVICE to start driving resume K after the firmware
    // request, polled in ENABLED_POLL_STEP units by the main flow.
    localparam int unsigned DEV_K_WAIT_MAX_US = 500;

    // Grace window for the forked responder to finish the host takeover.
    localparam int unsigned TAKEOVER_DONE_MAX_US = 200;

    // Ceiling for the VIP host link to report SUSPENDED after SOF-off. Without
    // a genuinely suspended VIP link, clear_suspend is discarded silently.
    localparam int unsigned SUSPEND_POLL_MAX_US = 10000;

    // Ceiling and step for the post-resume poll waiting for the VIP host link
    // to report ENABLED again. A transfer issued while the VIP still holds the
    // link SUSPENDED is a silent no-op, so skipping this poll turns the failure
    // into an unexplained transfer timeout with nothing on the wire.
    localparam int unsigned ENABLED_POLL_MAX_US = 50000;
    localparam realtime     ENABLED_POLL_STEP   = 1us;

    // UTMI TXValid, read for the step-7b ordering log below. This is the same
    // DUT output caliptra_ss_usb_device_wakeup_checker keys on, read here
    // directly because a uvm_sequence cannot reach testbench scope.
    localparam string TXVALID_PATH =
        "caliptra_ss_top_tb.cptra_ss_usb_utmi_txvalid_o";



    // -------------------------------------------------------------------------
    // Sticky latches written by the forked sampler and read by the main flow.
    // Class properties, not locals: the sampler outlives the statement that
    // spawned it. Both are evidence for the log only, never a verdict.
    // -------------------------------------------------------------------------
    bit       device_wakeup_latched;
    realtime  device_wakeup_time;

    bit       vip_link_suspend_seen;
    realtime  vip_link_suspend_time;

    // Written by the forked K-responder, polled by the main flow. Class
    // properties because the responder outlives the statement that spawned it.
    bit       device_k_seen;
    realtime  device_k_seen_time;
    bit       host_takeover_done;



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
    // Must not be triggered before enumeration.
    localparam string ARM_EVENT         = "usb_suspend_stimulus_armed";
    localparam string DUT_WAKEUP_K_EVENT = "usb_dut_wakeup_k_seen";

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
        device_k_seen         = 1'b0;
        device_k_seen_time    = 0;
        host_takeover_done    = 1'b0;

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

        // Step 2b: enable remote wakeup on the HUB at address 1. Mandatory:
        // hub_remotewakeup ANDs ep0_remote_wake_enabled(0), which only this
        // request sets, so without it the device request is discarded
        // silently. Must come after stepC because sync_busreset clears the bit.
        // The explicit re-anchor either side is the mechanism, not decoration:
        // do_control_xfer pins the VIP dev_anchor from usb_cfg and a mismatch
        // is an unsatisfiable randomization, not a misroute.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        #CTRL_PACING_GAP;
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (BREQ_SET_FEATURE),
            .wvalue               (FEAT_DEVICE_REMOTE_WAKEUP),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (1),
            .label                ("HubSetFeature_DeviceRemoteWakeup"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h),
                       .label("HubSetFeature_DeviceRemoteWakeup"));
        `uvm_info(MSG_ID,
            "SET_FEATURE(DEVICE_REMOTE_WAKEUP) completed to the hub at address 1; ep0_remote_wake_enabled(0) is now set and the compound can forward the device wakeup request upstream.",
            UVM_LOW)
        usb_cfg.remote_device_cfg[0].device_address = 7'(DEV_ADDR);
        host_agent_h.reconfigure(usb_cfg);
        #CTRL_PACING_GAP;

        // Step 3: arm the DUT-side checkers before the suspend stimulus.
        arm_ev.trigger();
        `uvm_info(MSG_ID,
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to this stimulus.",
            UVM_LOW)

        // Step 4a: start the wakeup sampler BEFORE the stimulus; the device K is
        // a short pulse on the DUT's own schedule.
        fork
            sample_device_remote_wakeup(shared_status);
        join_none

        // Step 4a2: fork the host K-responder BEFORE the suspend stimulus. It
        // is blocked on the DUT's own K event, so it answers within a delta of
        // the event rather than queueing behind the step 5 wait. Still purely
        // reactive: a DUT that never asks gets no host resume.
        fork
            begin: K_RESPONDER
                dut_wakeup_k_ev.wait_trigger();
                device_k_seen      = 1'b1;
                device_k_seen_time = $realtime;
                `uvm_info(MSG_ID,
                    "Device half done: the DUT drove resume K on its own UTMI TXValid (see CHK_DEVICE_WAKEUP_K). Answering immediately.",
                    UVM_LOW)

                // tdrsmdn is left at the VIP default on purpose; see the
                // localparam comment above for why it must not be lowered.
                //
                // clear_suspend returns well before the host resume K actually
                // ends, so the log line below records when the TAKEOVER was
                // ACCEPTED, not when the terminating SE0 reached the wire. The
                // SE0 lands later, inside BUS_EVENT_SW_WAKEUP_3.
                begin
                    svt_usb_link_service_clear_suspend_sequence clr_susp;
                    clr_susp = svt_usb_link_service_clear_suspend_sequence::type_id::create("clr_susp");
                    clr_susp.start(p_sequencer.link_service_sequencer);
                end

                host_takeover_done = 1'b1;
                `uvm_info(MSG_ID,
                    $sformatf("Host took over the resume and terminated it with the low-speed EOP %0t after the device-wakeup-K event. This latency must stay below the 1 ms takeover window of USB 2.0 section 7.1.7.7.",
                              $realtime - device_k_seen_time), UVM_LOW)
            end
        join_none

        // Step 4b: stop SOF to put the bus into global L2 suspend. The only
        // stimulus the host contributes; ending the suspend is the device's job.
        `uvm_info(MSG_ID, "Stopping SOF to suspend the bus...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end

        // Step 4c: the VIP host link must really reach SUSPENDED, or
        // clear_suspend is discarded on its prereq_link_20_state == SUSPEND
        // precondition and the host never drives the terminating EOP.
        wait_for_vip_link_suspended(shared_status);

        // Step 5: wait for the DUT itself to enter suspend. Gated on the DUT
        // event, never on the VIP link state. Timeout is not an error here -
        // CHK_SUSPEND_SEEN owns that verdict.
        //
        // The is_on() test must stay OUTSIDE the fork: inside, the
        // "disable <sibling>" would run before the sibling was scheduled and
        // be a no-op, costing the full ceiling plus a contradictory timeout
        // message. "disable fork" is not usable instead.
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

        // Step 6: observe the forked responder rather than re-waiting the event.
        // A second wait_trigger() on a one-shot event that has already fired
        // would block forever, so the flags it sets are polled instead.
        begin: OBSERVE_TAKEOVER
            int unsigned waited_us = 0;

            while (!device_k_seen && waited_us < DEV_K_WAIT_MAX_US) begin
                #ENABLED_POLL_STEP;
                waited_us++;
            end

            if (device_k_seen) begin
                waited_us = 0;
                while (!host_takeover_done && waited_us < TAKEOVER_DONE_MAX_US) begin
                    #ENABLED_POLL_STEP;
                    waited_us++;
                end
            end
        end

        // Informational only, read after the wait so the log carries both views
        // side by side.
        report_vip_wakeup_view(shared_status);

        // Step 7: classify the handshake. CHK_DEVICE_WAKEUP_K remains the
        // device-side verdict; these errors attribute the failure to a half.
        if (!device_k_seen) begin
            `uvm_error(MSG_ID,
                $sformatf("Device-initiated remote wakeup FAILED at the device half: the DUT never drove resume K within %0d us, so usbreg_remotewakeup was never acted on. Check, in order: that SET_FEATURE(DEVICE_REMOTE_WAKEUP) reached the HUB at address 1 (step 2b - without it ep0_remote_wake_enabled(0) gates the request off); that the firmware called usb_allow_clock_stop(); and that DEVCMDSTAT.DSUS was set when the wakeup write was issued. No host resume was driven, on purpose.",
                          DEV_K_WAIT_MAX_US))
        end
        else if (!host_takeover_done) begin
            `uvm_error(MSG_ID,
                $sformatf("The DUT requested wakeup at %0t (CHK_DEVICE_WAKEUP_K satisfied) but the host takeover did not complete within %0d us of being triggered. This is a HOST-side testbench issue, not a device failure: the device half already passed. Check whether the VIP link really reached SUSPENDED at step 4c, since clear_suspend is discarded on an ENABLED link.",
                          device_k_seen_time, TAKEOVER_DONE_MAX_US))
        end
        else begin
            `uvm_info(MSG_ID,
                "Device half and host takeover both complete; restarting SOF and confirming the device still answers traffic.",
                UVM_LOW)
        end

        // Step 7b: record the takeover ordering. INFORMATIONAL ONLY - do NOT
        // promote this to a uvm_error. An earlier revision did, and it was a
        // proven false failure; see claude_md note 36 s8/s9.
        //
        // TXValid still being high here is NORMAL on the L2 path: the device
        // holds K for the full T_3ms (3.072 ms), and clear_suspend returns long
        // before any host resume would end, so "takeover done" is not "EOP
        // already driven".
        if (device_k_seen && host_takeover_done && device_k_still_driving()) begin
            `uvm_info(MSG_ID,
                $sformatf("Takeover ordering: the DUT requested wakeup at %0t, the host takeover returned, and UTMI TXValid is still high - so the device is still mid-K. Expected on the L2 path; the SE0 that releases BUS_EVENT_SW_WAKEUP_3 arrives later, after the wait below.",
                          device_k_seen_time), UVM_LOW)
        end

        // Step 7b-wait: let the device FINISH driving its own resume K before
        // restarting SOF. This ordering is the whole fix, and it is load
        // bearing - do not move the SOF restart back above it.
        //
        // WHY. BUS_EVENT_SW_WAKEUP_3 leaves on exactly one condition,
        // ls_filt = LINESTATE_SE0, and has NO timeout arm (usb_pie.m.vhdl:1386).
        // An SE0 driven before the state is entered is therefore LOST, and the
        // DUT waits forever. Restarting SOF here instead of earlier means the
        // FS frame stream - every frame of which ends in an EOP, i.e. an SE0 -
        // is running while the detector is armed, so the DUT exits on the next
        // frame. No single pulse has to be placed precisely.
        //
        // Being LATE costs nothing, precisely because there is no timeout arm.
        // That is what makes this safe rather than another timing race.
        //
        // Measured 2026-11-06: with SOF restarted at ~1504 us, i.e. while the
        // device was still mid-K, the only SE0 on the bus was at 1495.8 us, the
        // state opened at 4569.7 us, and no further SE0 ever arrived - the DUT
        // parked and the GetDescriptor timed out at 12003 us.
        wait_for_device_k_end();

        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on2;
            sof_on2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on2");
            sof_on2.start(p_sequencer.prot_service_sequencer);
            `uvm_info(MSG_ID,
                "SOF restarted, now that the DUT has stopped driving K and is waiting in BUS_EVENT_SW_WAKEUP_3. Each restarted FS frame ends in an EOP (SE0), which is what releases that state.",
                UVM_LOW)
        end

        // Step 7c: the VIP host link must report ENABLED again before any
        // transfer is issued; a transfer on a link the VIP still holds in
        // SUSPENDED is dropped silently.
        wait_for_vip_link_enabled(shared_status);

        // Step 8: wait for the DUT to leave suspend. The event is always already
        // on here by construction, because SuspendM rises on the raw wakeup
        // request, i.e. at the START of the device K, which is before step 7
        // runs at all. Pre-fork is_on() test for the reason given at step 5.
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
        // silently skip this check on every run.
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
        // test reports PASSED whatever the DUT did.
        obs_window_ev.trigger();

        `uvm_info(MSG_ID,
            "caliptra_ss_usb_hs_host_remotewakeup_fromdevice_sequence complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Forked sampler: latch the VIP's view of the device remote wakeup the
    // moment it appears, plus whether the VIP link was ever seen SUSPENDED.
    // Records only; nothing here can fail the test. Terminates on the first
    // assertion; if the wakeup never happens the thread is still spinning when
    // body() returns, which is harmless.
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
    // Report what the HOST VIP made of the wakeup. Informational only: the
    // field was measured staying 0 through a full, correct device K, so as a
    // verdict it produced a false FAIL. Every branch below is uvm_info.
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
    // Is the DUT still driving its own resume K right now? Reads UTMI TXValid,
    // a DUT OUTPUT, so nothing the host or the VIP does can forge the answer.
    //
    // An unreadable path cannot establish that K has ended. Abort rather than
    // bypassing the ordering required by wait_for_device_k_end().
    // -------------------------------------------------------------------------
    function bit device_k_still_driving();
        logic [63:0] txvalid_val;
        if (!uvm_hdl_read(TXVALID_PATH, txvalid_val)) begin
            `uvm_fatal(MSG_ID,
                $sformatf("Cannot read %s; cannot safely restart SOF without observing the end of device K.",
                          TXVALID_PATH))
            return 1'b0;
        end
        return (txvalid_val[0] === 1'b1);
    endfunction

    // -------------------------------------------------------------------------
    // Bounded poll for the DUT to STOP driving its own resume K, then a short
    // guard so BUS_EVENT_SW_WAKEUP_3 is armed before the caller restarts SOF.
    //
    // Keys on UTMI TXValid, a DUT OUTPUT, so the host cannot forge the answer.
    // The timeout IS a verdict here, unlike the step-7b log: the device K is
    // self-terminating at T_3ms, so TXValid never falling means the DUT is
    // stuck driving K, which is a real fault and not a testbench artefact.
    // -------------------------------------------------------------------------
    task wait_for_device_k_end();
        int unsigned waited_us;
        waited_us = 0;
        while (device_k_still_driving() && (waited_us < K_END_WAIT_MAX_US)) begin
            #ENABLED_POLL_STEP;
            waited_us++;
        end
        if (device_k_still_driving()) begin
            `uvm_error(MSG_ID,
                $sformatf("UTMI TXValid is still high %0d us after the device wakeup K began, so the DUT never stopped driving resume K. It should self-terminate after T_3ms (3.072 ms) and move through SW_WAKEUP_2 into SW_WAKEUP_3. SOF is restarted anyway so the run completes, but the device cannot answer traffic while it is transmitting and the post-resume check below is expected to fail as a consequence.",
                          waited_us))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("DUT stopped driving resume K after %0d us (T_3ms is 3072 us). Waiting %0t for T_TxENDDELAY so BUS_EVENT_SW_WAKEUP_3 is armed, then SOF can supply the terminating SE0.",
                          waited_us, SW_WAKEUP_3_ARM_GUARD), UVM_LOW)
            #SW_WAKEUP_3_ARM_GUARD;
        end
    endtask

    // -------------------------------------------------------------------------
    // Bounded poll for the VIP host link to report SUSPENDED after SOF-off.
    // Load-bearing, not diagnostic: clear_suspend carries
    // prereq_link_20_state == SUSPEND, so on an ENABLED link it is discarded in
    // zero simulation time and the host never drives the terminating EOP.
    // -------------------------------------------------------------------------
    task wait_for_vip_link_suspended(svt_usb_status shared_status);
        int unsigned waited_us;
        waited_us = 0;
        while ((shared_status.link_usb_20_state != svt_usb_types::SUSPENDED)
               && (waited_us < SUSPEND_POLL_MAX_US)) begin
            #ENABLED_POLL_STEP;
            waited_us++;
        end
        if (shared_status.link_usb_20_state != svt_usb_types::SUSPENDED) begin
            `uvm_error(MSG_ID,
                $sformatf("VIP host link is still %0s %0d us after SOF-off, so it never declared SUSPENDED. clear_suspend requires that state and is discarded silently without it, so the host would never start its half of the resume at all - a takeover latency of 0 ns in the step-7 log is the signature of that discard. Check tinactivity against the idle gap between SOF-off and the device K.",
                          shared_status.link_usb_20_state.name(), waited_us))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("VIP host link reached SUSPENDED %0d us after SOF-off; the host half can take over a device-initiated resume.",
                          waited_us), UVM_LOW)
        end
    endtask

    // -------------------------------------------------------------------------
    // Bounded poll for the VIP host link to report ENABLED again after the
    // resume. A transfer issued while the VIP still holds the link SUSPENDED is
    // dropped with no bus activity yet still logged as started and done, so
    // failing here names the real cause instead of a later blind timeout.
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
    // -------------------------------------------------------------------------
    task post_resume_traffic_check(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        int unsigned nbytes;

        // do_control_xfer pins the VIP dev_anchor from usb_cfg, so the anchor
        // must agree with device_addr or randomization is unsatisfiable.
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
