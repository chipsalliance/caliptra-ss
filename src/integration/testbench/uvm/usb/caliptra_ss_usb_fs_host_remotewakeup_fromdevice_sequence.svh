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

`ifndef CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV

// =============================================================================
// Device-initiated remote wakeup, FULL SPEED, hub-composite IP.
//
// The resume is STARTED by the device: MCU firmware calls
// usb_request_remote_wakeup(), USBDC0 drives resume K upstream, and the host
// takes over and terminates it with a low-speed EOP.
//
// Verdict: CHK_DEVICE_WAKEUP_K in caliptra_ss_usb_device_wakeup_checker (DUT
// TXValid + linestate=K). Not any VIP status field.
// =============================================================================

class caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence)

    string MSG_ID = "USB_FS_RW_FROMDEV_SEQ";

    // Hub downstream port under test. wIndex is 1-based on the wire.
    localparam int unsigned PORT_UT = 1;

    // Device address usbdc0_enum_stepC leaves USBDC0 at.
    localparam int unsigned DEV_ADDR = 2;

    // Standard SET_FEATURE(DEVICE_REMOTE_WAKEUP) applied to the HUB at address 1
    // after enumeration. This is load-bearing, not politeness: the compound
    // gates the upstream wakeup request on ep0_remote_wake_enabled(0), which is
    // set ONLY by this request. Step 2b carries the full RTL derivation and the
    // evidence summary at the end of this file carries the measurement.
    // bRequest 0x03 is SET_FEATURE. Do NOT use 0x01 here - that is
    // CLEAR_FEATURE, which would drive ep0_remote_wake_enabled(0) to 0 and
    // reproduce the exact failure this step exists to fix. Cross-checked
    // against caliptra_ss_usb_get_status_sequence.svh:100.
    localparam bit [7:0]  BREQ_SET_FEATURE          = 8'h03;
    localparam bit [15:0] FEAT_DEVICE_REMOTE_WAKEUP = 16'h0001;

    // Pacing gap before a SETUP token: the firmware is still in the tail of the
    // preceding control transfer when wait_xfer_done() returns and has to re-arm
    // EP0 OUT before the next SETUP is driven. Same value and reason as
    // caliptra_ss_usb_get_status_sequence.svh:111.
    localparam realtime CTRL_PACING_GAP = 10us;

    // Standard GetDescriptor(Device) for the post-resume traffic check.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100; // type 1, index 0
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    // Keeps SOF_OFF away from an unsettled VIP link SM. Speed-neutral.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling for DUT suspend entry, not a dwell. FS entry was measured
    // at 1509 us after SOF-off, so this leaves ~490 us of margin; do not reduce.
    localparam realtime SUSPEND_DWELL = 2ms;

    // Ceiling for the device to START signalling wakeup. Exceeding it is not an
    // error here; CHK_DEVICE_WAKEUP_K owns that verdict.
    localparam realtime REMOTE_WAKEUP_WAIT_MAX = 500us;

    // Sampling step for the VIP status bit; must stay far below the ~3.07 ms K.
    localparam realtime REMOTE_WAKEUP_POLL_STEP = 100ns;

    // Ceiling for UTMI SuspendM to rise again. NOT "the resume finished".
    localparam realtime RESUME_WAIT_MAX = 500us;

    // Settling time after the host EOP. FS has no DEVICE_K_REMAINDER, so the
    // 3.072 ms of device K is paid here instead; do not reduce.
    localparam realtime POST_RESUME_SETTLE = 3.5ms;

    // -------------------------------------------------------------------------
    // Sticky latches written by the forked sampler and read by the main flow.
    // Class properties, not locals: the sampler outlives the statement that
    // spawned it. Evidence for the log only, never a verdict.
    // -------------------------------------------------------------------------
    bit       device_wakeup_latched;
    realtime  device_wakeup_time;

    bit       vip_link_suspend_seen;
    realtime  vip_link_suspend_time;

    // The relaxed tinactivity installed by the test class, saved just before the
    // suspend window tightens it and restored before the post-resume phase. A
    // class property and not a local because the tighten (step 4b-pre) and the
    // restore (step 7-pre) are in different steps of body(). Leaving the tight
    // value in force past the suspend window lets the VIP link slide back into
    // SUSPENDED during POST_RESUME_SETTLE, after which every transfer is a
    // silent no-op that the VIP logs as started and done without driving a bit.
    real      tinactivity_relaxed_ps;

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
    localparam string ARM_EVENT = "usb_suspend_stimulus_armed";
    localparam string DUT_WAKEUP_K_EVENT = "usb_dut_wakeup_k_seen";

    function new(string name = "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence");
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

        // Step 1: link first, then SOF. The suspend/resume checker arms on the
        // first SOF, so SOF must not start before the link is up.
        wait_for_link_enabled(shared_status, "FS host link");
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

        // Step 2b: enable remote wakeup on the HUB. This step is MANDATORY and
        // its absence was the measured cause of this test failing: see the
        // evidence summary at the end of this file.
        //
        // In hub mode the compound does not route the device's wakeup request
        // upstream directly. From
        // ip_xxx_3511_hs_mem_compound_structure.a.vhdl:2327-2334,
        //
        //   usbreg_remotewakeup <= hub_remotewakeup when hub_enable_q = '1'
        //                          else hub_port_remotewakeup(0);
        //   hub_remotewakeup    <= sync_suspend               and
        //                          ep0_remote_wake_enabled(0) and
        //                          (hub_epin_enable_buffer or
        //                           (hub_port_enable(0) and hub_port_remotewakeup(0)) or
        //                           (hub_port_enable(1) and hub_port_remotewakeup(1)));
        //
        // so with hub_enable_q = '1' the device request reaches the pie only
        // through ep0_remote_wake_enabled(0). That bit is set ONLY by
        // set_remote_wake_enabled in usb_ep0_handler.m.vhdl:405-407, which is
        // asserted only by a Standard SET_FEATURE to the device with wValue
        // bit 0 set, decoded at usb_ep0_handler.m.vhdl:334-337. The hub EP0 is
        // a hardware handler, so no firmware or SETUP-match change is needed -
        // the request simply has to be sent, and it has to be sent to the HUB
        // (device index 0), not to USBDC0.
        //
        // The anchor is at 2 on entry here because usbdc0_enum_stepC leaves it
        // there, so it must be moved to 1 first and moved back afterwards:
        // do_control_xfer() pins dev_anchor.device_address from usb_cfg and the
        // VIP then constrains device_address to equal it, so a mismatch is an
        // unsatisfiable randomization and a UVM_FATAL, not a silent misroute.
        // set_anchor_addr() is NOT a base-class helper - it is a task local to
        // caliptra_ss_usb_get_status_sequence. The two lines below are the
        // mechanism itself and must be issued in lockstep with every change of
        // target address.
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
            "SET_FEATURE(DEVICE_REMOTE_WAKEUP) sent to the hub at address 1, which sets ep0_remote_wake_enabled(0) and is what lets the compound forward the device wakeup request upstream in hub mode. Without it hub_remotewakeup is gated off and the pie never sees a request, no matter how many times the firmware asks.",
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

        // Step 4b-pre: tighten tinactivity only now, for the suspend window.
        // The relaxed enumeration value is set in the test class; the tight one
        // cannot be in force during enumeration. usb_cfg here is the agent's own
        // configuration, so tinactivity is a direct member (usb_cfg.host_cfg
        // does not compile).
        // The relaxed value is saved here and restored at step 7-pre; leaving
        // the tight one in force past the suspend window lets the VIP link
        // re-suspend during POST_RESUME_SETTLE and silently no-op step 9.
        tinactivity_relaxed_ps = usb_cfg.tinactivity;
        usb_cfg.tinactivity    = 900_000_000.0; // 0.9 ms in ps
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf("tinactivity lowered to 0.9 ms for the suspend window (enumeration ran with the relaxed value %0.0f ps, which is restored before the post-resume phase).",
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
        // The is_on() test must stay OUTSIDE the fork: inside, "disable
        // <sibling>" can run before the sibling is scheduled and becomes a
        // no-op, so the sequence pays the whole ceiling. "disable fork" is not
        // usable instead.
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

        // Step 6: wait for the DEVICE half on the DUT's own pins. Orders the
        // host half after the device half, which matters both for the check (a
        // host-first resume could hide a missing device K) and for the protocol.
        // Timeout is not an error - CHK_DEVICE_WAKEUP_K owns it. Pre-fork
        // is_on() test for the reason given at step 5; here the already-fired
        // path is the normal one.
        if (dut_wakeup_k_ev.is_on()) begin
            `uvm_info(MSG_ID,
                "Device half was already done before this wait was reached: the DUT is driving resume K upstream on the UTMI pins (see CHK_DEVICE_WAKEUP_K). Not waiting; proceeding to the host half.",
                UVM_LOW)
        end
        else begin
            fork
                begin: WAIT_DUT_WAKEUP_K
                    dut_wakeup_k_ev.wait_trigger();
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

        // Step 7: the HOST half. The ordering is protocol, not preference:
        //   7-pre. Configuration only, no delay: restore the relaxed
        //          tinactivity. The suspend window is over and every remaining
        //          idle gap (notably POST_RESUME_SETTLE) is longer than the
        //          tightened value, so leaving it in force lets the VIP link
        //          slide back into SUSPENDED and turns step 9 into a silent
        //          no-op that is logged as started and done without a bit
        //          being driven.
        //   7a.    clear_suspend drives the host resume K and terminates it
        //          with the low-speed EOP the pie waits for in
        //          BUS_EVENT_SW_WAKEUP_3, which has no other exit arc. It
        //          cannot forge the verdict: CHK_DEVICE_WAKEUP_K needs the
        //          DUT's own TXValid.
        //   7b.    SOF restart, or the VIP link falls straight back into
        //          suspend.
        //
        // On the EOP placement at full speed: every FS packet ends in an SE0,
        // so the restarted SOF stream keeps supplying SE0s and one lands while
        // the pie is in BUS_EVENT_SW_WAKEUP_3. tdrsmdn is deliberately NOT set
        // here. The HS twin needs it because high speed has no SE0s in normal
        // traffic at all, so nothing would ever rescue a short host K; at FS
        // the SOF stream does that job. Setting tdrsmdn here would only add
        // simulated time. An earlier revision of this comment described the FS
        // behaviour as an accident to be replaced by the HS ordering - that was
        // written before the failure was measured, and the measurement showed
        // the host half was never the problem. See the evidence summary at the
        // end of this file.
        usb_cfg.tinactivity = tinactivity_relaxed_ps;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf("tinactivity restored to %0.0f ps before the host half; the suspend window is over and the remaining idle gaps are longer than the tightened value.",
                      tinactivity_relaxed_ps), UVM_LOW)
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


        // Step 8: wait for the DUT to leave suspend. Gated on the DUT event,
        // not the VIP link state. Pre-fork is_on() test for the reason given at
        // step 5; a measured run had CHK_RESUME_SEEN fire at 3.0167 ms while
        // this wait was not reached until 3.4293 ms.
        if (dut_resume_ev.is_on()) begin
            `uvm_info(MSG_ID,
                $sformatf("DUT had already left suspend (UTMI SuspendM high again) before this wait was reached; not waiting. This is expected on a healthy run: the pie releases the PHY low-power request on the raw wakeup request, so SuspendM rises at the start of the device K. VIP link state is %0s.",
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


        // Step 10: close the checker observation window. Mandatory: without
        // this trigger the checkers never evaluate and the test reports PASSED
        // whatever the DUT did.
        obs_window_ev.trigger();

        `uvm_info(MSG_ID,
            "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence complete.", UVM_LOW)
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
    // Report what the HOST VIP made of the wakeup. Informational only: the field
    // was measured staying 0 through a full, correct device K, so as a verdict
    // it produced a false FAIL on a working DUT. Every branch below is uvm_info
    // by construction.
    // -------------------------------------------------------------------------
    task report_vip_wakeup_view(svt_usb_status shared_status);
        if (device_wakeup_latched) begin
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: device_remote_wakeup_in_progress asserted at %0t, so the VIP agreed a device remote wakeup was on the bus. Link state %0s.",
                          device_wakeup_time,
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else if (!vip_link_suspend_seen) begin
            // This branch prints on every run of both tests, including this
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
    // Post-resume traffic check. Re-anchors the VIP on USBDC0, issues a standard
    // GetDescriptor(Device) and requires a well-formed 18-byte device descriptor
    // back; both the length and bDescriptorType are checked, because a transfer
    // that ended but returned nothing must not count as the device working.
    // -------------------------------------------------------------------------
    task post_resume_traffic_check(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        int unsigned nbytes;

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

// =============================================================================
// EVIDENCE SUMMARY: why step 2b exists
//
// Measured from the FSDB of a failing run of this test, over the window
// 2600-3350 us. Signal paths are under
// /caliptra_ss_top_tb/caliptra_ss_dut/usb_core_i/u_hub_compound/.
// Reproduce non-interactively with fsdb2vcd -bt/-et and -s <path>; note the
// emitted VCD timescale is 10 fs, so divide raw timestamps by 100000 to get ns.
// BUS_EVENT_STATE_R is a VHDL enum and CANNOT be converted to VCD - the pin and
// handshake signals below are what pin the state down instead.
//
//   Firmware behaviour (from mcu_console.log): usb_request_remote_wakeup() was
//   issued three times, at 2764 us, 3047 us and 3326 us, each write and
//   read-back byte-identical (wrote 0x12414C82, read back 0x10434C82). The
//   read-back decodes to DSUS=1, FORCE_NEEDCLK=0, SPEED=01 (FS), DCON=1,
//   VBUS_DEBOUNCED=1 - exactly the state the IP requires for a wakeup. Three
//   identical ignored attempts 280 us apart is not a race; the firmware is
//   correct and is exonerated.
//
//   | Signal                    | Measured                                   |
//   | ------------------------- | ------------------------------------------ |
//   | PIE_SUSPEND               | 1 from 2631.402 us (pie IS in suspend)     |
//   | REG_DEV_SUSPEND           | 1 from 2631.424 us                         |
//   | SYNC_SUSPEND              | 1 from 2631.424 us                         |
//   | HUB_ENABLE_Q              | 1 for the whole run (hub mode)             |
//   | HUB_PORT_ENABLE(0)        | 1 for the whole run                        |
//   | HUB_PORT_REMOTEWAKEUP(0)  | 1 from 2761.774 us, stays 1                |
//   | EP0_REMOTE_WAKE_ENABLED(0)| 0 for the ENTIRE run                       |
//   | HUB_REMOTEWAKEUP          | 0 for the ENTIRE run                       |
//   | USBREG_REMOTEWAKEUP       | 0 for the ENTIRE run                       |
//   | cptra_ss_usb_utmi_txvalid_o | 0 for the ENTIRE window (no K ever driven)|
//
// So the device raised its request correctly and the pie was sitting in exactly
// the state that would consume it, but ep0_remote_wake_enabled(0) = 0 gated
// hub_remotewakeup off, the request never reached the pie, and no resume K was
// ever driven. Every other term of the hub_remotewakeup AND at
// ip_xxx_3511_hs_mem_compound_structure.a.vhdl:2330-2334 was satisfied; that
// one bit was the whole failure.
//
// Three hypotheses were tested and REFUTED by this data. They are recorded so
// they are not re-proposed:
//
//   1. "Raise the sequence timeout ceilings to 4-12 ms." Refuted: the
//      device-wakeup-K ceiling expired at 3135669.170 ns and CHK_RESUME_SEEN
//      fired 6.664 ns later at 3135675.834 ns - that resume was the host's own
//      clear_suspend at step 7, not the device. No ceiling was ever short.
//   2. "HUB_CTRL.PLL_ON is being cleared." Refuted: HUB_CTRL reads 0x10610881
//      identically before and after usb_allow_clock_stop(); bit 9 is never set,
//      so the clear is a no-op.
//   3. "The pie needs a longer dwell in BUS_EVENT_HOST_RESUME, which the VIP
//      must prolong via tdrsmdn." Refuted: BUS_EVENT_HOST_RESUME is on the
//      HOST-initiated resume path. PIE_SUSPEND = 1 throughout, so the pie was
//      in BUS_EVENT_SUSPEND, never in BUS_EVENT_HOST_RESUME, and no amount of
//      tdrsmdn would have helped. tdrsmdn remains correct and necessary for the
//      HS twin for the unrelated reason given at step 7.
//
// A fourth claim, an RTL wiring defect in the line-2327 mux itself, was also
// considered and is NOT supported: the mux and the OR term that feeds it are
// both correct. hub_port_remotewakeup(0) is present in the OR exactly as it
// should be. The missing SET_FEATURE was a testbench omission, not an RTL bug.
// =============================================================================

`endif // CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
