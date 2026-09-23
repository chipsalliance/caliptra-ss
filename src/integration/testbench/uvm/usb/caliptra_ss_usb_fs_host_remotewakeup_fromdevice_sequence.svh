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
// Device-initiated remote wakeup, full speed, hub-composite IP.
//
// What is different about this test, and why it was rewritten
// -----------------------------------------------------------
// Every other suspend test in this directory ends the suspend from the HOST
// side: the *_global_suspend_L2 family stops SOF and then drives K with
// svt_usb_link_service_clear_suspend_sequence. Here the DEVICE must end the
// suspend: the MCU firmware calls usb_request_remote_wakeup(), which makes
// USBDC0 drive resume K upstream, and this sequence must prove that the host
// actually saw that K on the bus.
//
// The original version of this file did not prove anything. Its flow was
//   suspend -> #5us -> svt_usb_protocol_service_20_resume_sequence
// with a comment claiming "host detects device K resume and responds". The wait
// was a fixed delay and the host resume was unconditional, so the observed
// result was byte-for-byte identical whether or not the device ever drove K,
// and the file contained no uvm_error at all. It also extended plain
// uvm_sequence and hand-rolled its own objections and agent casts instead of
// using caliptra_ss_usb_base_sequence. It has been rewritten on the
// caliptra_ss_usb_fs_dev_global_suspend_L2_sequence pattern.
//
// The check that makes this a remote-wakeup test
// ---------------------------------------------
// The verdict lives OUTSIDE this sequence, in
// caliptra_ss_usb_device_wakeup_checker (CHK_DEVICE_WAKEUP_K), which watches the
// DUT drive resume K on its own UTMI pins: TXValid asserted by the DUT together
// with linestate = K, held for a sustained minimum. TXValid is a DUT output, so
// nothing the host or the VIP does can satisfy that check - which is exactly the
// property the old version of this file was missing.
//
// This sequence's only job with respect to the check is to (a) arm it before the
// stimulus, (b) wait for its progress event usb_dut_wakeup_k_seen before driving
// the host half, and (c) close the observation window at the end.
//
// Why the VIP field is no longer the verdict
// ------------------------------------------
// svt_usb_status::device_remote_wakeup_in_progress is documented as "Indicates
// whether Device is signaling Remotewakeup on the Bus", and an earlier revision
// of this file used it as the pass/fail condition. It was then measured staying
// 0 through a full, correct, 3.089 ms device K: see
// docs/usb_remote_wakeup_selfclear_race_report.md sections 2A.4 and 7.4. The
// most probable reason is that the VIP only latches it once it has seen a
// COMPLETE device resume, including the host takeover it expects to perform
// itself, so the device half alone can never satisfy it. It is still sampled
// here, but purely as evidence for the log; it can no longer fail the test.
//
// Why the host resume IS driven now
// ---------------------------------
// The previous revision deliberately omitted
// svt_usb_link_service_clear_suspend_sequence, on the grounds that a host-driven
// K would end the suspend whether or not the device ever woke. That reasoning
// was correct while the verdict was a bus-level observable, and is obsolete now
// that the verdict is a DUT output: a host K does not make the DUT assert
// TXValid, so it cannot forge CHK_DEVICE_WAKEUP_K.
//
// Driving it is not optional either. Remote wakeup is device-initiated and
// HOST-COMPLETED (USB 2.0 section 7.1.7.7): the host must take over the resume
// within 1 ms of the device K and terminate it with a low-speed EOP, i.e. an
// SE0. usb_pie.m.vhdl BUS_EVENT_SW_WAKEUP_3 waits for that SE0 with no timer and
// no other exit arc, so a device left to itself parks there forever and never
// returns to BUS_EVENT_FS_IDLE - it can never answer the post-resume traffic
// check. That is why the host half is driven, and why it is driven only AFTER
// usb_dut_wakeup_k_seen has fired.

//
// Why the wakeup watcher is forked, and why the VIP link state is not a gate
// -------------------------------------------------------------------------
// An earlier revision of this sequence polled the conditions strictly in
// order: VIP link SUSPENDED, then usb_dut_suspend_seen, then
// device_remote_wakeup_in_progress. That ordering cannot work here, because
// the three actors run on unrelated timers:
//
//   - the VIP host link declares SUSPENDED only after tinactivity, which the
//     FS suspend tests set in the hundreds of microseconds to milliseconds;
//   - the DUT suspends on its own T_SUSPEND_DET. At FULL SPEED with
//     G_SIM_CHIRP_TIMERS=1 (how caliptra_ss_top_tb elaborates the DUT) that is
//     T_SUSPEND_DET_SIM_FS = 1100 us (usb_pie.m.vhdl:508). The 200 us figure
//     quoted in earlier revisions of this file was the HS constant
//     T_SUSPEND_DET_SIM_HS and does not apply to this test;
//   - the firmware then arms the wakeup a fixed number of DEVCMDSTAT polls
//     after it sees DSUS, and the resulting upstream K is a short pulse.
//
// There is a second, harder ordering constraint that follows from this. The VIP
// only interprets an upstream K as a remote wakeup while its own link is
// suspended, so tinactivity must expire BEFORE the DUT's suspend-detect timer,
// not after. That is a property of the test configuration, not of this
// sequence; see the tinactivity comment in the test class for the measured
// numbers and the window it has to sit in.

//
// Measured on the first run of this test: the DUT reported DSUS at 2.92 ms and
// the firmware drove the wakeup at 3.02 ms, while the sequence was still
// sitting in the VIP-SUSPENDED poll loop. The K pulse was long over by the
// time the sampler started, so the sequence reported a wakeup failure that had
// not happened, and it then spent every remaining timeout ceiling in simulated
// time to reach that wrong conclusion - hours of wall clock on this testbench,
// all after the MCU had already halted.
//
// Two rules follow, and both are load-bearing:
//   - The wakeup sampler is forked off BEFORE the suspend stimulus and latches
//     its result, so the pulse is caught whenever it happens.
//   - Progress is gated on the DUT event usb_dut_suspend_seen, never on the VIP
//     link state. The VIP state is still logged, but only as information;
//     making it a gate reintroduces the stall described above.
//
// Flow:
//   1. Wait for the FS host link to reach ENABLED, then start SOF.
//   2. Settle, then hub-aware enumeration (steps A + B + C) so the hub is at
//      address 1 and USBDC0 at address 2. This is needed because step 9
//      addresses USBDC0 directly for the post-resume traffic check.
//   3. Arm the DUT-side checkers (suspend/resume AND device-wakeup) before any
//      suspend stimulus. Both share the same arm event.
//   4. Fork the informational VIP-side wakeup sampler, then stop SOF to drive
//      the bus into global (L2) suspend.
//   5. Wait for the DUT to enter suspend (uvm_event usb_dut_suspend_seen).
//   6. Wait for the DEVICE half: uvm_event usb_dut_wakeup_k_seen, triggered by
//      caliptra_ss_usb_device_wakeup_checker once the DUT has held TXValid with
//      linestate=K for its minimum. No error is raised here on timeout - the
//      checker owns that verdict as CHK_DEVICE_WAKEUP_K.
//   7. Drive the HOST half of the handshake, in this order and only after
//      step 6: svt_usb_link_service_clear_suspend_sequence (host takes over the
//      resume and terminates it with the low-speed EOP the pie is waiting for in
//      BUS_EVENT_SW_WAKEUP_3), then restart SOF so the VIP link does not fall
//      straight back into suspend.
//   8. Wait for the DUT to leave suspend (uvm_event usb_dut_resume_seen), then
//      log the VIP link state for information.
//   9. Post-resume traffic check: GetDescriptor(Device) to USBDC0 must return a
//      well-formed 18-byte device descriptor.
//  10. Close the observation window (mandatory: without this trigger neither
//      checker evaluates, so CHK_SUSPEND_SEEN, CHK_RESUME_SEEN and
//      CHK_DEVICE_WAKEUP_K would all silently never run).

//
// Firmware coupling. caliptra_ss_usb_fs_host_remotewakeup_fromdevice.c must
// call usb_allow_clock_stop() after enumeration, or FORCE_NEEDCLK holds
// usbreg_pll_on high, utmi_suspendm never falls, the controller never reports
// DSUS, and there is no suspended state from which a wakeup can be requested.
// It must also keep serving EP0 for a grace window past the resume so step 9
// has someone to talk to.
// =============================================================================

class caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence)

    string MSG_ID = "USB_FS_RW_FROMDEV_SEQ";

    // Downstream port under test. wIndex is 1-based on the wire; the RTL forms
    // var_port := wIndex - 1, so wIndex 1 is USBDC0 on hub_port_*(0).
    localparam int unsigned PORT_UT = 1;

    // Device address usbdc0_enum_stepC leaves USBDC0 at.
    localparam int unsigned DEV_ADDR = 2;

    // Standard GetDescriptor(Device) for the post-resume traffic check.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100; // type 1, index 0
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    // Empirical margin. Guards a real failure mode: driving SOF_OFF while the
    // VIP link SM is still walking TRANSMIT -> ENABLED makes the link go
    // DISCONNECTED and starts an unintended second bus-reset cycle.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Timeout ceiling for the DUT entering suspend, not a dwell: the wait ends
    // on usb_dut_suspend_seen. At full speed with G_SIM_CHIRP_TIMERS=1 (how
    // caliptra_ss_top_tb elaborates the DUT) T_SUSPEND_DET_FS is 1100 us and
    // the DUT was measured entering suspend 1509 us after SOF-off, so 2 ms
    // leaves only about 490 us of margin. Do not reduce this. Against a
    // G_SIM_CHIRP_TIMERS=0 build the spec value is 3.072 ms and this ceiling
    // would have to be raised above it first.
    localparam realtime SUSPEND_DWELL = 2ms;


    // Timeout ceiling for the DEVICE to start signaling remote wakeup, measured
    // from the moment the DUT was seen to enter suspend. This bounds the wait on
    // usb_dut_wakeup_k_seen in step 6.
    //
    // Sizing: the firmware waits USB_WAKEUP_ARM_DELAY_POLLS (~80 us of polling)
    // after it observes DSUS before it issues the request, and its view of
    // suspend arrives on its own DEVCMDSTAT polling cadence rather than
    // instantly, so the ceiling has to cover both, plus the pie state machine
    // walking into BUS_EVENT_SW_WAKEUP_1, plus the checker's own K_MIN_HOLD
    // (20 us) before it triggers. 500 us is comfortably above the ~95 us
    // measured between DSUS and the wakeup write plus that hold.
    //
    // Exceeding this ceiling is NOT reported as an error here. The verdict
    // belongs to caliptra_ss_usb_device_wakeup_checker's CHK_DEVICE_WAKEUP_K,
    // which can additionally distinguish "never drove K" from "drove K too
    // briefly" - a distinction this sequence cannot make and which points at
    // different defects. Raising an error here as well would double-report one
    // failure with the less informative of the two messages.
    localparam realtime REMOTE_WAKEUP_WAIT_MAX = 500us;


    // Sampling step for device_remote_wakeup_in_progress and for polling the
    // latch. The VIP field is a status bit, not an event, so it has to be
    // sampled; the step must be well below the duration of the upstream K so
    // the pulse cannot fall between two samples.
    localparam realtime REMOTE_WAKEUP_POLL_STEP = 100ns;

    // Timeout ceiling for UTMI SuspendM to go high again, which is what the
    // step 8 wait observes and all it observes.
    //
    // Read the name with care. This is NOT "the resume finished". The pie
    // releases the PHY low-power request on the RAW wakeup request
    // (clear_ulpi_req_low_power_mode, usb_pie.m.vhdl:4629-4635), so SuspendM
    // rises before any bus activity at all - measured rising 2.8 us BEFORE the
    // firmware's own request print. 500 us is therefore generous for what it
    // actually waits on, and would be far too short for a genuine
    // end-of-resume, which needs T_3ms + T_TxENDDELAY plus the host EOP, i.e.
    // over 3.2 ms. Anyone retargeting this wait must raise the ceiling with it.
    // The real end-of-resume wait in this sequence is POST_RESUME_SETTLE, sized
    // exactly that way. See docs/usb_remote_wakeup_selfclear_race_report.md
    // sections 2A, 3 and 7.3.
    localparam realtime RESUME_WAIT_MAX = 500us;


    // Settling time after the resume observation before traffic is sent.
    //
    // Sized against the RTL, not chosen empirically. The device drives resume K
    // for the whole of BUS_EVENT_SW_WAKEUP_1, whose only exit is
    // timer_bus_event = T_3ms = 184320 pie_clk cycles (usb_pie.m.vhdl:477 and
    // 1659-1663). T_3ms has NO _SIM variant - only T_TUCH, T_CHIRP_DELAY,
    // T_TWTFS, T_TWTRSTHS and T_SUSPEND_DET are scaled by G_SIM_CHIRP_TIMERS -
    // so simulation pays the full 3.072 ms at 60 MHz. After that comes
    // T_TxENDDELAY (1800 cycles = 30 us, line 553) in BUS_EVENT_SW_WAKEUP_2 and
    // then the host low-speed EOP in BUS_EVENT_SW_WAKEUP_3 before the device
    // returns to BUS_EVENT_FS_IDLE and can answer a transfer.
    //
    // The previous value of 200 us was measured to inject the GetDescriptor
    // while the pie was still sitting in BUS_EVENT_SW_WAKEUP_1 driving K, which
    // the device cannot answer. 3.5 ms covers 3.072 ms of K plus TxEndDelay plus
    // EOP with margin. Do not reduce it without re-reading those RTL lines.
    localparam realtime POST_RESUME_SETTLE = 3.5ms;

    // -------------------------------------------------------------------------
    // Sticky latch written by the forked sampler and read by the main flow.
    // A class property rather than a local variable because the sampler runs in
    // a thread that outlives the statement that spawned it.
    // -------------------------------------------------------------------------
    bit       device_wakeup_latched;
    realtime  device_wakeup_time;

    // Second sticky latch, recorded by the same sampler: was the VIP host link
    // ever observed in svt_usb_types::SUSPENDED. This is not a check, it is
    // evidence for the failure message. The VIP only interprets an upstream K
    // as a remote wakeup while its own link is suspended, so if the wakeup was
    // never latched AND the link was never seen suspended, the fault is the
    // tinactivity ordering in the test class and not the DUT. Without this flag
    // the timeout message cannot tell those two cases apart, and a testbench
    // configuration fault gets filed as a DUT defect.
    bit       vip_link_suspend_seen;
    realtime  vip_link_suspend_time;

    // -------------------------------------------------------------------------
    // Global uvm_event names shared with caliptra_ss_usb_suspend_resume_checker.
    // These strings are the only coupling between this sequence and the
    // testbench-scope checker module and are duplicated verbatim there, because
    // a uvm_sequence cannot reach into testbench scope and the checker must not
    // depend on the UVM package. Keep both copies in sync.
    // -------------------------------------------------------------------------
    localparam string OBS_WINDOW_EVENT  = "usb_suspend_resume_obs_window_done";
    localparam string DUT_SUSPEND_EVENT = "usb_dut_suspend_seen";
    localparam string DUT_RESUME_EVENT  = "usb_dut_resume_seen";
    // Must not be triggered before enumeration: out of reset the DUT holds
    // SuspendM low by design and it rises again inside boot_usb_core_fs, and a
    // checker watching from time zero latches that boot-time low-then-high as a
    // complete suspend/resume cycle (a false PASS). It is triggered before the
    // suspend stimulus rather than being tied to any link-state milestone,
    // because the DUT reacts on its own T_SUSPEND_DET timer and the checker has
    // to be watching before either that timer or the VIP's tinactivity expires.
    localparam string ARM_EVENT = "usb_suspend_stimulus_armed";

    // Progress event from caliptra_ss_usb_device_wakeup_checker: fired the
    // moment the DUT has held UTMI TXValid with linestate=K for K_MIN_HOLD. This
    // is the cue that the device half of the handshake is done and that the host
    // half may now be driven. Same duplication rule as the strings above: the
    // literal also appears in caliptra_ss_usb_device_wakeup_checker.sv, keep
    // both copies in sync.
    localparam string DUT_WAKEUP_K_EVENT = "usb_dut_wakeup_k_seen";


    function new(string name = "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        // Resolved up front: uvm_event_pool::get_global() creates the event on
        // first use, so resolving the DUT-reaction events before any stimulus
        // removes the race with the checker triggering them.
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

        // Step 1: link first, then SOF. This ordering is the reverse of most
        // USB tests here and is deliberate: the suspend/resume checker arms on
        // the first SOF, so SOF must not start before the link is up.
        wait_for_link_enabled(shared_status, "FS host link");
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Step 2: hub-aware enumeration. Needed here (the global_suspend_L2
        // sequence does not do it) because step 9 addresses USBDC0 directly,
        // which requires it to have been given an address first.
        hub_enum_stepA(host_agent_h, usb_cfg);
        // port_num is passed by name: the positional parameters of
        // hub_port_bringup_stepB after usb_cfg are suffix and
        // no_queue_and_hold, so passing PORT_UT positionally would land on the
        // wrong argument and silently bring up the default port.
        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_UT));
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info(MSG_ID, "Hub-aware enumeration done (hub at addr 1, USBDC0 at addr 2).", UVM_LOW)

        // Step 3: arm the DUT-side checker before the suspend stimulus. See
        // ARM_EVENT above for why this point and not later.
        arm_ev.trigger();
        `uvm_info(MSG_ID,
            "Armed DUT-side suspend/resume checker; SuspendM activity from here on is attributable to this stimulus.",
            UVM_LOW)

        // Step 4a: start the wakeup sampler BEFORE the stimulus. The device K
        // is a short pulse that the DUT drives on its own schedule, so anything
        // that starts sampling for it only after the other waits have completed
        // can miss it entirely. See the header note.
        fork
            sample_device_remote_wakeup(shared_status);
        join_none

        // Step 4b: stop SOF to put the bus into global L2 suspend. This is the
        // only stimulus the host contributes; ending the suspend is the
        // device's job in this test.
        `uvm_info(MSG_ID, "Stopping SOF to suspend the bus...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end

        // Step 5: wait for the DUT itself to enter suspend, reported by the
        // checker over usb_dut_suspend_seen. This, and not the VIP link state,
        // is the gate: the DUT reacts on its own T_SUSPEND_DET, unrelated to
        // the VIP's tinactivity, and it is the DUT's suspend that the firmware
        // is waiting on to arm the wakeup. tinactivity is now deliberately set
        // shorter than T_SUSPEND_DET so the VIP is already suspended when the
        // device K arrives, but that is a configuration constraint and must not
        // become a gate here.
        //
        // The timeout arm is deliberately not an error: whether the DUT
        // suspended at all is the checker's CHK_SUSPEND_SEEN, and reporting it
        // in one place keeps one failure from producing two messages.
        fork
            begin: WAIT_DUT_SUSPEND
                // is_on() first: uvm_event::wait_trigger() only catches FUTURE
                // triggers, so an event the checker already fired before this
                // wait was reached would be missed and the ceiling paid in full.
                if (!dut_suspend_ev.is_on()) dut_suspend_ev.wait_trigger();
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

        // Step 6: wait for the DEVICE half of the handshake to be observed on
        // the DUT's own pins. caliptra_ss_usb_device_wakeup_checker triggers
        // usb_dut_wakeup_k_seen once it has seen TXValid high with linestate=K
        // held for its minimum, and owns the verdict as CHK_DEVICE_WAKEUP_K.
        //
        // This wait exists to ORDER the host half after the device half, which
        // matters twice over:
        //   - correctness of the check: if the host resume were driven first,
        //     the DUT would come out of suspend for a host-initiated reason and
        //     the device K might never be produced, yet the test would still
        //     look healthy from the bus;
        //   - correctness of the protocol: the host must not take over a resume
        //     that has not started.
        //
        // No error on timeout, by design - the checker's message can additionally
        // distinguish "never drove K" from "drove K but too briefly", which this
        // sequence cannot. The flow continues to step 7 either way so that the
        // observation window still gets closed and the checker still reports.
        fork
            begin: WAIT_DUT_WAKEUP_K
                // is_on() first, and it matters more here than anywhere else in
                // this file: the DUT drives K on the firmware's schedule, which
                // was measured completing while the main flow was still inside
                // the step 5 suspend wait.
                if (!dut_wakeup_k_ev.is_on()) dut_wakeup_k_ev.wait_trigger();
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

        // Informational only, and read after the wait so the log carries both
        // views side by side: what the host VIP made of the same event. This is
        // no longer a verdict; see the header note on why.
        report_vip_wakeup_view(shared_status);

        // Step 7: the HOST half. Ordering inside this step is protocol, not
        // preference.
        //
        // 7a. clear_suspend drives the host resume K and terminates it with the
        //     low-speed EOP (SE0). This is what the device is waiting for:
        //     usb_pie.m.vhdl BUS_EVENT_SW_WAKEUP_3 has no timeout arc out of it,
        //     so without this the DUT never returns to BUS_EVENT_FS_IDLE and can
        //     never answer step 9's transfer, no matter how long it is given.
        //     This cannot forge the verdict: CHK_DEVICE_WAKEUP_K needs the DUT
        //     to assert its own TXValid, which a host-driven K does not do.
        // 7b. SOF restart, because the VIP link SM drops back into suspend on
        //     its inactivity timer otherwise and the traffic check would run
        //     against a re-suspended link.
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


        // Step 8: wait for the DUT to leave suspend. Again gated on the DUT
        // event, not on the VIP link state: the VIP walks back to ENABLED on
        // its own schedule and polling for it here would add simulated time
        // without adding a check. The link state is logged for context, and the
        // post-resume traffic check in step 9 is what actually proves the link
        // is usable again.
        fork
            begin: WAIT_DUT_RESUME
                // is_on() first, and here it is not hypothetical: measured run
                // had CHK_RESUME_SEEN fire at 3.0167 ms while this wait was not
                // reached until 3.4293 ms, because step 6 had to spend its full
                // REMOTE_WAKEUP_WAIT_MAX ceiling first. The bare wait_trigger()
                // then missed the already-fired event and reported "Resume wait
                // ceiling reached without the DUT leaving suspend" 900 us after
                // the checker had already scored the resume - a false statement
                // in the log, directly contradicted by CHK_RESUME_SEEN.
                if (!dut_resume_ev.is_on()) dut_resume_ev.wait_trigger();
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

        // Step 9: the device must still be usable after waking itself.
        //
        // Gated on the DUT-side K event, NOT on the VIP status latch. That
        // matters: device_wakeup_latched is the VIP field, which is expected to
        // stay 0 even on a healthy DUT (see report_vip_wakeup_view), so gating
        // on it here would silently skip this check on every run - the check
        // would be dead code that nobody noticed.
        //
        // Skipped when the device never drove K, because then there was no
        // device-initiated resume to survive and a failure here would be noise
        // on top of CHK_DEVICE_WAKEUP_K, which already owns that report.
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
        // cosmetic: caliptra_ss_usb_suspend_resume_checker evaluates
        // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN only on this event, so without
        // the trigger neither check runs and the test would report PASSED
        // whatever the DUT did.
        obs_window_ev.trigger();

        `uvm_info(MSG_ID,
            "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence complete.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Forked sampler: latch the device remote wakeup the moment it appears.
    //
    // svt_usb_status::device_remote_wakeup_in_progress is documented by the VIP
    // as "Indicates whether Device is signaling Remotewakeup on the Bus". It is
    // a status bit rather than an event, so it has to be sampled; the step is
    // far shorter than any resume K the device can legally drive, so the
    // assertion cannot be missed between samples.
    //
    // This runs from before the suspend stimulus until the pulse is seen, and
    // it only records - it never reports pass or fail. Nothing it records can
    // fail the test any more: the verdict is CHK_DEVICE_WAKEUP_K in
    // caliptra_ss_usb_device_wakeup_checker, and what this sampler latches is
    // printed for the log by report_vip_wakeup_view() from the main flow, so
    // that the message appears once and in a deterministic order relative to
    // the other prints.

    //
    // The loop terminates on the first assertion. If the wakeup never happens
    // the thread is still spinning when the main flow finishes; that is
    // harmless, because it holds no objection and UVM kills the sequence's
    // child threads when body() returns.
    // -------------------------------------------------------------------------
    task sample_device_remote_wakeup(svt_usb_status shared_status);
        forever begin
            // Recorded on the same cadence and for the failure message only:
            // the VIP will not report a remote wakeup unless its own link is
            // suspended when the K arrives, so knowing whether the link ever
            // got there is what separates a DUT defect from a tinactivity
            // ordering fault in the test configuration.
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
    // Report what the HOST VIP made of the wakeup. Informational only.
    //
    // This used to be wait_for_latched_wakeup() and used to own the verdict, on
    // the basis that svt_usb_status::device_remote_wakeup_in_progress can only
    // be set by upstream K from the device. It was removed as a verdict because
    // the field was measured staying 0 through a full, correct, 3.089 ms device
    // K (docs/usb_remote_wakeup_selfclear_race_report.md sections 2A.4 and 7.4);
    // as a pass/fail condition it produced a false FAIL on a working DUT, which
    // is worse than no check at all. CHK_DEVICE_WAKEUP_K replaced it.
    //
    // It is still worth logging, for two reasons: it is the only view of the
    // event from the host side, and if a future VIP version starts setting the
    // field this message is where that will first show up. Every branch below is
    // uvm_info by construction - nothing here may fail the test.
    // -------------------------------------------------------------------------
    task report_vip_wakeup_view(svt_usb_status shared_status);
        if (device_wakeup_latched) begin
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: device_remote_wakeup_in_progress asserted at %0t, so the VIP agreed a device remote wakeup was on the bus. Link state %0s.",
                          device_wakeup_time,
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else if (!vip_link_suspend_seen) begin
            // Not a failure of anything, but the one case where the VIP view is
            // guaranteed uninformative: the VIP only interprets an upstream K as
            // a remote wakeup while its own link is suspended, so if the link was
            // never once seen in SUSPENDED, a correct device K was discarded.
            // Worth saying explicitly so nobody reads the silence as evidence.
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: device_remote_wakeup_in_progress never asserted, and the VIP link was never once seen in SUSPENDED (it is %0s now), so the VIP could not have reported a wakeup even from a perfectly correct device. This says nothing about the DUT; CHK_DEVICE_WAKEUP_K is the verdict. If the DUT check also failed, look at cfg.host_cfg.tinactivity / cfg.dev_cfg.tinactivity in the test class before suspecting the design: tinactivity must expire before the DUT's own suspend-detect timer, while staying above the 1 ms FS SOF period.",
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("Host VIP view: the VIP link did reach SUSPENDED (at %0t) but device_remote_wakeup_in_progress still never asserted. This is the known VIP behaviour recorded in docs/usb_remote_wakeup_selfclear_race_report.md sections 2A.4 and 7.4 and is expected even on a working DUT; it is not a failure. Read CHK_DEVICE_WAKEUP_K for the actual verdict. Link state %0s.",
                          vip_link_suspend_time,
                          shared_status.link_usb_20_state.name()), UVM_LOW)
        end
    endtask


    // -------------------------------------------------------------------------
    // Post-resume traffic check.
    //
    // Re-anchors the VIP on USBDC0 and issues a standard GetDescriptor(Device),
    // then requires a well-formed 18-byte device descriptor back. Both the
    // length and bDescriptorType are checked: a transfer that ended but
    // returned nothing, or returned a short or wrong descriptor, must not count
    // as the device still working. Same shape as the identically named task in
    // caliptra_ss_usb_hs_dev_hub_port_suspend_sequence.
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

        // Leave the anchor on the hub, where the hub-class helpers expect it,
        // in case this flow is ever extended past this point.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
