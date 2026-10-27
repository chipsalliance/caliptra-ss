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
        usb_cfg.tinactivity = 900_000_000.0; // 0.9 ms in ps
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            "tinactivity lowered to 0.9 ms for the suspend window (enumeration ran with the relaxed value).",
            UVM_LOW)

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
        //   7a. clear_suspend drives the host resume K and terminates it with
        //       the low-speed EOP the pie waits for in BUS_EVENT_SW_WAKEUP_3,
        //       which has no other exit arc. It cannot forge the verdict:
        //       CHK_DEVICE_WAKEUP_K needs the DUT's own TXValid;
        //   7b. SOF restart, or the VIP link falls straight back into suspend.
        //
        // The EOP lands ~3 ms before the pie can act on it. FS survives that
        // only because every FS packet ends in an SE0, so the restarted SOF
        // stream keeps supplying SE0s until one lands in the right state.
        // Anyone restructuring this step should adopt the HS ordering (sized
        // host K via tdrsmdn) rather than preserve that accident.
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

`endif // CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
