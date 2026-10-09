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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_SEQUENCE_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_SEQUENCE_SV

// =============================================================================
// USB dual-device Full-Speed bulk loopback sequence.
//
// Full-speed port of caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence.
// The bus-level flow is identical; the differences are:
//
//   1. FS link. The test class (caliptra_ss_usb_dual_device_fs_bulk_loopback_
//      test) clears high_speed_capable and stamps FS speed / FS max-packet
//      sizes on every endpoint_cfg entry, so the link settles at 12 Mbit/s. No
//      sequence-side action is needed to select the speed; this sequence only
//      has to tolerate the slower timing.
//
//   2. Longer settling delays. At FS a 64-byte bulk packet takes about 43 us on
//      the wire instead of about 1 us at HS, and the VIP only schedules tokens
//      on SOF boundaries (1 ms frames at FS versus 125 us microframes at HS).
//      The HS sequence's 20 us firmware-turnaround gaps are therefore far too
//      short here and are widened to multi-frame values.
//
//   3. Line-speed verification. This sequence triggers the global uvm_event
//      "usb_fs_obs_window_done" after the loopbacks complete, which releases
//      the completeness guard in caliptra_ss_usb_fs_speed_checker.sv (enabled
//      by +usb_fs_speed_check from the test .mk). That checker observes the
//      UTMI interface and fails the test if the link is actually running at HS
//      (CHK_XCVR_FS / CHK_RATE_FS) or if no traffic was ever seen
//      (CHK_SAW_TRAFFIC). Without this trigger the checker's guard never runs
//      and an unevaluated rate check would silently pass. The trigger must
//      happen while the run phase is still active so any uvm_report_error from
//      the checker is counted by final_phase, which is why it is done here
//      rather than left to the end of simulation.
//
// Topology (unchanged from the HS variant): both embedded device controllers of
// the compound USB IP (IP_3511) sit behind the on-chip 2-port hub and each does
// an independent EP1 64-byte bulk OUT -> IN loopback:
//   - USBDC0 : hub downstream port 1, assigned USB device address 2.
//   - USBDC1 : hub downstream port 2, assigned USB device address 3.
//
// The two controllers share one USB bus, so they must take DISTINCT addresses.
// The SVT VIP shared_cfg models a SINGLE remote device
// (local_device_cfg_size = 1); addressing a specific controller is therefore
// done by mutating usb_cfg.remote_device_cfg[0].device_address and calling
// host_agent_h.reconfigure(usb_cfg) in lockstep (see the constraint note in
// caliptra_ss_usb_base_sequence.svh). select_remote_device() below centralizes
// that switch so the OUT/IN data phases can be interleaved across the two
// controllers while the single remote-device model follows whichever address is
// currently being driven.
//
// Flow:
//   1. Wait for FS host link ENABLED.
//   2. Start SOF generation to keep the link alive between transfers.
//   3. Post-reset settling delay for MCU firmware to re-arm EP0 on both
//      controllers.
//   4. Enumerate the hub (addr 1).
//   5. Bring up port 1, enumerate USBDC0 at address 2.
//   6. Bring up port 2, enumerate USBDC1 at address 3.
//   7. Bulk OUT 64 bytes to USBDC0 EP1, then to USBDC1 EP1 (interleaved so
//      both controllers are driven in the same window).
//   8. Bulk IN  64 bytes from USBDC0 EP1, then from USBDC1 EP1.
//   9. Verify each loopback payload matches the bytes sent to that controller.
//  10. Release the TB FS speed checker's completeness guard.
//
// Each controller gets a distinct OUT pattern (dev0: byte[i]=i; dev1:
// byte[i]=i^0xFF) so a mis-routed loopback (data from the wrong controller) is
// caught by the content check, not just a length check.
// =============================================================================
class caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence)

    // USB device addresses assigned to the two controllers. They MUST differ.
    localparam bit [6:0] USBDC0_ADDR = 7'd2;
    localparam bit [6:0] USBDC1_ADDR = 7'd3;

    // Name of the global uvm_event triggered once the loopbacks are done, which
    // closes the observation window for the TB FS line-speed checker. Must
    // match OBS_WINDOW_EVENT in caliptra_ss_usb_fs_speed_checker.sv (and the
    // same string used by caliptra_ss_usb_fs_clock_sequence).
    string obs_window_event_name = "usb_fs_obs_window_done";

    // Upper bound on the wait for the host link to reach ENABLED. At FS the
    // VIP drives SE0 for drive_reset_time before going ENABLED, so link-up is
    // later than at HS; keep the bound generous but finite so a device that
    // never connects reports here rather than dying on the MCU-halt timeout.
    int unsigned link_up_timeout_us = 3000;

    // Firmware turnaround budget after a bulk OUT, before the matching bulk IN
    // is issued. The MCU must take the EP1OUT interrupt, copy 64 bytes and arm
    // EP1 IN. At FS the next IN token can only be scheduled on a 1 ms SOF
    // boundary anyway, so a sub-frame delay (the HS value was 20 us) buys
    // nothing and risks issuing the IN before the data is staged.
    int unsigned fw_turnaround_us = 200;

    // Settling budget between a hub downstream port reset and the first SETUP
    // addressed to the device behind that port.
    //
    // A hub port reset propagates a USB bus reset into the device controller
    // behind it, and the IP_3511 clears the Active bit on EVERY endpoint entry
    // when it sees one. The device then NAKs every token until firmware notices
    // DEVCMDSTAT.DRES_C and runs usb_handle_bus_reset() -> usb_ep0_reinit() to
    // re-arm the EP0 OUT/SETUP entries. USB 2.0 section 8.5.3 forbids NAKing a
    // SETUP, so any SETUP landing inside that re-arm window is flagged by the
    // VIP as valid_device_response_check ("Received a NAK device response to a
    // host SETUP packet which is a violation") even though the VIP's retries
    // eventually push the transfer through.
    //
    // hub_port_bringup_stepB() in the base sequence only waits 10 us after the
    // reset, which is an HS-tuned value. It is not enough here: this firmware
    // services BOTH controllers from one polling loop and does VPRINTF logging
    // in the EP0 path, so one controller's DRES_C handling can be queued behind
    // the other's servicing. Waiting several FS frames after each port
    // bring-up, before enumerating the device behind that port, guarantees the
    // first SETUP finds EP0 armed.
    int unsigned post_port_reset_us = 500;

    // Overall stimulus watchdog, in microseconds of simulation time.
    //
    // Without this the sequence can hang indefinitely: do_data_xfer() and the
    // control transfers inside the enum steps block on the VIP's transfer
    // completion, and if the VIP never completes one (observed: the SVT host
    // reports device_response_timeout_check on Dev:3 EP:0 and the sof_processor
    // then logs "SOF processor was not granted access to the link" every frame)
    // body() never returns and the run phase never ends. The watchdog turns
    // that silent hang into a reported failure at a known time, still closes
    // the FS speed checker's observation window, and lets the test terminate
    // with a verdict.
    //
    // Sized well above the expected stimulus length: hub enumeration plus two
    // device enumerations plus four bulk transfers at FS, with the 500 us
    // post-port-reset settling delays and the 200 us turnarounds, completes in
    // a few milliseconds of bus time.
    int unsigned stimulus_timeout_us = 20000;

    // Set by the watchdog when it fires, so the reporting path can distinguish
    // a watchdog abort from a clean finish.
    bit stimulus_timed_out = 0;

    function new(string name = "caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence");
        super.new(name);
    endfunction

    // Phase-boundary trace. Every step of the flow is bracketed with one of
    // these so the simulation log carries an explicit, timestamped stimulus
    // timeline that can be lined up against the MCU firmware's VPRINTF
    // timeline and against the SVT VIP's own per-transfer messages. This is
    // what makes a hang diagnosable: the last dbg_phase() printed identifies
    // exactly which transfer the VIP stalled on.
    function void dbg_phase(string phase);
        `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
            $sformatf("[%0t] PHASE: %s", $realtime, phase), UVM_LOW)
    endfunction

    // Point the single remote-device model at the given bus address so the
    // next data transfer's device_address constraint is satisfiable. Must be
    // called before each OUT/IN phase that targets a different controller.
    task select_remote_device(svt_usb_agent host_agent_h,
                              svt_usb_configuration usb_cfg,
                              bit [6:0] addr);
        usb_cfg.remote_device_cfg[0].device_address = addr;
        host_agent_h.reconfigure(usb_cfg);
        // Logged at UVM_LOW (the HS variant used UVM_HIGH): a mismatch between
        // this anchor address and the address a subsequent transfer is
        // constrained to is the usual cause of a randomize() failure or a
        // transfer aimed at the wrong controller, so the anchor history must be
        // visible in the default log.
        `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
            $sformatf("[%0t] Remote device model retargeted to address %0d.",
                      $realtime, addr),
            UVM_LOW)
    endtask

    // Release the TB FS speed checker's completeness guard. Called on every
    // path that reaches the end of the stimulus, including the link-timeout
    // path, so the checker always gets to report CHK_SAW_TRAFFIC rather than
    // letting unevaluated checks pass silently.
    function void close_speed_check_window();
        uvm_event obs_window_done;
        obs_window_done = uvm_event_pool::get_global(obs_window_event_name);
        obs_window_done.trigger();
        `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
            $sformatf("Triggered %s for the TB FS speed checker.",
                      obs_window_event_name),
            UVM_LOW)
    endfunction

    // Watchdog wrapper. run_stimulus() carries the whole flow; this task races
    // it against a fixed timeout so a VIP transfer that never completes cannot
    // wedge the run phase. join_any returns as soon as either branch finishes
    // and disable_fork then reaps the loser, so a clean run is unaffected
    // (the watchdog branch is simply killed).
    virtual task body();
        dbg_phase($sformatf(
            "stimulus start (watchdog armed at %0d us)", stimulus_timeout_us));

        fork
            begin : stimulus_branch
                run_stimulus();
            end
            begin : watchdog_branch
                #(stimulus_timeout_us * 1us);
                stimulus_timed_out = 1;
                `uvm_error("USB_DUAL_FS_LOOPBACK_SEQ",
                    $sformatf({"STIMULUS WATCHDOG EXPIRED after %0d us at %0t. ",
                               "The sequence was still blocked on a VIP ",
                               "transfer - see the last PHASE message above ",
                               "for the exact transfer, and the MCU dumps for ",
                               "the device-side EP0/EP1 state at that time. ",
                               "Aborting so the test reports a verdict instead ",
                               "of hanging."},
                              stimulus_timeout_us, $realtime))
                // Close the window on this path too, so the FS speed checker
                // reports its completeness guard rather than leaving the rate
                // checks unevaluated (which would silently pass).
                close_speed_check_window();
            end
        join_any
        disable fork;

        if (!stimulus_timed_out)
            dbg_phase("stimulus finished cleanly (watchdog disarmed)");
    endtask

    virtual task run_stimulus();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      dev0_out_req, dev0_in_req;
        svt_usb_transfer      dev1_out_req, dev1_in_req;
        bit [7:0]             dev0_data[];
        bit [7:0]             dev1_data[];
        int unsigned          i;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for FS link ENABLED. The VIP autonomously drives SE0 for
        // drive_reset_time (set in the test cfg) before going ENABLED, so by
        // the time this returns the DUT has already seen its bus reset and no
        // explicit se0 sequence is needed.
        dbg_phase($sformatf(
            "step 1: waiting for FS host link ENABLED (timeout %0d us)",
            link_up_timeout_us));
        wait_for_link_enabled(shared_status, "FS host link", link_up_timeout_us);
        if (link_wait_timed_out) begin
            dbg_phase("step 1 FAILED: link never reached ENABLED");
            // Still close the window: the checker must report that no traffic
            // was ever observed instead of leaving its checks unevaluated.
            close_speed_check_window();
            return;
        end

        // Step 2: Start SOF generation to keep the link alive. At FS this also
        // establishes the 1 ms frame timer the VIP schedules all tokens on.
        dbg_phase("step 1 done: link ENABLED");

        dbg_phase("step 2: starting SOF generation");
        start_sof_generation();

        // Step 3: Post-reset settling delay (both controllers re-arm EP0).
        dbg_phase("step 3: 50 us post-reset settling delay");
        #50us;

        // Step 4: Enumerate the hub (addr 1). Done once for both controllers.
        dbg_phase("step 4: hub enumeration (hub_enum_stepA, hub -> addr 1)");
        hub_enum_stepA(host_agent_h, usb_cfg);
        dbg_phase("step 4 done: hub enumerated at addr 1");

        // Step 5: Bring up port 1 and enumerate USBDC0 at address 2.
        dbg_phase("step 5a: hub downstream port 1 bring-up");
        hub_port_bringup_stepB(
            .host_agent_h(host_agent_h), .usb_cfg(usb_cfg), .port_num(1));
        dbg_phase($sformatf(
            "step 5b: port 1 reset done, settling %0d us before first SETUP",
            post_port_reset_us));

        // Let USBDC0 finish its bus-reset EP0 re-arm before the first SETUP.
        // See post_port_reset_us.
        #(post_port_reset_us * 1us);

        dbg_phase("step 5c: USBDC0 enumeration (usbdc0_enum_stepC, -> addr 2)");
        usbdc0_enum_stepC(
            .host_agent_h  (host_agent_h),
            .usb_cfg       (usb_cfg),
            .suffix        ("_dev0"),
            .device_idx    (0),
            .assign_address(USBDC0_ADDR));
        dbg_phase("step 5 done: USBDC0 enumerated and configured at addr 2");

        // Step 6: Bring up port 2 and enumerate USBDC1 at address 3.
        // Step 5's usbdc0_enum_stepC() left the VIP anchor at address 2
        // (USBDC0). hub_port_bringup_stepB() issues hub-class requests at
        // device address 1 and requires the anchor to be 1 on entry (see its
        // header comment), so re-anchor onto the hub first; otherwise the
        // GetPortStatus_Port2 WITH-constraint (device_address==1) contradicts
        // the VIP fixed_dev_ep_ustr_valid_ranges constraint (device_address==2)
        // and randomize() fails.
        dbg_phase("step 6a: re-anchoring onto the hub (addr 1) for port 2 setup");
        select_remote_device(host_agent_h, usb_cfg, 7'd1);
        dbg_phase("step 6b: hub downstream port 2 bring-up");
        hub_port_bringup_stepB(
            .host_agent_h(host_agent_h), .usb_cfg(usb_cfg), .port_num(2));
        dbg_phase($sformatf(
            "step 6c: port 2 reset done, settling %0d us before first SETUP",
            post_port_reset_us));

        // Same bus-reset EP0 re-arm window for USBDC1. This one matters more:
        // the port-2 reset arrives while firmware may still be draining
        // USBDC0's enumeration traffic from step 5.
        #(post_port_reset_us * 1us);

        dbg_phase("step 6d: USBDC1 enumeration (usbdc0_enum_stepC, -> addr 3)");
        usbdc0_enum_stepC(
            .host_agent_h  (host_agent_h),
            .usb_cfg       (usb_cfg),
            .suffix        ("_dev1"),
            .device_idx    (1),
            .assign_address(USBDC1_ADDR));
        dbg_phase("step 6 done: USBDC1 enumerated and configured at addr 3");

        `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
            "Dual-device FS enumeration complete (USBDC0@2, USBDC1@3).", UVM_LOW)
        #10us;

        // Build distinct 64-byte patterns so a cross-routed loopback fails the
        // content check (dev0: i, dev1: i xor 0xFF).
        dev0_data = new[64];
        dev1_data = new[64];
        for (i = 0; i < 64; i++) begin
            dev0_data[i] = i[7:0];
            dev1_data[i] = i[7:0] ^ 8'hFF;
        end

        // Step 7: Bulk OUT to both controllers (interleaved). Retarget the
        // single remote-device model before each OUT. ep_anchor_idx 2 = EP1
        // BULK OUT (see the test's endpoint_cfg[] layout).
        //
        // no_zero_length_end is NOT set, matching the HS variant: at FS the EP1
        // bulk max_packet_size is 64, so a 64-byte OUT is exactly max-packet
        // aligned and the VIP would normally append a terminating ZLP. The
        // firmware never consumes that ZLP and would NAK it, so the ZLP is
        // suppressed by allow_aligned_transfer_without_zero_length=1 on
        // endpoint_cfg[2] in the test class instead of by a per-transfer
        // constraint here - the two mechanisms are mutually exclusive and
        // setting both over-constrains randomize().
        dbg_phase("step 7a: BULK OUT 64 bytes to USBDC0 EP1 (addr 2)");
        select_remote_device(host_agent_h, usb_cfg, USBDC0_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr  (int'(USBDC0_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(2),
            .label        ("FS_BULK_OUT_EP1_dev0"),
            .req          (dev0_out_req),
            .obj_name     ("dev0_out_req"),
            .payload_data (dev0_data));
        dbg_phase("step 7a done: USBDC0 BULK OUT complete");

        dbg_phase("step 7b: BULK OUT 64 bytes to USBDC1 EP1 (addr 3)");
        select_remote_device(host_agent_h, usb_cfg, USBDC1_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr  (int'(USBDC1_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(2),
            .label        ("FS_BULK_OUT_EP1_dev1"),
            .req          (dev1_out_req),
            .obj_name     ("dev1_out_req"),
            .payload_data (dev1_data));
        dbg_phase("step 7b done: USBDC1 BULK OUT complete");

        // Allow MCU firmware time to copy EP1 OUT->IN and arm IN on both. See
        // fw_turnaround_us: this is a multi-frame wait at FS, not the HS 20 us.
        dbg_phase($sformatf(
            "step 7c: %0d us firmware turnaround (EP1 OUT->IN copy and arm)",
            fw_turnaround_us));
        #(fw_turnaround_us * 1us);

        // Step 8: Bulk IN from both controllers (loopback readback).
        // ep_anchor_idx 1 = EP1 BULK IN.
        dbg_phase("step 8a: BULK IN 64 bytes from USBDC0 EP1 (addr 2)");
        select_remote_device(host_agent_h, usb_cfg, USBDC0_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr  (int'(USBDC0_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(1),
            .label        ("FS_BULK_IN_EP1_dev0"),
            .req          (dev0_in_req),
            .obj_name     ("dev0_in_req"));
        dbg_phase("step 8a done: USBDC0 BULK IN complete");

        dbg_phase("step 8b: BULK IN 64 bytes from USBDC1 EP1 (addr 3)");
        select_remote_device(host_agent_h, usb_cfg, USBDC1_ADDR);
        do_data_xfer(
            .agent_h      (host_agent_h),
            .usb_cfg      (usb_cfg),
            .xfer_kind    (svt_usb_transfer::BULK_IN_TRANSFER),
            .device_addr  (int'(USBDC1_ADDR)),
            .ep_num       (1),
            .byte_count   (64),
            .ep_anchor_idx(1),
            .label        ("FS_BULK_IN_EP1_dev1"),
            .req          (dev1_in_req));
        dbg_phase("step 8b done: USBDC1 BULK IN complete");

        // Step 9: Verify each loopback payload.
        dbg_phase("step 9: comparing both loopback payloads");
        check_loopback("USBDC0", dev0_in_req, dev0_data);
        check_loopback("USBDC1", dev1_in_req, dev1_data);

        // Allow MCU firmware time to log both completions.
        #(fw_turnaround_us * 1us);

        // Step 10: Close the observation window so the TB FS speed checker
        // evaluates its completeness guard while the run phase is still live.
        dbg_phase("step 10: closing the FS speed-check observation window");
        close_speed_check_window();

        `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
            "USB dual-device FS bulk loopback sequence complete.", UVM_LOW)
    endtask

    // Compare a received bulk IN payload against the bytes sent to that
    // controller, erroring on any mismatch.
    function void check_loopback(string dev_name, svt_usb_transfer in_req,
                                 bit [7:0] sent[]);
        int mismatch_count;
        mismatch_count = 0;
        for (int unsigned bi = 0; bi < 64; bi++) begin
            if (in_req.payload.data[bi] !== sent[bi]) begin
                `uvm_error("USB_DUAL_FS_LOOPBACK_SEQ",
                    $sformatf("%s loopback mismatch at byte[%0d]: sent=0x%02h received=0x%02h",
                              dev_name, bi, sent[bi], in_req.payload.data[bi]))
                mismatch_count++;
            end
        end
        if (mismatch_count == 0)
            `uvm_info("USB_DUAL_FS_LOOPBACK_SEQ",
                $sformatf("%s loopback data check PASSED: all 64 bytes match.",
                          dev_name), UVM_LOW)
        else
            `uvm_error("USB_DUAL_FS_LOOPBACK_SEQ",
                $sformatf("%s loopback data check FAILED: %0d byte(s) mismatched.",
                          dev_name, mismatch_count))
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_SEQUENCE_SV
