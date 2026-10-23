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

`ifndef CALIPTRA_SS_USB_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_BASE_SEQUENCE_SV

// =============================================================================
// Base sequence for Caliptra-SS USB host-side sequences.
//
// Centralizes the protocol-level boilerplate that was copy-pasted, near-
// identically, across every per-test sequence file:
//
//   - pre_start()/post_start(): resolve the shared usb_data_check_api handle
//     from the config_db, and raise/drop the starting phase's objection when
//     this sequence has no parent sequence (i.e. it was start()'d directly
//     as a top-level sequence rather than nested inside another).
//   - resolve_host_agent(): cast p_sequencer's parent component to
//     svt_usb_agent (every sequence needs this to reach agent_h.prot for
//     wait_xfer_done() and agent_h.reconfigure() after a SET_ADDRESS).
//   - resolve_shared_status(): fetch the svt_usb_status object the link FSM
//     writes, via p_sequencer.get_shared_status(this).
//   - resolve_xfer_handles(): resolve the agent, configuration and shared
//     status handles in one call (used by the init and OCP recovery
//     sequences, which cache them as members).
//   - wait_for_link_enabled(): the fork/disable idiom that blocks until
//     shared_status.link_usb_20_state reaches ENABLED, with a periodic
//     status log every 10 us while waiting. Bounded by timeout_us; on
//     expiry it raises a uvm_error, sets link_wait_timed_out and returns,
//     so a DUT that never connects fails the test instead of hanging the
//     simulation.
//   - start_sof_generation(): start the svt_usb_protocol_service_20_sof_on
//     sequence on p_sequencer.prot_service_sequencer, needed by every
//     sequence to keep the link out of SUSPENDED during an idle window.
//   - do_control_xfer(): build, randomize and issue one svt_usb_transfer
//     CONTROL_TRANSFER with the given SETUP fields, then finish_item() it.
//   - wait_xfer_done(): block on an svt_usb_agent's
//     prot.NOTIFY_USB_TRANSFER_ENDED event.
//   - do_data_xfer(): build, randomize and issue one data-stage
//     svt_usb_transfer (bulk OUT/IN, isochronous OUT/IN) with optional
//     caller-supplied payload, then wait for it to complete.
//
// This is a `virtual class` (abstract): it is never `start()`ed directly and
// is never registered with `uvm_object_utils`, only extended. Every concrete
// per-test sequence should extend this class instead of `uvm_sequence`
// directly, then keep only its own body() and any per-test-specific helper
// tasks (e.g. the hub enumeration steps, bulk/iso payload construction).
//
// UVM_INFO verbosity policy (rationalised):
//   - UVM_MEDIUM : coarse milestones a default run wants to see - link-up
//                  start/complete and the three enumeration step completions.
//   - UVM_HIGH   : per-transfer chatter and periodic polling - CONTROL/DATA
//                  issue+complete lines, the 10 us link-state poll, the SOF
//                  start note, and the VIP anchor-reset note.
//   - uvm_error / uvm_fatal : unchanged (real failures).
// =============================================================================


virtual class caliptra_ss_usb_base_sequence extends uvm_sequence;

    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected caliptra_ss_usb_data_check_api usb_data_check_api;
    protected svt_usb_transfer last_ctrl_seq_item;

    // Bits of svt_usb_transfer::results_status that describe a NORMAL end of
    // transfer rather than a failure, and must therefore be ignored when
    // deciding whether a transfer succeeded.
    //
    //   bit 5 - "Transfer finished due to 0-length Data Packet" (Host).
    //           Set on every control transfer with no data stage, i.e. on
    //           SET_ADDRESS and SET_CONFIGURATION, and on any bulk IN that
    //           ends on a zero-length packet. The VIP's own sequence library
    //           (svt_usb_20_na_30_ss_transfer_system_virtual_sequence_collection)
    //           reports status==ACCEPT with results_status==0x20 as
    //           "completed normally (with 0-length DP)".
    //
    // Everything else in the table is a genuine failure reason (bit 1 host
    // abort command, bit 2 device response timeout, bit 3 injected-error
    // timeout, bit 4 STALL, bit 6 uframe interval exceeded, bit 7 unexpected
    // device timeout, ...), so only these benign bits are masked out.
    localparam bit [127:0] USB_RESULTS_STATUS_BENIGN_MASK = 128'h20;


    // Set by wait_for_link_enabled() when its timeout expired before the
    // link reached ENABLED. Cleared at every entry to that task. Sequences
    // that must abort the rest of their body on a failed link-up read this
    // instead of duplicating their own timeout fork.
    bit link_wait_timed_out = 1'b0;

    // Set by wait_xfer_done() when its timeout expired before the VIP reported
    // NOTIFY_USB_TRANSFER_ENDED. Cleared at every entry to that task. Sequences
    // that want to abandon a multi-step flow after one transfer went unanswered
    // read this instead of adding their own fork.
    bit xfer_wait_timed_out = 1'b0;

    // Hub Self-Powered state from bmAttributes D6 of its CONFIGURATION
    // descriptor, captured during hub enumeration. GET_STATUS(DEVICE) D0
    // must report the same state (USB 2.0 Sec 9.4.5, Sec 9.6.3).
    bit hub_self_powered = 1'b0;

    function new(string name = "caliptra_ss_usb_base_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------
    // pre_start / post_start
    //
    // pre_start() does two things:
    //
    //  1. Resolves the shared usb_data_check_api handle from the config_db.
    //     This is deliberately NOT done in new(): the handle is published by
    //     caliptra_ss_usb_data_check_api_impl::build_phase(), which UVM runs
    //     only after the enclosing test's own build_phase has returned. A
    //     get() in the constructor would therefore make it illegal for a
    //     test to create its sequence object inside build_phase - which is
    //     exactly what a test must do when it needs to set fields on the
    //     sequence instance before installing it as default_sequence.
    //     pre_start() runs when the sequence is actually started, by which
    //     point the handle always exists.
    //
    //     NOTE: any subclass that overrides pre_start() must call
    //     super.pre_start(), or usb_data_check_api will be left null.
    //
    //  2. Raises the starting phase's objection, but only when this sequence
    //     has no parent sequence - i.e. it was start()'d directly as a
    //     top-level sequence from a test, rather than nested inside another
    //     sequence (which would already be holding its own objection).
    //     post_start() drops it symmetrically.
    // -------------------------------------------------------------------
    virtual task pre_start();
        uvm_phase phase;
        super.pre_start();

        if (uvm_config_db#(caliptra_ss_usb_data_check_api)::get(null, "uvm_test_top",
                                                               "usb_data_check_api",
                                                               usb_data_check_api) != 1) begin
            `uvm_fatal("USB_BASE_SEQ", "impossible to get usb_data_check_api")
        end

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

    // -------------------------------------------------------------------
    // resolve_host_agent
    //
    // Every sequence needs the svt_usb_agent handle (for agent_h.prot in
    // wait_xfer_done() and agent_h.reconfigure() after a SET_ADDRESS). The
    // agent is p_sequencer's parent component; this was previously
    // re-implemented, identically, in every body() task.
    // -------------------------------------------------------------------
    function svt_usb_agent resolve_host_agent();
        svt_usb_agent host_agent_h;
        uvm_component parent_comp;
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_BASE_SEQ",
                $sformatf("Cannot cast p_sequencer parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))
        return host_agent_h;
    endfunction

    // -------------------------------------------------------------------
    // resolve_shared_status
    //
    // Fetch the svt_usb_status object the link FSM writes
    // (link_usb_20_state, etc), via the canonical accessor
    // p_sequencer.get_shared_status(this). Fatals if null.
    // -------------------------------------------------------------------
    function svt_usb_status resolve_shared_status();
        svt_usb_status shared_status;
        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_BASE_SEQ",
                "p_sequencer.get_shared_status(this) returned null.")
        return shared_status;
    endfunction

    // -------------------------------------------------------------------
    // resolve_usb_cfg
    //
    // Fetch and cast p_sequencer's configuration to svt_usb_configuration.
    // Needed before the first SET_ADDRESS reconfigure() and by
    // do_control_xfer()'s usb_cfg argument.
    // -------------------------------------------------------------------
    function svt_usb_configuration resolve_usb_cfg();
        svt_configuration     get_cfg;
        svt_usb_configuration usb_cfg;
        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_BASE_SEQ", "Unable to cast configuration to svt_usb_configuration")
        return usb_cfg;
    endfunction

    // -------------------------------------------------------------------
    // resolve_xfer_handles
    //
    // Resolve the host agent, configuration and shared status in one call
    // for sequences that cache all three as members before issuing
    // transfers.
    // -------------------------------------------------------------------
    virtual task resolve_xfer_handles(
        output svt_usb_agent         host_agent_h,
        output svt_usb_configuration usb_cfg,
        output svt_usb_status        shared_status);
        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();
    endtask

    // -------------------------------------------------------------------
    // start_sof_generation
    //
    // Start the svt_usb_protocol_service_20_sof_on_sequence on
    // p_sequencer.prot_service_sequencer. Every sequence needs this once
    // the link reaches ENABLED: without SOF/micro-frame packets the VIP
    // link state machine transitions to SUSPENDED within its idle timeout.
    // -------------------------------------------------------------------
    task start_sof_generation();
        svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
        sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
        sof_on_seq.start(p_sequencer.prot_service_sequencer);
        `uvm_info("USB_BASE_SEQ", "SOF generation started.", UVM_LOW)
    endtask

    // -------------------------------------------------------------------
    // do_control_xfer
    //
    // Build one svt_usb_transfer CONTROL_TRANSFER item with the given SETUP
    // packet fields, randomize it with those fields WITH-constrained, and
    // issue it via start_item/finish_item on p_sequencer.xfer_sequencer.
    // Does not itself wait for completion - pair with wait_xfer_done()
    // (usually forked before finish_item() for short transfers - see that
    // task's header comment).
    //
    // usb_cfg, if non-null, is assigned onto the transfer's cfg handle
    // before randomize() so the item picks up the caller's current
    // configuration (e.g. after a reconfigure() following a SET_ADDRESS).
    // -------------------------------------------------------------------
    task do_control_xfer(
        input bit [7:0]  bm_request_type_dir,
        input bit [7:0]  bm_request_type_type,
        input bit [7:0]  bm_request_type_recip,
        input bit [7:0]  brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label,
        input svt_usb_configuration usb_cfg = null,
        input bit        no_queue_and_hold = 0
    );
        svt_usb_transfer req;
        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        `uvm_info("USB_BASE_SEQ",
            $sformatf("CONTROL %s started (addr=%0d)", label, device_addr), UVM_LOW)
        if (usb_cfg != null)
            req.cfg = usb_cfg;
        // fix_anchors(dev_idx, ep_idx, upstream_idx): dev_idx is the array
        // index into remote_device_cfg[], always 0 for a single-device setup.
        req.fix_anchors(0, 0, 0);
        // no_queue_and_hold constrains queue_and_hold==0 on the transfer.
        //
        // NOTE: this has no effect on VIP behaviour. svt_usb_transfer
        // documents queue_and_hold as "utilized by the USB Test Suite's DUT
        // USB Host xHCI Driver for controlling whether or not the xHCI
        // Doorbell for the endpoint is rung", and states explicitly "THIS
        // FIELD IS NOT UTILIZED BY ANY OF THE USB SVT TRANSACTORS". It is
        // kept only because the randomize() default distribution
        // (QUEUE_AND_HOLD_SET_wt=70 vs CLEAR_wt=30) would otherwise leave the
        // field randomized; pinning it keeps transfers reproducible. Do not
        // rely on it to change when a transfer reaches the bus.
        if (no_queue_and_hold) begin
            if (!req.randomize() with {
                    xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                    device_address                     == device_addr;
                    setup_data_bmrequesttype_dir       == bm_request_type_dir;
                    setup_data_bmrequesttype_type      == bm_request_type_type;
                    setup_data_bmrequesttype_recipient == bm_request_type_recip;
                    setup_data_brequest                == brequest_val;
                    setup_data_w_value                 == wvalue;
                    setup_data_w_index                 == windex;
                    setup_data_w_length                == wlength;
                    queue_and_hold                     == 0;
                }) begin
                `uvm_fatal("USB_BASE_SEQ", $sformatf("randomize failed for %s", label))
            end
        end
        else if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == device_addr;
                setup_data_bmrequesttype_dir       == bm_request_type_dir;
                setup_data_bmrequesttype_type      == bm_request_type_type;
                setup_data_bmrequesttype_recipient == bm_request_type_recip;
                setup_data_brequest                == brequest_val;
                setup_data_w_value                 == wvalue;
                setup_data_w_index                 == windex;
                setup_data_w_length                == wlength;
            }) begin
            `uvm_fatal("USB_BASE_SEQ", $sformatf("randomize failed for %s", label))
        end
        finish_item(req, -1);

        void'($cast(last_ctrl_seq_item,req));
        `uvm_info("USB_BASE_SEQ",
            $sformatf("CONTROL %s done (addr=%0d)", label, device_addr), UVM_LOW)
    endtask

    // -------------------------------------------------------------------
    // wait_xfer_done
    //
    // Block until agent_h.prot fires NOTIFY_USB_TRANSFER_ENDED. For short
    // bulk/iso transfers, callers must fork this wait BEFORE finish_item()
    // on the transfer item - the VIP can complete a short transfer and fire
    // the event before the calling thread resumes after finish_item(),
    // which would make a wait AFTER finish_item() miss the pulse and hang
    // indefinitely (see caliptra_ss_usb_hs_dev_bulk_out_sequence.svh for the
    // canonical fork pattern).
    //
    // The wait is bounded by timeout_us. Without a bound, a transfer that the
    // VIP never completes - for example a control transfer queued while the
    // host link has gone SUSPENDED on its tinactivity timer, which the link
    // then never grants - blocks this task forever. The run does not fail: the
    // sequence simply stops making progress, never reaches the checker arm and
    // observation events, and the simulation ends on the MCU-halt mechanism
    // with no verdict at all and no UVM_ERROR (the silent-pass mode recorded in
    // docs/handover/claude_md/16_usb_silent_fail_verdict_gap.md). The only
    // visible symptom is unrelated-looking VIP chatter such as "SOF processor
    // was not granted access to the link". On expiry a uvm_error naming the
    // transfer is issued, xfer_wait_timed_out is set and the task returns, so
    // the failure is reported where it happened.
    //
    // The default ceiling is deliberately generous: it must not fire on a
    // transfer that is merely slow on this testbench, only on one that is never
    // going to complete. Callers with a tighter expectation can pass their own.
    // -------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label,
                        int unsigned timeout_us = 2000);
        xfer_wait_timed_out = 1'b0;
        fork
            begin: WAIT_XFER
                agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
                disable XFER_TIMEOUT;
            end
            begin: XFER_TIMEOUT
                #(timeout_us * 1us);
                xfer_wait_timed_out = 1'b1;
                disable WAIT_XFER;
            end
        join

        if (xfer_wait_timed_out) begin
            agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.cancel();
            `uvm_error("USB_BASE_SEQ",
                $sformatf({"Transfer %s never completed within %0d us ",
                           "(NOTIFY_USB_TRANSFER_ENDED was never fired). The ",
                           "transfer was issued but the VIP never reported it ",
                           "finished, so either the device did not answer or ",
                           "the host link was not granted to it. Check whether ",
                           "the link went SUSPENDED - cfg.host_cfg.tinactivity ",
                           "must stay longer than the largest idle gap in the ",
                           "active phase of the test."},
                          label, timeout_us))
            return;
        end

        `uvm_info("USB_BASE_SEQ",
            $sformatf("Transfer %s completed.", label), UVM_LOW)
    endtask

    // -------------------------------------------------------------------
    // check_xfer_status
    //
    // Assert that a transfer the VIP has finished with actually SUCCEEDED.
    // NOTIFY_USB_TRANSFER_ENDED (and therefore wait_xfer_done()) fires on
    // ANY terminal outcome, including ABORTED, so a sequence that only
    // waits for the event cannot tell a good transfer from a dead one and
    // will happily report "enumeration complete" on a bus where the device
    // answered nothing at all.
    //
    // Two independent VIP fields are inspected:
    //   svt_usb_transfer::status        - must be ACCEPT. ABORTED/CANCELLED
    //                                    mean the VIP gave up on the
    //                                    transfer (device response timeout,
    //                                    STALL, protocol reset, ...).
    //   svt_usb_transfer::results_status - a bit array describing how the
    //                                    transfer ended. Most set bits are
    //                                    failure reasons (bit 1/2/3 abort or
    //                                    response timeout, bit 4 STALL, ...),
    //                                    but NOT all of them: bit 5 means
    //                                    "transfer finished due to 0-length
    //                                    Data Packet", which is the normal
    //                                    and expected outcome for a control
    //                                    transfer with no data stage
    //                                    (SET_ADDRESS, SET_CONFIGURATION)
    //                                    and for a short/zero-length bulk IN.
    //                                    The VIP's own sequence library
    //                                    treats status==ACCEPT together with
    //                                    results_status==0x20 as "completed
    //                                    normally (with 0-length DP)", so the
    //                                    benign bits are masked out here via
    //                                    USB_RESULTS_STATUS_BENIGN_MASK and
    //                                    only the remaining bits are failures.
    //
    // min_payload_bytes, when non-zero, additionally requires the transfer
    // to have moved at least that many payload bytes. An ABORTED IN control
    // transfer typically ends with a zero-length payload, so data checks
    // run on it would be comparing against nothing and would pass by
    // accident - callers that read a descriptor or a configuration value
    // back must set this to the number of bytes they rely on.
    //
    // All failures are reported as uvm_error against the caller-supplied
    // label so the log identifies the exact transfer, and fail is set to 1
    // so a caller can skip dependent checks instead of cascading noise.
    // -------------------------------------------------------------------
    task check_xfer_status(svt_usb_transfer xfer,
                           string           label,
                           int unsigned     min_payload_bytes = 0,
                           output bit       fail);
        int unsigned     pld_bytes;
        bit [127:0]      rs_failures;
        fail = 1'b0;

        if (xfer == null) begin
            `uvm_error("USB_BASE_SEQ",
                $sformatf("Transfer %s: no transfer handle to check (null) - the transfer was never issued or the handle was lost.",
                          label))
            fail = 1'b1;
            return;
        end

        if (xfer.status != svt_usb_transfer::ACCEPT) begin
            `uvm_error("USB_BASE_SEQ",
                $sformatf("Transfer %s FAILED: status=%s (expected ACCEPT), results_status=0x%0h. The VIP terminated this transfer without a complete, accepted exchange - the device did not respond as the protocol requires.",
                          label, xfer.status.name(), xfer.results_status))
            fail = 1'b1;
        end

        // Only the non-benign bits count as failures. results_status==0x20
        // alone means the transfer simply ended on a zero-length data packet,
        // which is the normal outcome for SET_ADDRESS / SET_CONFIGURATION and
        // for a bulk IN that terminates short.
        rs_failures = xfer.results_status & ~USB_RESULTS_STATUS_BENIGN_MASK;
        if (rs_failures != 0) begin
            `uvm_error("USB_BASE_SEQ",
                $sformatf("Transfer %s FAILED: results_status=0x%0h carries failure bits 0x%0h (status=%s). Each set bit encodes a transfer failure reason - decode it against the svt_usb_transfer results_status bit table (bit 2 device response timeout, bit 4 STALL, ...).",
                          label, xfer.results_status, rs_failures, xfer.status.name()))
            fail = 1'b1;
        end

        if (min_payload_bytes != 0) begin
            pld_bytes = xfer.payload_byte_count();
            if (pld_bytes < min_payload_bytes) begin
                `uvm_error("USB_BASE_SEQ",
                    $sformatf("Transfer %s FAILED: moved %0d payload bytes, expected at least %0d (status=%s, results_status=0x%0h). Any data check run on this transfer would be inspecting an empty or truncated payload.",
                              label, pld_bytes, min_payload_bytes,
                              xfer.status.name(), xfer.results_status))
                fail = 1'b1;
            end
        end

        if (!fail)
            `uvm_info("USB_BASE_SEQ",
                $sformatf("Transfer %s status checked: ACCEPT, results_status=0x%0h (no failure bits), payload=%0d bytes.",
                          label, xfer.results_status, xfer.payload_byte_count()), UVM_HIGH)
    endtask

    // -------------------------------------------------------------------
    // wait_and_check_xfer
    //
    // wait_xfer_done() followed immediately by check_xfer_status() on the
    // most recent control transfer (last_ctrl_seq_item, set by
    // do_control_xfer()). This is the form every control-transfer call site
    // should use: waiting without checking is what allowed a fully failing
    // enumeration to be logged as successful.
    // -------------------------------------------------------------------
    task wait_and_check_xfer(svt_usb_agent agent_h,
                             string        label,
                             int unsigned  min_payload_bytes = 0,
                             output bit    fail);
        wait_xfer_done(.agent_h(agent_h), .label(label));
        check_xfer_status(.xfer             (last_ctrl_seq_item),
                          .label            (label),
                          .min_payload_bytes(min_payload_bytes),
                          .fail             (fail));
    endtask


    // -------------------------------------------------------------------
    // do_control_xfer_and_wait
    //
    // Issue a control transfer and wait for ITS OWN completion, forking the
    // wait before the transfer is handed to the driver.
    //
    // NOTIFY_USB_TRANSFER_ENDED is a protocol-layer-wide event, not a
    // per-transfer one: the VIP fetches it from the protocol transactor's
    // event pool, so every transfer on the agent pulses the same event. A
    // caller that runs do_control_xfer() to completion and only then waits
    // can therefore consume the pulse belonging to the PREVIOUS transfer and
    // return while its own transfer is still in flight. check_xfer_status()
    // then samples last_ctrl_seq_item mid-flight, sees a status that is
    // neither ACCEPT nor DISABLED, and reports a failure against a transfer
    // the device goes on to service perfectly a few microseconds later.
    //
    // That misreport is identifiable: status=ABORTED with results_status=0x0.
    // Per svt_usb_transfer the results_status bits are set by whoever aborts
    // a transfer ("It is the responsibility of the calling process to set any
    // transfer attributes to correctly capture the reason for the abort"), and
    // an all-zero vector is defined to mean a successful transfer. ABORTED
    // with no reason bit set is thus not a device failure at all - it is
    // set_aborted_status() sweeping a still-active transfer at teardown.
    //
    // The hazard only bites when two control transfers are issued back to
    // back with no delay between them, which is exactly what the
    // SET_CONFIGURATION + GET_CONFIGURATION read-back pair in
    // usbdc0_enum_stepC() does. The bulk path has always forked (see the
    // fork_wait branch of the data-transfer task); the control path did not.
    // -------------------------------------------------------------------
    task do_control_xfer_and_wait(
        input svt_usb_agent agent_h,
        input bit [7:0]  bm_request_type_dir,
        input bit [7:0]  bm_request_type_type,
        input bit [7:0]  bm_request_type_recip,
        input bit [7:0]  brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label,
        input svt_usb_configuration usb_cfg = null,
        input bit        no_queue_and_hold = 0,
        input int unsigned min_payload_bytes = 0,
        output bit       fail
    );
        fork
            begin
                wait_xfer_done(.agent_h(agent_h), .label(label));
            end
            begin
                do_control_xfer(
                    .bm_request_type_dir  (bm_request_type_dir),
                    .bm_request_type_type (bm_request_type_type),
                    .bm_request_type_recip(bm_request_type_recip),
                    .brequest_val         (brequest_val),
                    .wvalue               (wvalue),
                    .windex               (windex),
                    .wlength              (wlength),
                    .device_addr          (device_addr),
                    .label                (label),
                    .usb_cfg              (usb_cfg),
                    .no_queue_and_hold    (no_queue_and_hold));
            end
        join
        check_xfer_status(.xfer             (last_ctrl_seq_item),
                          .label            (label),
                          .min_payload_bytes(min_payload_bytes),
                          .fail             (fail));
    endtask


    // -------------------------------------------------------------------
    // wait_for_link_enabled
    //
    // Block until shared_status.link_usb_20_state reaches ENABLED, logging
    // the current link state every 10 us while waiting. label is used only
    // to make the log lines identify which sequence/stage called this
    // (e.g. "FS link" vs "HS link").
    //
    // The wait is bounded by timeout_us: a device or hub that never connects
    // would otherwise leave the sequence waiting forever, and the run would
    // die on the far coarser MCU-halt timeout with no indication of the real
    // cause. On expiry a uvm_error is issued and the task returns.
    //
    // Callers that must skip the rest of their body when the link never came
    // up should test link_wait_timed_out after the call - it is set to 1 only
    // when this task gave up, and cleared at every entry.
    // -------------------------------------------------------------------
    task wait_for_link_enabled(svt_usb_status shared_status,
                               string       label      = "link",
                               int unsigned timeout_us = 3000);
        link_wait_timed_out = 1'b0;
        `uvm_info("USB_BASE_SEQ",
            $sformatf("Waiting for %s ENABLED (current=%p, timeout=%0d us)...",
                      label, shared_status.link_usb_20_state, timeout_us), UVM_MEDIUM)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
                disable LINK_TIMEOUT;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_BASE_SEQ",
                        $sformatf("link_usb_20_state=%p", shared_status.link_usb_20_state),
                        UVM_HIGH);
                end
            end
            begin: LINK_TIMEOUT
                #(timeout_us * 1us);
                link_wait_timed_out = 1'b1;
                disable REPORT_LINK;
                disable WAIT_EN;
            end
        join

        if (link_wait_timed_out) begin
            `uvm_error("USB_BASE_SEQ",
                $sformatf({"%s never reached ENABLED within %0d us ",
                           "(last state [%p]). The device did not connect - ",
                           "check hub bring-up (HUB_EN / HUB_CONNECT) and the ",
                           "device bring-up in firmware."},
                          label, timeout_us, shared_status.link_usb_20_state))
            return;
        end

        `uvm_info("USB_BASE_SEQ", $sformatf("%s ENABLED.", label), UVM_MEDIUM)
    endtask

    // -------------------------------------------------------------------------
    // Hub-composite enumeration, steps A / B / C.
    //
    // The hub-composite IP (ip_xxx_3511_hs_mem_compound_wrapper) presents an
    // on-chip 2-port hub with an embedded downstream device controller
    // (USBDC0). Bringing it to the configured state always takes the same
    // three steps, which every enumeration-based test was previously
    // reproducing verbatim:
    //
    //   A - enumerate the HUB itself at address 1
    //   B - bring up (or re-reset) hub downstream port 1, where USBDC0 sits
    //   C - enumerate USBDC0 at address 2
    //
    // The steps are exposed individually because some tests re-run B and C
    // after a disturbance (power-down, cable pull) without redoing A.
    // enumerate_hub_and_usbdc0() is the A -> B -> C convenience wrapper.
    //
    // suffix, when non-empty, is appended to every transfer label so a test
    // that enumerates more than once can tell the two passes apart in the log.
    //
    // with_get_config_readback selects whether step C issues the two optional
    // GET_CONFIGURATION transfers (a readback before SET_CONFIGURATION and a
    // verify after it). Set it to 0 for tests that only need the device
    // configured with the minimum number of EP0 transfers.
    //
    // IMPORTANT (VIP): usb_cfg.remote_device_cfg[0].device_address must be
    // mutated and agent_h.reconfigure(usb_cfg) called in lockstep with every
    // SET_ADDRESS. Otherwise the VIP's fixed_dev_ep_ustr_valid_ranges
    // constraint (device_address == dev_anchor.device_address) contradicts
    // do_control_xfer()'s WITH constraint and the next randomize() hits a
    // constraint-solver UVM_FATAL.
    // -------------------------------------------------------------------------

    // Step A: enumerate the HUB at address 1.
    //   GET_DESC(8)@0 -> SET_ADDRESS(1)@0 -> GET_DESC(18)/CFG9/CFG25/HUB9@1 ->
    //   SET_CONFIGURATION(1)@1.
    // On entry the VIP anchor must be 0; on exit it is left at 1.
    task hub_enum_stepA(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                        string suffix = "", bit no_queue_and_hold = 0);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (0),
            .label                ({"GET_DESC_DEV_addr0_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_DEV_addr0_hub", suffix}));
        usb_data_check_api.check_device_descriptor(.usb_item(last_ctrl_seq_item), 
                                                   .device_name("hub"));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h05),
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (0),
            .label                ({"SET_ADDRESS_1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"SET_ADDRESS_1_hub", suffix}));
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (1),
            .label                ({"GET_DESC_DEV_addr1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_DEV_addr1_hub", suffix}));
        usb_data_check_api.check_device_address(.usb_item(last_ctrl_seq_item), 
                                                .device_name("hub"), .expected_address(1));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0200),
            .windex               (16'h0000),
            .wlength              (16'h0009),
            .device_addr          (1),
            .label                ({"GET_DESC_CFG9_addr1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_CFG9_addr1_hub", suffix}));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0200),
            .windex               (16'h0000),
            .wlength              (16'h0019),
            .device_addr          (1),
            .label                ({"GET_DESC_CFG25_addr1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_CFG25_addr1_hub", suffix}));
        // NOTE: Expected to fail for (usb_cfg.speed != svt_usb_types::HS)
	//       unless MCU validation firmware overrides the descriptor
        usb_data_check_api.check_configuration_descriptor(.usb_item   (last_ctrl_seq_item),
                                                          .device_name("hub"));
        // Extract after the descriptor has been read in full and validated.
        // bmAttributes is byte 7 of the CONFIGURATION descriptor; D6 is Self-powered.
        if (last_ctrl_seq_item.payload_byte_count() > 7)
            hub_self_powered = last_ctrl_seq_item.payload.data[7][6];
        else
            `uvm_error("USB_BASE_SEQ",
                $sformatf("hub CONFIGURATION descriptor too short (%0d bytes)",
                          last_ctrl_seq_item.payload_byte_count()))

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h2900),
            .windex               (16'h0000),
            .wlength              (16'h0009),
            .device_addr          (1),
            .label                ({"GET_DESC_HUB9_addr1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_HUB9_addr1_hub", suffix}));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h09),
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (1),
            .label                ({"SET_CONFIG_1_hub", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"SET_CONFIG_1_hub", suffix}));

        `uvm_info("USB_BASE_SEQ", "Step A: HUB enumeration complete (addr 1).", UVM_MEDIUM)
    endtask

    // Step B: bring up (or re-reset) a hub downstream port.
    //   GetPortStatus -> ClearFeature(C_PORT_CONNECTION) ->
    //   SetFeature(PORT_RESET) -> ClearFeature(C_PORT_RESET).
    // SetFeature(PORT_RESET) drives a USB bus reset onto the device behind
    // that port, returning it to the Default state at address 0. On entry the
    // VIP anchor must be 1.
    //
    // port_num selects which hub downstream port to bring up. The compound IP
    // hub descriptor reports bNbrPorts = 2 (see usb_ep0_hub_descr.m.vhdl, HUB
    // DESCRIPTOR block) and C_NBDEV = 2, so:
    //   port 1 -> USBDC0 (dev0_axi, register base 0x2000_1000)
    //   port 2 -> USBDC1 (dev1_axi, register base 0x2001_0000)
    // The default of 1 preserves the behaviour of every pre-existing test.
    task hub_port_bringup_stepB(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                                string suffix = "", bit no_queue_and_hold = 0,
                                int port_num = 1);
        string p;
        p = $sformatf("_Port%0d", port_num);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h00),
            .wvalue               (16'h0000),
            .windex               (16'(port_num)),
            .wlength              (16'h0004),
            .device_addr          (1),
            .label                ({"GetPortStatus", p, suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GetPortStatus", p, suffix}));
        // At this point the device has just connected to the hub downstream
        // port and the port is powered, but no port feature has been cleared
        // yet. wPortStatus therefore has PORT_CONNECTION(bit0) and
        // PORT_POWER(bit8) set, and wPortChange has C_PORT_CONNECTION(bit0) set.

        do_control_xfer(

            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h01),
            .wvalue               (16'h0010),

            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (1),
            .label                ({"ClearFeature_C_PORT_CONNECTION", p, suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"ClearFeature_C_PORT_CONNECTION", p, suffix}));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h03),
            .wvalue               (16'h0004),
            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (1),
            .label                ({"SetFeature_PORT_RESET", p, suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"SetFeature_PORT_RESET", p, suffix}));
        #10us;

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::CLASS),
            .bm_request_type_recip(svt_usb_types::BMREQ_OTHER),
            .brequest_val         (8'h01),
            .wvalue               (16'h0014),
            .windex               (16'(port_num)),
            .wlength              (16'h0000),
            .device_addr          (1),
            .label                ({"ClearFeature_C_PORT_RESET", p, suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"ClearFeature_C_PORT_RESET", p, suffix}));
        #10us;

        `uvm_info("USB_BASE_SEQ",
            $sformatf("Step B: hub downstream port %0d brought up.", port_num), UVM_MEDIUM)
    endtask


    // Step C: enumerate USBDC0 (behind hub port 1) at address 2.
    //   GET_DESC(18)@0 -> GET_STATUS@0 -> SET_ADDRESS(2)@0 ->
    //   GET_DESC(18)@2 -> [GET_CONFIG@2 ->] SET_CONFIG@2 [-> GET_CONFIG@2].
    // USBDC0 responds at address 0 after the step B port reset. On completion
    // the VIP anchor is left at 2 (USBDC0).
    // assign_address selects the USB device address assigned to this device
    // by SET_ADDRESS (default 2, matching every pre-existing single-device
    // caller). A dual-device test enumerating BOTH embedded controllers on the
    // same bus must give them DISTINCT addresses (e.g. USBDC0=2, USBDC1=3):
    // two devices cannot share one address on a single USB bus.
    //
    // Every control transfer in this step is status-checked via
    // wait_and_check_xfer(): an ABORTED transfer here means the device never
    // answered the SETUP, which leaves it un-addressed or un-configured and
    // makes every later stage of the test meaningless. Without these checks
    // a completely dead device still produced a "USBDC0 enumeration complete"
    // log line and zero errors, because NOTIFY_USB_TRANSFER_ENDED fires on
    // ABORTED just as it does on success. The IN transfers additionally
    // require their full expected payload, so a data check can never run
    // against an empty payload and pass by accident.
    task usbdc0_enum_stepC(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                           string suffix = "", bit with_get_config_readback = 1,
                           bit no_queue_and_hold = 0, int unsigned device_idx=0,
                           bit [6:0] assign_address = 7'd2);
        bit xfer_fail;

        // Reset VIP anchor to addr=0 before addressing the freshly port-reset
        // USBDC0 - see the constraint note in this block's header comment.

        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_BASE_SEQ",
            "Reset host agent remote device_address=0 before enumerating USBDC0.",
            UVM_HIGH)

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (0),
            .label                ({"GET_DESC_DEV_addr0", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        // 18-byte DEVICE descriptor read at the default address. This is the
        // very first SETUP the device sees after the port reset; if it aborts,
        // the device controller is not servicing EP0 at all and nothing after
        // this point can succeed.
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ({"GET_DESC_DEV_addr0", suffix}),
                            .min_payload_bytes(18),
                            .fail             (xfer_fail));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h00),
            .wvalue               (16'h0000),
            .windex               (16'h0000),
            .wlength              (16'h0002),
            .device_addr          (0),
            .label                ({"GET_STATUS_addr0", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        // 2-byte device status word.
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ({"GET_STATUS_addr0", suffix}),
                            .min_payload_bytes(2),
                            .fail             (xfer_fail));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h05),
            .wvalue               (16'(assign_address)),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (0),
            .label                ({"SET_ADDRESS_2", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        // No data stage, so no payload requirement - but the status stage
        // must be accepted, otherwise the device never commits the new
        // address and every transfer below is sent to an address nobody
        // answers on.
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ({"SET_ADDRESS_2", suffix}),
                            .min_payload_bytes(0),
                            .fail             (xfer_fail));
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = assign_address;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (int'(assign_address)),
            .label                ({"GET_DESC_DEV_addr2", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        // First transfer at the newly assigned address: proves the device
        // accepted SET_ADDRESS and is answering on the new address with a
        // full 18-byte descriptor.
        wait_and_check_xfer(.agent_h          (host_agent_h),
                            .label            ({"GET_DESC_DEV_addr2", suffix}),
                            .min_payload_bytes(18),
                            .fail             (xfer_fail));
        // Only run the address check when the transfer itself succeeded. The
        // check reads the committed address out of RTL and would otherwise
        // report a pass on the strength of a transfer that moved no data at
        // all, which is how an entirely failed enumeration used to be logged
        // as successful.
        if (!xfer_fail)
            usb_data_check_api.check_device_address(.usb_item(last_ctrl_seq_item),
                                                    .device_name($sformatf("dev%0d", device_idx)),
                                                    .expected_address(int'(assign_address)));

        if (with_get_config_readback) begin
            do_control_xfer(
                .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
                .bm_request_type_type (svt_usb_types::STANDARD),
                .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
                .brequest_val         (8'h08),
                .wvalue               (16'h0000),
                .windex               (16'h0000),
                .wlength              (16'h0001),
                .device_addr          (int'(assign_address)),
                .label                ({"GET_CONFIG_addr2", suffix}),
                .usb_cfg              (usb_cfg),
                .no_queue_and_hold    (no_queue_and_hold));
            // 1-byte bConfigurationValue readback before SET_CONFIGURATION.
            wait_and_check_xfer(.agent_h          (host_agent_h),
                                .label            ({"GET_CONFIG_addr2", suffix}),
                                .min_payload_bytes(1),
                                .fail             (xfer_fail));
        end

        // The device only arms its non-control endpoints once it is
        // configured, so an aborted SET_CONFIGURATION silently disables every
        // bulk/iso stage of the test that follows.
        //
        // This and the GET_CONFIG_verify below are issued back to back with
        // no delay, which is what makes the shared-notification race in
        // wait_xfer_done() observable. Both therefore use the forked
        // do_control_xfer_and_wait() form - see its header for the details.
        do_control_xfer_and_wait(
            .agent_h              (host_agent_h),
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h09),
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (int'(assign_address)),
            .label                ({"SET_CONFIG_1", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold),
            .min_payload_bytes    (0),
            .fail                 (xfer_fail));

        if (with_get_config_readback) begin
            // 1-byte bConfigurationValue readback confirming the device
            // really entered the Configured state. Forked form: this is the
            // transfer that reported ABORTED/results_status=0x0 on every
            // controller whose SET_CONFIGURATION was immediately followed by
            // this read-back, while the firmware log showed the request being
            // serviced normally ~3.4 us later.
            do_control_xfer_and_wait(
                .agent_h              (host_agent_h),
                .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
                .bm_request_type_type (svt_usb_types::STANDARD),
                .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
                .brequest_val         (8'h08),
                .wvalue               (16'h0000),
                .windex               (16'h0000),
                .wlength              (16'h0001),
                .device_addr          (int'(assign_address)),
                .label                ({"GET_CONFIG_verify", suffix}),
                .usb_cfg              (usb_cfg),
                .no_queue_and_hold    (no_queue_and_hold),
                .min_payload_bytes    (1),
                .fail                 (xfer_fail));
        end


        `uvm_info("USB_BASE_SEQ", "Step C: USBDC0 enumeration complete (addr 2).", UVM_MEDIUM)
    endtask

    // A -> B -> C: full bring-up from an un-enumerated bus to USBDC0
    // configured at address 2.
    task enumerate_hub_and_usbdc0(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                                  string suffix = "", bit with_get_config_readback = 1,
                                  bit no_queue_and_hold = 0);
        hub_enum_stepA(
            .host_agent_h     (host_agent_h),
            .usb_cfg          (usb_cfg),
            .suffix           (suffix),
            .no_queue_and_hold(no_queue_and_hold));
        hub_port_bringup_stepB(
            .host_agent_h     (host_agent_h),
            .usb_cfg          (usb_cfg),
            .suffix           (suffix),
            .no_queue_and_hold(no_queue_and_hold),
            .port_num         (1));
        usbdc0_enum_stepC(
            .host_agent_h            (host_agent_h),
            .usb_cfg                 (usb_cfg),
            .suffix                  (suffix),
            .with_get_config_readback(with_get_config_readback),
            .no_queue_and_hold       (no_queue_and_hold));
    endtask

    // -------------------------------------------------------------------------
    // USBDC1 (dev1) variants of steps B/C and the A -> B -> C wrapper.
    //
    // USBDC1 is the second embedded device controller of the compound IP. It
    // sits behind hub downstream port 2 (bNbrPorts = 2, C_NBDEV = 2) and its
    // register/DMA apertures are at 0x2001_0000 / 0x2001_0100 - see the
    // USB_DEV1_* macros in src/integration/test_suites/libs/usb/usb.h.
    //
    // The bus-level enumeration is identical to USBDC0's: the port reset in
    // step B leaves the device answering at address 0, and the host then
    // assigns it address 2. Only the hub port index differs, so these wrappers
    // just re-target step B and reuse step C verbatim. Device-side firmware
    // targets USBDC1 by being compiled with -DUSB_DEV_SEL=1.
    // -------------------------------------------------------------------------

    // Step B for USBDC1: bring up hub downstream port 2.
    task hub_port_bringup_stepB_dev1(svt_usb_agent host_agent_h,
                                     svt_usb_configuration usb_cfg,
                                     string suffix = "", bit no_queue_and_hold = 0);
        hub_port_bringup_stepB(
            .host_agent_h     (host_agent_h),
            .usb_cfg          (usb_cfg),
            .suffix           (suffix),
            .no_queue_and_hold(no_queue_and_hold),
            .port_num         (2));
    endtask

    // Step C for USBDC1: identical EP0 sequence to USBDC0's step C. Kept as a
    // separate name so a dev1 test reads symmetrically with a dev0 test.
    task usbdc1_enum_stepC(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                           string suffix = "", bit with_get_config_readback = 1,
                           bit no_queue_and_hold = 0);
        usbdc0_enum_stepC(
            .host_agent_h            (host_agent_h),
            .usb_cfg                 (usb_cfg),
            .suffix                  (suffix),
            .with_get_config_readback(with_get_config_readback),
            .no_queue_and_hold       (no_queue_and_hold),
            .device_idx              (1));
    endtask

    // A -> B(port 2) -> C: full bring-up from an un-enumerated bus to USBDC1
    // configured at address 2.
    task enumerate_hub_and_usbdc1(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                                  string suffix = "", bit with_get_config_readback = 1,
                                  bit no_queue_and_hold = 0);
        hub_enum_stepA(
            .host_agent_h     (host_agent_h),
            .usb_cfg          (usb_cfg),
            .suffix           (suffix),
            .no_queue_and_hold(no_queue_and_hold));
        hub_port_bringup_stepB(
            .host_agent_h     (host_agent_h),
            .usb_cfg          (usb_cfg),
            .suffix           (suffix),
            .no_queue_and_hold(no_queue_and_hold),
            .port_num         (2));
        usbdc1_enum_stepC(
            .host_agent_h            (host_agent_h),
            .usb_cfg                 (usb_cfg),
            .suffix                  (suffix),
            .with_get_config_readback(with_get_config_readback),
            .no_queue_and_hold       (no_queue_and_hold));
    endtask


    // -------------------------------------------------------------------
    // do_data_xfer
    //
    // Generic data-stage transfer: builds one svt_usb_transfer of the given
    // xfer_kind (svt_usb_transfer::BULK_OUT_TRANSFER, BULK_IN_TRANSFER,
    // ISOCHRONOUS_OUT_TRANSFER, ISOCHRONOUS_IN_TRANSFER, ...), issues it on
    // p_sequencer.xfer_sequencer and waits for completion.
    //
    // Arguments:
    //   agent_h            - agent whose prot.NOTIFY_USB_TRANSFER_ENDED is
    //                        awaited (see wait_xfer_done).
    //   usb_cfg            - assigned onto req.cfg before randomize() when
    //                        non-null, so the item picks up the caller's
    //                        current configuration. Pass null to leave the
    //                        item on whatever cfg the VIP gives it.
    //   xfer_kind          - the svt_usb_transfer xfer_type to constrain to.
    //                        Typed as int so a caller can pass any of the
    //                        enum literals directly.
    //   device_addr/ep_num - USB device address and endpoint number.
    //   byte_count         - payload_intended_byte_count.
    //   ep_anchor_idx      - the ep_idx argument of fix_anchors(0, N, 0).
    //                        This is the VIP endpoint-config array index, not
    //                        the USB endpoint number, and it differs per
    //                        direction/endpoint - pass exactly what the
    //                        original inline block used.
    //   label              - used in the completion logs and passed to
    //                        wait_xfer_done().
    //   req                - the transfer handle, returned so the caller can
    //                        inspect req.payload.data[] afterwards (IN
    //                        transfers) or otherwise scoreboard the item.
    //   obj_name           - UVM object name for the transfer. Defaults to
    //                        {label, "_req"} when left empty.
    //   payload_data       - when non-empty, the transfer is switched to the
    //                        user-defined payload algorithm and these bytes
    //                        are written into req.payload.data[] after
    //                        randomize(). Leave empty for IN transfers and
    //                        for OUT transfers that want VIP-generated data.
    //   no_zero_length_end - adds aligned_transfer_ends_with_zero_length==0.
    //   single_isoc_txn    - adds first_isoc_transaction==1 and
    //                        last_isoc_transaction==1, i.e. the transfer is a
    //                        self-contained isochronous transaction.
    //                        no_zero_length_end and single_isoc_txn are
    //                        mutually exclusive: SystemVerilog cannot extend
    //                        an inline constraint block conditionally, so each
    //                        supported combination is a separate randomize()
    //                        branch below and no call site needs both.
    //   fork_wait          - when 1, wait_xfer_done() is forked alongside
    //                        finish_item() so a short transfer that completes
    //                        before the calling thread resumes cannot make
    //                        the wait miss the event. Set to 0 only where the
    //                        original code deliberately waited sequentially.
    //   timeout_us         - ceiling handed to wait_xfer_done() for this
    //                        transfer. The 2000 us default matches
    //                        wait_xfer_done()'s own default and is safe at
    //                        high speed, where the frame period is 125 us.
    //                        FULL-SPEED callers must raise it: the FS frame
    //                        period is 1 ms, so one FS interrupt or
    //                        isochronous transfer of a few hundred bytes can
    //                        cost more than 2000 us of simulation time on a
    //                        perfectly healthy bus and the default then
    //                        expires on a transfer that was about to
    //                        complete. Measured reference: a 64-byte FS
    //                        INTERRUPT IN loopback in
    //                        caliptra_ss_usb_fs_dev_int_iso_mix took about
    //                        2019 us end to end. Raise this per call site
    //                        instead of raising the global default, so the
    //                        guard stays tight for the high-speed tests.
    // -------------------------------------------------------------------
    task do_data_xfer(
        input  svt_usb_agent         agent_h,
        input  svt_usb_configuration usb_cfg,
        input  int                   xfer_kind,
        input  int                   device_addr,
        input  int                   ep_num,
        input  int unsigned          byte_count,
        input  int                   ep_anchor_idx,
        input  string                label,
        output svt_usb_transfer      req,
        input  string                obj_name           = "",
        input  bit [7:0]             payload_data[]     = {},
        input  bit                   no_zero_length_end = 0,
        input  bit                   single_isoc_txn    = 0,
        input  bit                   fork_wait          = 1,
        input  int unsigned          timeout_us         = 2000
    );
        if (no_zero_length_end && single_isoc_txn)
            `uvm_fatal("USB_BASE_SEQ",
                $sformatf({"do_data_xfer(%s): no_zero_length_end and ",
                           "single_isoc_txn cannot both be set"}, label))

        req = svt_usb_transfer::type_id::create(
                  (obj_name == "") ? {label, "_req"} : obj_name);
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null)
            req.cfg = usb_cfg;
        if (payload_data.size() > 0) begin
            // Deterministic caller-supplied payload instead of the VIP's
            // seed-based generator, so the DUT-side check can predict data.
            req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
            req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        end
        req.fix_anchors(0, ep_anchor_idx, 0);

        if (no_zero_length_end) begin
            if (!req.randomize() with {
                    xfer_type                              == xfer_kind;
                    device_address                         == device_addr;
                    endpoint_number                        == ep_num;
                    payload_intended_byte_count            == byte_count;
                    aligned_transfer_ends_with_zero_length == 0;
                }) begin
                `uvm_fatal("USB_BASE_SEQ", $sformatf("randomize failed for %s", label))
            end
        end
        else if (single_isoc_txn) begin
            if (!req.randomize() with {
                    xfer_type                   == xfer_kind;
                    device_address              == device_addr;
                    endpoint_number             == ep_num;
                    payload_intended_byte_count == byte_count;
                    first_isoc_transaction      == 1;
                    last_isoc_transaction       == 1;
                }) begin
                `uvm_fatal("USB_BASE_SEQ", $sformatf("randomize failed for %s", label))
            end
        end
        else if (!req.randomize() with {
                xfer_type                   == xfer_kind;
                device_address              == device_addr;
                endpoint_number             == ep_num;
                payload_intended_byte_count == byte_count;
            }) begin
            `uvm_fatal("USB_BASE_SEQ", $sformatf("randomize failed for %s", label))
        end

        foreach (payload_data[i])
            req.payload.data[i] = payload_data[i];

        if (fork_wait) begin
            fork
                begin
                    finish_item(req, -1);
                    `uvm_info("USB_BASE_SEQ",
                        $sformatf("DATA %s issued (addr=%0d ep=%0d bytes=%0d).",
                                  label, device_addr, ep_num, byte_count), UVM_LOW)
                end
                begin
                    wait_xfer_done(.agent_h(agent_h), .label(label),
                                   .timeout_us(timeout_us));
                end
            join
        end
        else begin
            finish_item(req, -1);
            wait_xfer_done(.agent_h(agent_h), .label(label),
                           .timeout_us(timeout_us));
        end
    endtask

endclass


`endif // CALIPTRA_SS_USB_BASE_SEQUENCE_SV
