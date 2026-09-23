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
//   - pre_start()/post_start(): raise/drop the starting phase's objection
//     when this sequence has no parent sequence (i.e. it was start()'d
//     directly as a top-level sequence rather than nested inside another).
//   - resolve_host_agent(): cast p_sequencer's parent component to
//     svt_usb_agent (every sequence needs this to reach agent_h.prot for
//     wait_xfer_done() and agent_h.reconfigure() after a SET_ADDRESS).
//   - resolve_shared_status(): fetch the svt_usb_status object the link FSM
//     writes, via p_sequencer.get_shared_status(this).
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

    // Set by wait_for_link_enabled() when its timeout expired before the
    // link reached ENABLED. Cleared at every entry to that task. Sequences
    // that must abort the rest of their body on a failed link-up read this
    // instead of duplicating their own timeout fork.
    bit link_wait_timed_out = 1'b0;

    function new(string name = "caliptra_ss_usb_base_sequence");
        super.new(name);

        if(uvm_config_db#(caliptra_ss_usb_data_check_api)::get(null, "uvm_test_top", 
                                                              "usb_data_check_api", 
                                                              usb_data_check_api) != 1) begin
            `uvm_fatal("USB_BASE_SEQ", "impossible to get usb_data_check_api")
        end
    endfunction

    // -------------------------------------------------------------------
    // pre_start / post_start
    //
    // Raise/drop the starting phase's objection, but only when this
    // sequence has no parent sequence - i.e. it was start()'d directly as
    // a top-level sequence from a test, rather than nested inside another
    // sequence (which would already be holding its own objection).
    // -------------------------------------------------------------------
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
        // no_queue_and_hold forces queue_and_hold==0 so the VIP issues the
        // transfer immediately instead of holding it in the queue. Needed by
        // tests that pull the cable mid-stream and must not leave a held
        // transfer behind (see caliptra_ss_usb_hs_dev_disconnect_sequence).
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
    // -------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_BASE_SEQ",
            $sformatf("Transfer %s completed.", label), UVM_LOW)
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
    task usbdc0_enum_stepC(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg,
                           string suffix = "", bit with_get_config_readback = 1,
                           bit no_queue_and_hold = 0, int unsigned device_idx=0);
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
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_DEV_addr0", suffix}));

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
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_STATUS_addr0", suffix}));

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h05),
            .wvalue               (16'h0002),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (0),
            .label                ({"SET_ADDRESS_2", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"SET_ADDRESS_2", suffix}));
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd2;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0100),
            .windex               (16'h0000),
            .wlength              (16'h0012),
            .device_addr          (2),
            .label                ({"GET_DESC_DEV_addr2", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"GET_DESC_DEV_addr2", suffix}));
        usb_data_check_api.check_device_address(.usb_item(last_ctrl_seq_item), 
                                                .device_name($sformatf("dev%0d", device_idx)), 
                                                .expected_address(2));

        if (with_get_config_readback) begin
            do_control_xfer(
                .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
                .bm_request_type_type (svt_usb_types::STANDARD),
                .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
                .brequest_val         (8'h08),
                .wvalue               (16'h0000),
                .windex               (16'h0000),
                .wlength              (16'h0001),
                .device_addr          (2),
                .label                ({"GET_CONFIG_addr2", suffix}),
                .usb_cfg              (usb_cfg),
                .no_queue_and_hold    (no_queue_and_hold));
            wait_xfer_done(.agent_h(host_agent_h), .label({"GET_CONFIG_addr2", suffix}));
        end

        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h09),
            .wvalue               (16'h0001),
            .windex               (16'h0000),
            .wlength              (16'h0000),
            .device_addr          (2),
            .label                ({"SET_CONFIG_1", suffix}),
            .usb_cfg              (usb_cfg),
            .no_queue_and_hold    (no_queue_and_hold));
        wait_xfer_done(.agent_h(host_agent_h), .label({"SET_CONFIG_1", suffix}));

        if (with_get_config_readback) begin
            do_control_xfer(
                .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
                .bm_request_type_type (svt_usb_types::STANDARD),
                .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
                .brequest_val         (8'h08),
                .wvalue               (16'h0000),
                .windex               (16'h0000),
                .wlength              (16'h0001),
                .device_addr          (2),
                .label                ({"GET_CONFIG_verify", suffix}),
                .usb_cfg              (usb_cfg),
                .no_queue_and_hold    (no_queue_and_hold));
            wait_xfer_done(.agent_h(host_agent_h), .label({"GET_CONFIG_verify", suffix}));
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
        input  bit                   fork_wait          = 1
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
                    wait_xfer_done(.agent_h(agent_h), .label(label));
                end
            join
        end
        else begin
            finish_item(req, -1);
            wait_xfer_done(.agent_h(agent_h), .label(label));
        end
    endtask

endclass


`endif // CALIPTRA_SS_USB_BASE_SEQUENCE_SV
