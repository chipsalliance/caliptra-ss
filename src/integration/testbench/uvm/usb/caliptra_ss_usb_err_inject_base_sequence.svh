// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_ERR_INJECT_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_ERR_INJECT_BASE_SEQUENCE_SV

// =============================================================================
// Shared base for the USB error-injection sequences.
//
// WHAT THESE TESTS ARE STIMULUS FOR
//
// cp_errortype of usb_transfer_outcome_cg (src/usb/coverage/usb_dev_ep_cov.sv),
// which samples pie_errortype at end of transfer whenever pie_error is set.
// Before these tests only two of its bins were ever hit - timeout (0x6) and
// sent_received_NAK (0x9) - because nothing in the regression ever corrupted a
// packet. Everything else in the IP's error taxonomy sat at zero.
//
// THE CODE LEGEND IS RTL-DERIVED, NOT GUESSED
//
// pie_errortype is 4 bits wide and its encoding is NOT in any specification.
// It comes from the SetError procedure of
// third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_pie.m.vhdl.
// That procedure was commented out by a lint fix and its body inlined at the
// call sites ("Removed procedure and moved code explicitly in design to fix
// lint error"), so the surviving comment block at lines 1901-1918 is the
// legend and the live "errortype <= ..." assignments are the authority for
// which codes the design can still produce:
//
//   code  name                         live sites  reachable by this test set
//   0x0   ERROR_NO_ERROR               reset only  no, see below
//   0x1   ERROR_PID_ENCODING           4           yes - pid sequence
//   0x2   ERROR_PID_UNKNOWN            9           yes - pid sequence
//   0x3   ERROR_PACKET_UNEXPECTED      7           yes - sequence sequence
//   0x4   ERROR_TOKEN_CRC              2           yes - crc sequence
//   0x5   ERROR_DATA_CRC               1           yes - crc sequence
//   0x6   ERROR_TIMEOUT                5           already covered
//   0x7   ERROR_BABBLE                 0           NO - not implemented
//   0x8   ERROR_TR_EOP                 4           yes - length sequence
//   0x9   ERROR_SENT_RECEIVED_NAK      4           already covered
//   0xA   ERROR_SENT_STALL             3           yes - stall sequence
//   0xB   ERROR_OVERRUN                2           yes - length sequence
//   0xC   ERROR_SENT_EMPTYPACK         0           NO - not implemented
//   0xD   ERROR_BITSTUFF_ERROR         0           NO - not implemented
//   0xE   ERROR_SYNC_ERROR             0           NO - not implemented
//   0xF   ERROR_DATA_IGNORED_WRONG_DATA01  1       yes - sequence sequence
//
// 0x7, 0xC, 0xD and 0xE have NO live assignment anywhere in usb_pie: the only
// occurrence of each is inside the dead commented-out procedure. They are
// therefore unreachable by any stimulus whatsoever and have been removed from
// the coverpoint rather than chased or waived. 0x0 is excluded for a different
// reason: the coverpoint is qualified "iff (xfer_done_for_me && xfer_error)",
// so the no-error code can never coincide with a sample.
//
// Note in particular that 0xD and 0xE are the bit-stuffing and SYNC codes.
// Injecting svt_usb_packet_exception BIT_STUFF_ERROR or SYNC_ERROR does
// corrupt the wire, but this PIE never reports either through pie_errortype,
// so those injections cannot close a bin and are deliberately not used.
//
// THE VIP EXCEPTION FIELD MODEL
//
// Verified against the generated class reference at
// /pkg/synopsys-designware-/vip_collection/vip/svt/usb_svt/latest/doc/
//   class_ref/usb_svt_uvm_class_reference/html/exception/
// and against the three in-repo sequences that already use the framework
// (caliptra_ss_usb_ocp_packet_observer_selftest_sequence,
//  caliptra_ss_usb_ocp_stall_base_sequence,
//  caliptra_ss_usb_ocp_directed_packet_sequence).
//
// error_kind IS the top-level selector in every one of the four exception
// classes, and it then enables exactly one sub-field:
//
//   error_kind == CRC_ERROR       -> crc_error      (CRC5_ERROR, CRC16_ERROR, ...)
//   error_kind == PHYSICAL_ERROR  -> physical_error (SYNC_ERROR, EOP_ERROR,
//                                                    BIT_STUFF_ERROR,
//                                                    BYTE_BOUNDARY_ERROR,
//                                                    PRE_PID_ERROR, RX_ERROR)
//   error_kind == LENGTH_ERROR    -> length_error   (SHORT_PACKET_ERROR,
//                                                    LONG_PACKET_ERROR, ...)
//   error_kind == FRAMING_ERROR   -> framing_error  (SS only)
//   error_kind == DATA_ERROR      -> data_error     (SS only)
//   error_kind == PACKET_FIELD_ERROR / RESERVED_FIELD_ERROR
//                                 -> field_id
//
// So SYNC_ERROR, EOP_ERROR, BIT_STUFF_ERROR, BYTE_BOUNDARY_ERROR and RX_ERROR
// are NOT error_kind values - they are physical_error_enum members and are
// only reachable with error_kind == PHYSICAL_ERROR. RX_ERROR is additionally
// documented as "only for reporting purpose" and cannot be injected at all.
//
// Two idioms below are taken verbatim from the working in-repo code and must
// be kept:
//   no_exception == 0  - without it randomization is free to decide that no
//                        error is to be injected after all.
//   recognized   == 0  - marks the exception as GENERATED by us rather than
//                        RECOGNISED in a received packet.
// The null-guard before allocating exception_list is from the same source: the
// list is shared per transaction and may already exist.
//
// WHERE THE EXCEPTION ATTACHES
//
// A svt_usb_packet_exception attaches to a svt_usb_PACKET, never to a
// svt_usb_transfer: svt_usb_transfer.exception_list is a
// svt_usb_transfer_exception_list holding a different class entirely, and the
// packet exception additionally requires its cfg and xact back-references to
// be populated before inject() will run. The corrupted stimulus is therefore
// driven by inject_error_packet() below, which delegates to
// caliptra_ss_usb_err_inject_packet_sequence on the packet sequencer. That
// file's header carries the full analysis.
// =============================================================================

virtual class caliptra_ss_usb_err_inject_base_sequence
    extends caliptra_ss_usb_base_sequence;

    // Device address USBDC0 is left at by usbdc0_enum_stepC.
    localparam int USBDC0_ADDR = 2;

    // EP1 is the bulk pair the firmware arms; ep_anchor_idx 1 is its entry in
    // the endpoint_cfg[] layout the *_err_* tests declare. Same convention as
    // caliptra_ss_usb_hs_dev_bulk_out_sequence.
    localparam int EP1_BULK          = 1;
    localparam int EP1_ANCHOR        = 1;

    // One HS bulk max packet. Deliberately exactly max-packet so a LENGTH
    // error that elongates the packet crosses the wMaxPacketSize boundary,
    // which is what the overrun path keys on.
    localparam int unsigned HS_BULK_MAX_PACKET = 512;

    // Settling delays. Same values as the other HS device sequences: 20 us
    // after link-up for the firmware EP0 re-arm, 10 us after enumeration.
    localparam realtime LINK_SETTLE_DELAY = 20us;
    localparam realtime ENUM_SETTLE_DELAY = 10us;

    // Time allowed for the firmware to observe the error and for the PIE to
    // retire the transfer before the sequence moves on. The coverage sample
    // happens on the endtransfer strobe, so this only has to be long enough
    // for the transaction to actually end.
    localparam realtime ERROR_SETTLE_DELAY = 50us;

    // Upper bound on how long to wait for a corrupted packet to complete.
    // A malformed packet may never be answered - a bad-CRC data packet gets no
    // handshake at all - so the injection start() must not be able to hang the
    // test. Same guard style as caliptra_ss_usb_ocp_persistent_stall_sequence.
    localparam realtime INJECT_RESPONSE_BOUND = 200us;

    // Opcode and ack timeout for the MCU STOP handshake called at the end of
    // every error-injection body. The opcode must match MCU_COMMAND_STOP in
    // caliptra_ss_usb_legacy_ep0_observer_if and USB_LEGACY_EP0_COMMAND_STOP
    // in libs/usb/usb.h - all three are the same number and must be changed
    // together.
    localparam bit [3:0] MCU_STOP_OPCODE  = 4'h7;
    localparam realtime  MCU_STOP_ACK_MAX = 200us;


    // Tag used only in log messages, to name the injection leg of the sequence
    // so a waveform or log can be lined up against the three-leg structure
    // (clean, corrupted, clean).
    protected string inject_on_label = "";

    function new(string name = "caliptra_ss_usb_err_inject_base_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Common bring-up: link, SOF, settle, enumerate hub + USBDC0.
    //
    // Every error-injection sequence needs the device configured before it can
    // address a bulk endpoint, and the hub must be enumerated first or the hub
    // hardware never forwards traffic to USBDC0 at all - see the root-cause
    // note in caliptra_ss_usb_hs_dev_bulk_out_sequence.
    //
    // Returns 0 when bring-up failed, so the caller can abandon the body
    // instead of injecting into a bus that never came up.
    // -------------------------------------------------------------------------
    protected task err_inject_bringup(output svt_usb_agent         host_agent_h,
                                      output svt_usb_configuration usb_cfg,
                                      input  string                msg_id,
                                      output bit                   ok);
        svt_usb_status shared_status;

        ok            = 1'b0;
        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(msg_id,
                "Link never reached ENABLED; abandoning error injection.")
            return;
        end

        start_sof_generation();
        #LINK_SETTLE_DELAY;

        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        #ENUM_SETTLE_DELAY;

        ok = 1'b1;
    endtask

    // -------------------------------------------------------------------------
    // A clean reference bulk OUT.
    //
    // Issued before and after the corrupted transfer in every sequence. It
    // serves two purposes: it proves the endpoint was alive before the error
    // (so a missing error bin cannot be explained away by a dead endpoint),
    // and when issued afterwards it proves the controller RECOVERED rather
    // than wedging, which is the real point of an error-injection test.
    //
    // -------------------------------------------------------------------------
    protected task do_clean_reference_xfer(svt_usb_agent         host_agent_h,
                                           svt_usb_configuration usb_cfg,
                                           string                label,
                                           string                msg_id);
        svt_usb_transfer req;
        bit [7:0]        data[];

        data = new[HS_BULK_MAX_PACKET];
        foreach (data[i]) data[i] = i[7:0];

        `uvm_info(msg_id,
            $sformatf("%s: clean reference BULK OUT of %0d bytes to addr %0d EP%0d.",
                      label, HS_BULK_MAX_PACKET, USBDC0_ADDR, EP1_BULK), UVM_LOW)

        do_data_xfer(
            .agent_h            (host_agent_h),
            .usb_cfg            (usb_cfg),
            .xfer_kind          (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr        (USBDC0_ADDR),
            .ep_num             (EP1_BULK),
            .byte_count         (HS_BULK_MAX_PACKET),
            .ep_anchor_idx      (EP1_ANCHOR),
            .label              (label),
            .req                (req),
            .payload_data       (data),
            .no_zero_length_end (1));
    endtask

    // -------------------------------------------------------------------------
    // Send one corrupted packet on the packet sequencer.
    //
    // Shared by the CRC, PID, length and toggle sequences, which differ only in
    // which error_kind / sub-field pair they pin. The sub-field arguments are
    // passed as their own enum types so a wrong-class value cannot be supplied
    // by mistake.
    //
    // WHY THIS IS A PACKET AND NOT A TRANSFER
    //
    // An earlier version of this helper attached a svt_usb_packet_exception to
    // svt_usb_transfer.exception_list. That crashed inside the VIP with a null
    // object access at svt_usb_packet_exception.svp line 9846, for two reasons:
    //   - svt_usb_transfer.exception_list is a svt_usb_transfer_exception_list,
    //     which holds a different exception class that has no crc_error /
    //     physical_error / length_error / field_id members at all.
    //   - svt_usb_packet_exception requires its cfg AND xact back-references to
    //     be populated, with xact being a svt_usb_packet. inject() dereferences
    //     xact.
    // See the header of caliptra_ss_usb_err_inject_packet_sequence.svh for the
    // full write-up and the two in-repo precedents this follows.
    //
    // The corrupt packet is addressed at the same device and endpoint the clean
    // reference transfers use, so the PIE decodes it in the same context.
    //
    // SEQUENCING ERRORS TAKE NO EXCEPTION
    //
    // Clearing attach_exception sends the packet exactly as built. That is the
    // only way to express an error that is a matter of WHEN a well formed
    // packet arrives rather than HOW it is formed - the VIP has no error_kind
    // for that case, and its valid_ranges constraint
    // (sverilog/src/com/svt_usb_packet_exception.svp:3163) restricts a DATA
    // packet to {CRC_ERROR, PHYSICAL_ERROR, ILLEGAL_DATA_PID_ERROR,
    // PID_CHECK_ERROR, LENGTH_ERROR, NO_OP_ERROR} anyway.
    //
    // LENGTH ERRORS NEED A NON-ZERO byte_offset
    //
    // byte_offset is the number of bytes a LENGTH_ERROR adds or removes, and
    // valid_ranges only bounds it as >= 0, so an unpinned solve may legally
    // pick 0 and inject nothing. len_byte_offset supplies it explicitly.
    // -------------------------------------------------------------------------
    protected task inject_error_packet(
        svt_usb_configuration                         usb_cfg,
        string                                        msg_id,
        svt_usb_packet::pid_name_enum                 pid,
        int unsigned                                  byte_count,
        svt_usb_packet_exception::error_kind_enum     kind,
        bit                                           use_crc,
        svt_usb_packet_exception::crc_error_enum       crc_sel,
        bit                                           use_phys,
        svt_usb_packet_exception::physical_error_enum  phys_sel,
        bit                                           use_len,
        svt_usb_packet_exception::length_error_enum    len_sel,
        bit                                           use_field = 1'b0,
        svt_usb_packet_exception::field_id_enum        field_sel =
            svt_usb_packet_exception::PID_NAME,
        bit [31:0]                                    field_value = 32'h0,
        bit                                           attach_exception = 1'b1,
        int unsigned                                  len_byte_offset = 1);

        caliptra_ss_usb_err_inject_packet_sequence pkt_seq;
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;
        bit [7:0]                                  payload[$];
        bit                                        sent;
        bit                                        is_data_pkt;

        if (usb_cfg == null) begin
            `uvm_error(msg_id,
                "No USB configuration available; nothing injected.")
            return;
        end

        is_data_pkt = (pid == svt_usb_packet::DATA0) ||
                      (pid == svt_usb_packet::DATA1);

        // A DATA packet driven bare on the packet sequencer, with no OUT
        // token of its own immediately before it, is not recognised by the
        // PIE as the start of a new transaction - it simply trails the
        // previous transaction's DATA phase with no intervening token or
        // handshake. Confirmed from env.host_agent.link_mon.20.TX.pkt_trace:
        // the corrupted/out-of-turn DATA packet showed up back-to-back after
        // the prior clean DATA0 under a single earlier OUT token, and
        // pie_errortype never reported the target code for any of the five
        // sequences that inject a bare DATA packet this way (data_crc,
        // short_pkt, long_pkt, pid_illegal, toggle). The two PASSING
        // inject_error_packet() users (token_crc, pid_check) are unaffected
        // because their corrupted item is itself a TOKEN, which legitimately
        // starts its own transaction. Sending a directed OUT token here, with
        // no exception attached, puts the PIE into the data phase it expects
        // before the DATA packet (clean or corrupted) arrives - this is the
        // fix caliptra_ss_usb_hs_dev_err_sequence_sequence's header already
        // called out as the next step if the toggle bin stayed open.
        if (is_data_pkt) begin
            tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
                "tok_seq");
            tok_seq.pid                  = svt_usb_packet::OUT;
            tok_seq.device_address       = 7'(USBDC0_ADDR);
            tok_seq.endpoint_number      = 4'(EP1_BULK);
            tok_seq.payload_bytes.delete();
            tok_seq.packet_configuration = usb_cfg;
            tok_seq.attach_exception     = 1'b0;
            tok_seq.msg_id               = msg_id;

            `uvm_info(msg_id,
                $sformatf({"%s: sending a directed OUT token to addr %0d ep ",
                           "%0d so the PIE is in its data phase when the ",
                           "%s packet below arrives."},
                          inject_on_label, USBDC0_ADDR, EP1_BULK, pid.name()),
                UVM_LOW)

            tok_seq.start(p_sequencer.usb_20_pkt_sequencer);
        end

        // Payload only applies to DATA packets; a TOKEN carries none.
        payload.delete();
        if (is_data_pkt)
            for (int unsigned i = 0; i < byte_count; i++)
                payload.push_back(~i[7:0]);

        pkt_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "pkt_seq");
        pkt_seq.pid                  = pid;
        pkt_seq.device_address       = 7'(USBDC0_ADDR);
        pkt_seq.endpoint_number      = 4'(EP1_BULK);
        pkt_seq.payload_bytes        = payload;
        pkt_seq.packet_configuration = usb_cfg;
        pkt_seq.error_kind           = kind;
        pkt_seq.use_crc              = use_crc;
        pkt_seq.crc_sel              = crc_sel;
        pkt_seq.use_phys             = use_phys;
        pkt_seq.phys_sel             = phys_sel;
        pkt_seq.use_len              = use_len;
        pkt_seq.len_sel              = len_sel;
        pkt_seq.len_byte_offset      = len_byte_offset;
        pkt_seq.use_field            = use_field;
        pkt_seq.field_sel            = field_sel;
        pkt_seq.field_value          = field_value;
        pkt_seq.attach_exception     = attach_exception;
        pkt_seq.msg_id               = msg_id;

        `uvm_info(msg_id,
            $sformatf({"%s: sending a %s packet (error_kind=%s). A bus-level ",
                       "failure on this packet is the expected outcome."},
                      inject_on_label, pid.name(),
                      attach_exception ? kind.name() : "none"), UVM_LOW)

        // The DUT may legitimately never answer a malformed packet, so the
        // start() is bounded - the same guard caliptra_ss_usb_ocp_persistent_
        // stall_sequence.svh uses around its directed packet.
        sent = 1'b0;
        fork : bounded_injection
            begin
                pkt_seq.start(p_sequencer.usb_20_pkt_sequencer);
                sent = 1'b1;
            end
            begin
                #INJECT_RESPONSE_BOUND;
            end
        join_any
        disable bounded_injection;

        if (!sent) begin
            pkt_seq.kill();
            `uvm_info(msg_id,
                {"Corrupted packet did not complete within the response bound. ",
                 "That is an acceptable outcome for an injected error - the DUT ",
                 "is not obliged to answer a malformed packet."}, UVM_LOW)
        end

        #ERROR_SETTLE_DELAY;
    endtask

    // -------------------------------------------------------------------------
    // Tell the MCU firmware it may halt, and wait for its ack.
    //
    // WHY EVERY ERROR-INJECTION BODY ENDS WITH THIS
    //
    // The error firmware has no completion condition of its own: a corrupted
    // packet is EXPECTED to be discarded, so there is no "transfer finished"
    // event it could stop on. It therefore polled to a fixed ceiling
    // (USB_ERR_POLL_TIMEOUT) and halted only when the budget ran out, which is
    // what made every one of these tests cost ~7.7 ms of simulation regardless
    // of which error it injected - all seven passing runs landed inside a 1 us
    // spread, while the sequences' own explicit delays account for under 300 us.
    //
    // With this handshake the firmware halts when the host says it is done, so
    // the simtime is set by the stimulus rather than by a loop count.
    //
    // Mechanism is the existing MCI generic-wire command channel from the
    // OCP-recovery work, same as caliptra_ss_usb_hs_hub_int_ep_status_change
    // and caliptra_ss_usb_fs_dev_lpm_l1_dev_wakeup:
    //   host_mcu_command -> GENERIC_INPUT_WIRES_1 -> firmware polls it
    //   firmware acks via GENERIC_OUTPUT_WIRES_1 -> fw_snapshot_header
    // issue_mcu_command_bounded() holds the command asserted until that ack
    // arrives, so polling firmware cannot miss a pulse.
    //
    // A missing ack is uvm_info, not uvm_error: the firmware keeps its own
    // bounded poll ceiling and halts without the command, and the base test's
    // MCU-halt monitor still applies. Failing here would let a teardown step
    // fail a test whose actual checks all passed.
    //
    // This is also the one point every err-injection sequence's body already
    // calls at its tail, so it is where caliptra_ss_usb_errortype_checker's
    // observation window is closed: triggering usb_errortype_obs_window_done
    // here lets that checker's verdict run in run_phase, while uvm_error still
    // counts toward final_phase, rather than in a `final` block that would run
    // after the verdict was already printed.
    // -------------------------------------------------------------------------
    protected task request_mcu_stop(string msg_id);
        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        bit acknowledged;
        uvm_event errortype_obs_window_done;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_info(msg_id,
                "No legacy EP0 observer interface in this testbench configuration, so the MCU STOP handshake is skipped. The firmware falls back to its own poll ceiling before halting.",
                UVM_LOW)
        end
        else begin
            observer_vif.issue_mcu_command_bounded(
                .opcode(MCU_STOP_OPCODE),
                .generation(16'h0001),
                .expected_legacy_dispatch_delta(4'h0),
                .timeout(MCU_STOP_ACK_MAX),
                .acknowledged(acknowledged));

            if (acknowledged)
                `uvm_info(msg_id,
                    "MCU STOP acknowledged: the firmware kept USBDC0 serviced for the whole sequence and is now free to halt.",
                    UVM_LOW)
            else
                `uvm_info(msg_id,
                    $sformatf("MCU STOP was not acknowledged within %0t. Not failed here: the firmware halts on its own poll ceiling without the command. If the MCU log also shows no STOP, suspect the firmware was not rebuilt with the STOP check.",
                        MCU_STOP_ACK_MAX),
                    UVM_LOW)
        end

        errortype_obs_window_done =
            uvm_event_pool::get_global("usb_errortype_obs_window_done");
        errortype_obs_window_done.trigger();
    endtask


endclass


`endif // CALIPTRA_SS_USB_ERR_INJECT_BASE_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
