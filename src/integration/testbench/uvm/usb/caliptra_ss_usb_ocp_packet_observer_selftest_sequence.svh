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

`ifndef CALIPTRA_SS_USB_OCP_PACKET_OBSERVER_SELFTEST_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_PACKET_OBSERVER_SELFTEST_SEQUENCE_SVH

// Synthetic callback/model checks use no monitor or DUT-returned status to
// establish expectations. The base sequence owns transport initialization
// and test completion so firmware can finish normally after these checks.
// USB 2.0 8.5.3.4; OCP Recovery 1.1 8.5.1, 9.1, 9.2.
class caliptra_ss_usb_ocp_packet_observer_selftest_sequence
    extends caliptra_ss_usb_ocp_stall_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_packet_observer_selftest_sequence)

    protected caliptra_ss_usb_ocp_arbiter_packet_callback observer;
    protected caliptra_ss_usb_ocp_stall_model model;
    protected logic [15:0] generation;
    protected caliptra_ss_usb_ocp_fifo_packet_model adapter;

    function new(string name =
        "caliptra_ss_usb_ocp_packet_observer_selftest_sequence");
        super.new(name);
        generation = 0;
    endfunction

    protected function void ocp_packet_check_true(input bit condition, input string label);
        if (!(condition === 1'b1))
            `uvm_fatal("OCP_PACKET_SELFTEST", label)
    endfunction

    protected function void ocp_packet_open_synthetic_observation_window();
        generation++;
        observer.start_window(generation);
        observer.arm_setup_ack_trigger();
    endfunction

    protected function void ocp_packet_emit_synthetic_packet(
        input svt_usb_packet::pid_name_enum pid,
        input bit rx = 1'b0,
        input int unsigned bytes = 0,
        input bit [6:0] address = 7'd5,
        input bit [3:0] endpoint = 4'd0,
        input bit bad_crc = 1'b0);

        svt_usb_packet pkt;
        svt_usb_packet_exception crc_exception;
        bit carries_target;
        pkt = svt_usb_packet::type_id::create("synthetic_packet");
        pkt.pid_name = pid;
        case (pid)
            svt_usb_packet::SETUP, svt_usb_packet::IN,
            svt_usb_packet::OUT, svt_usb_packet::SOF:
                pkt.pid_type = svt_usb_packet::TOKEN;
            svt_usb_packet::PING:
                pkt.pid_type = svt_usb_packet::SPECIAL;
            svt_usb_packet::DATA0, svt_usb_packet::DATA1,
            svt_usb_packet::DATA2, svt_usb_packet::MDATA:
                pkt.pid_type = svt_usb_packet::DATA;
            default: pkt.pid_type = svt_usb_packet::HANDSHAKE;
        endcase
        // DATA/handshake address fields deliberately differ from the token.
        // The observer must use the token, not these irrelevant fields.
        carries_target = (pkt.pid_type === svt_usb_packet::TOKEN) ||
                         ((pkt.pid_type === svt_usb_packet::SPECIAL) &&
                          (pid === svt_usb_packet::PING));
        pkt.device_address = carries_target ? address : 7'd99;
        pkt.ept_num = carries_target ? endpoint : 4'd7;
        if (pkt.pid_type === svt_usb_packet::DATA) begin
            pkt.payload = svt_usb_payload::type_id::create("synthetic_payload");
            pkt.payload.data_generation_algorithm =
                svt_usb_payload::TWO_SEED_BASED_ALGORITHM;
            pkt.payload.byte_count = bytes;
        end
        if (bad_crc) begin
            crc_exception = new("synthetic_crc");
            crc_exception.xact = pkt;
            crc_exception.error_group = svt_usb_packet_exception::RANDOM_ERROR_GROUP;
            crc_exception.error_kind = svt_usb_packet_exception::CRC_ERROR;
            crc_exception.crc_error = svt_usb_packet_exception::CRC16_ERROR;
            crc_exception.no_exception = 0;
            crc_exception.recognized = 0;
            crc_exception.retry_number = 0;
            pkt.exception_list = new("synthetic_crc_list");
            pkt.exception_list.add_exception(crc_exception);
            ocp_packet_check_true(pkt.crc_error_detected(1'b1),
                "synthetic CRC marker retained");
        end
        if (rx) observer.usb_20_rx_packet_ended(null, pkt);
        else observer.usb_20_tx_packet_ended(null, pkt);
    endfunction

    protected function void ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 1'b0, 8);
    endfunction

    protected function bit ocp_packet_check_synthetic_stall_probe(input
        svt_usb_packet::pid_name_enum pid);
        return observer.check_stall_probe(pid, 7'd5, 4'd0, "synthetic");
    endfunction

    protected function void ocp_packet_emit_synthetic_stall_probe(
        input svt_usb_packet::pid_name_enum pid);
        ocp_packet_emit_synthetic_packet(pid);
        if (pid == svt_usb_packet::OUT)
            ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b0, 3);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
    endfunction

    protected function bit ocp_packet_check_synthetic_history_complete();
        caliptra_ss_usb_ocp_arbiter_packet_callback saved_callback;
        bit complete;
        // Exercise the production close predicate without altering live capture.
        saved_callback = checker.packet_callback;
        checker.packet_callback = observer;
        complete = checker.packet_history_complete();
        checker.packet_callback = saved_callback;
        return complete;
    endfunction

    protected task ocp_packet_check_synthetic_overflow();
        localparam int unsigned TraceLimit =
            caliptra_ss_usb_ocp_arbiter_packet_callback::MAX_PACKET_RECORDS;
        svt_usb_transfer::xfer_stage_enum stages[3] = '{
            svt_usb_transfer::SETUP_STAGE, svt_usb_transfer::DATA_STAGE,
            svt_usb_transfer::STATUS_STAGE};
        bit observed;
        int unsigned data_length;
        realtime setup_time;
        realtime expected_setup_time;

        // -------------------------------------------------------------------------
        // Fill trace storage, then deliver a complete control read after it fills.
        // Run checks:
        // * SETUP/DATA/STATUS events and SETUP acceptance still arrive.
        // * Counters, lengths, timestamps and OUT completion include dropped records.
        // * Full storage is complete; exceeding it prevents isolation checking.
        foreach (stages[index]) begin
            ocp_packet_open_synthetic_observation_window();
            for (int unsigned i = 0; i < TraceLimit; i++)
                ocp_packet_emit_synthetic_packet(svt_usb_packet::SOF);
            ocp_packet_check_true(!observer.overflowed() &&
                ocp_packet_check_synthetic_history_complete(),
                "full trace without truncation remains complete");
            observer.arm_stage_trigger(stages[index]);
            fork
                observer.wait_for_stage_trigger(10ns, observed);
                begin
                    #1ns;
                    expected_setup_time = $realtime;
                    ocp_packet_emit_synthetic_setup_pair();
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1, 4);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1);
                    ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
                end
            join
            ocp_packet_check_true(observed,
                $sformatf("%s trigger survives trace overflow", stages[index].name()));
            observer.wait_for_setup_ack_trigger(1ns, observed);
            ocp_packet_check_true(observed &&
                (observer.accepted_setup_count() == 1) &&
                observer.setup_stage_acked(), "SETUP summary survives overflow");
            ocp_packet_check_true(observer.overflowed() &&
                (observer.packet_count() == TraceLimit) &&
                !ocp_packet_check_synthetic_history_complete() &&
                !ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN) &&
                !observer.validate_control_stall(7'd5, 4'd0),
                "truncated trace cannot prove isolation or STALL");
            ocp_packet_check_true(
                (observer.count_pid(svt_usb_packet::OUT,
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) == 1) &&
                (observer.count_pid(svt_usb_packet::ACK,
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) == 2) &&
                (observer.count_zlp(
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) == 1) &&
                (observer.count_zlp(
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) == 0),
                "streaming packet counters include unretained traffic");
            ocp_packet_check_true(observer.get_last_rx_data_length(data_length) &&
                (data_length == 4) && observer.get_setup_timestamp(setup_time) &&
                (setup_time == expected_setup_time) &&
                observer.legacy_out_stage_completed(),
                "streaming control-read summaries include unretained status");
            observer.stop_window();
            ocp_packet_check_true(observer.legacy_out_stage_completed() &&
                (observer.accepted_setup_count() == 1) &&
                observer.get_last_rx_data_length(data_length) &&
                (data_length == 4) &&
                !ocp_packet_check_synthetic_history_complete(),
                "closed window preserves summaries and overflow");
        end

        // -------------------------------------------------------------------------
        // Fill trace with control-IN retries, then complete DATA and OUT status.
        // Run checks:
        // * The status-stage event and OUT completion survive truncation.
        // * Restarting capture removes the previous window's summaries.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_check_true(!observer.overflowed() &&
            (observer.packet_count() == 0) &&
            (observer.accepted_setup_count() == 0) &&
            !observer.legacy_out_stage_completed() &&
            !observer.get_last_rx_data_length(data_length) &&
            !observer.get_setup_timestamp(setup_time) &&
            (observer.count_pid(svt_usb_packet::OUT,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) == 0) &&
            (observer.count_zlp(
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) == 0),
            "new window clears streaming summaries and overflow");
        observer.arm_stage_trigger(svt_usb_transfer::STATUS_STAGE);
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        while ((observer.packet_count() + 2) <= TraceLimit) begin
            ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
        end
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_check_true((observer.packet_count() == TraceLimit) &&
            !observer.overflowed(), "retry history fills the retained trace");
        fork
            observer.wait_for_stage_trigger(10ns, observed);
            begin
                #1ns;
                ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1, 4);
                ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK);
                ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
                ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1);
                ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
            end
        join
        ocp_packet_check_true(observed && observer.overflowed() &&
            observer.legacy_out_stage_completed() &&
            (observer.accepted_setup_count() == 1) &&
            !ocp_packet_check_synthetic_history_complete(),
            "control-IN retry overflow preserves completed OUT status");
        observer.stop_window();
        `uvm_info("OCP_PACKET_SELFTEST",
            {"Streaming summaries and all three stage triggers survive trace ",
             "overflow; truncated histories cannot prove isolation."}, UVM_NONE)
    endtask

    protected function void ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
    endfunction

    protected function void ocp_packet_emit_synthetic_fifo_out(
        input svt_usb_packet::pid_name_enum toggle,
        input int unsigned bytes,
        input svt_usb_packet::pid_name_enum reply);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(toggle, 1'b0, bytes);
        ocp_packet_emit_synthetic_packet(reply, 1'b1);
    endfunction

    protected function void ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1, 0);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK);
    endfunction

    protected function bit ocp_packet_check_and_consume_synthetic_fifo_window(
        input int unsigned bytes,
        input bit allowed = 1'b1,
        input bit owner_abort = 1'b0,
        input bit unrelated_abort = 1'b0);
        return adapter.observe_window(observer, generation, 7'd5,
            bytes, allowed, owner_abort, unrelated_abort);
    endfunction

    protected function void ocp_packet_check_synthetic_fifo_adapter();
        svt_usb_packet::pid_name_enum orphan_replies[$] = '{
            svt_usb_packet::ACK, svt_usb_packet::NYET};
        adapter = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_adapter");

        // -------------------------------------------------------------------------
        // Exercise packet processing, drain, abort and reset before configuration.
        // Run checks:
        // * Unconfigured packet and lifecycle operations are rejected.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            !adapter.observe_drain(1) &&
            !adapter.observe_abort(0) && !adapter.observe_reset(),
            "unconfigured lifecycle fails closed");

        // -------------------------------------------------------------------------
        // Retry NAKed DATA, replay accepted DATA, then complete status and drain.
        // Run checks:
        // * ACK/NYET acceptance counts each unique DATA packet once.
        // * Status completion commits exactly 20 bytes.
        // * Repeated history consumption is rejected.
        // * Drain bounds and READ_INDEX match the consumed DWORDs.
        adapter.configure(8, 8, 16, 1'b1, 32, 64);
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::NAK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::NYET);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20) &&
            (adapter.committed_byte_count() == 20) &&
            (adapter.partial_byte_count() == 0) &&
            adapter.indices_match(5, 0), "packet-qualified ACK/NYET commit");
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(20), "window replay rejected");
        ocp_packet_check_true(!adapter.observe_drain(0) && !adapter.observe_drain(6) && (adapter.committed_byte_count() == 20), "excess drain rejected");
        ocp_packet_check_true(adapter.observe_drain(2) && adapter.indices_match(5, 2), "independent drain evidence");

        // -------------------------------------------------------------------------
        // Interrupt a write, apply unrelated/FIFO-write aborts, then drain/reset.
        // Run checks:
        // * An unrelated abort preserves partial and earlier committed bytes.
        // * A FIFO-write abort discards only the partial bytes.
        // * Drain and reset produce the expected indices.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20, 1, 0, 1) &&
            (adapter.partial_byte_count() == 16) &&
            (adapter.committed_byte_count() == 12),
            "unrelated decoder abort preserves observed partial and prior commits");
        ocp_packet_check_true(adapter.observe_abort(0) &&
            (adapter.partial_byte_count() == 16) &&
            adapter.observe_abort(1) &&
            (adapter.partial_byte_count() == 0) &&
            adapter.indices_match(5, 2), "only FIFO owner abort discards partial");
        ocp_packet_check_true(!adapter.observe_abort(1), "duplicate owner abort rejected");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::NYET);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4, 1, 1) &&
            (adapter.committed_byte_count() == 12) &&
            adapter.indices_match(5, 2), "owner abort before status cannot commit");
        ocp_packet_check_true(adapter.observe_drain(3) && adapter.indices_match(5, 5) &&
            adapter.observe_reset() && adapter.indices_match(0, 0),
            "drain and reset reconcile independently");

        // -------------------------------------------------------------------------
        // Retry corrupt DATA and corrupt or unacknowledged status responses.
        // Run checks:
        // * Valid completion commits the retried write once.
        // * An ACK following corrupt OUT DATA cannot establish acceptance.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 0, 4, 7'd5, 4'd0, 1);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1, 0, 7'd5, 4'd0, 1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1, 0);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0),
            "corrupt DATA/no-handshake and repeated status commit only once");
        ocp_packet_check_true(adapter.observe_reset(), "reset retry history");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 0, 4, 7'd5, 4'd0, 1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "ACK of corrupted DATA cannot manufacture acceptance");
        ocp_packet_check_true(adapter.observe_reset(), "reset corrupt acceptance");

        // -------------------------------------------------------------------------
        // Supply corrupt RX DATA followed by unsolicited ACK/NYET or status DATA.
        // Handshakes have no CRC; the OUT-reply fixture uses unexpected DATA.
        // Run checks:
        // * An unsolicited OUT reply allocates no bytes.
        // * Unsolicited status DATA cannot commit the earlier accepted bytes.
        foreach (orphan_replies[i]) begin
            ocp_packet_emit_synthetic_fifo_setup();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 0, 4);
            ocp_packet_emit_synthetic_packet(.pid(svt_usb_packet::DATA1),
                .rx(1'b1), .bad_crc(1'b1));
            ocp_packet_emit_synthetic_packet(orphan_replies[i], 1'b1);
            ocp_packet_emit_synthetic_fifo_status();
            ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
                (adapter.committed_byte_count() == 0) &&
                (adapter.partial_byte_count() == 0),
                $sformatf("orphan %s after corrupt OUT reply rejected",
                    orphan_replies[i].name()));
            ocp_packet_check_true(adapter.observe_reset(), "reset orphan OUT reply");
        end

        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(.pid(svt_usb_packet::DATA1),
            .rx(1'b1), .bad_crc(1'b1));
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            (adapter.committed_byte_count() == 0) &&
            (adapter.partial_byte_count() == 4),
            "orphan status DATA1 after corruption cannot commit");
        ocp_packet_check_true(adapter.observe_reset(), "reset orphan status reply");

        // -------------------------------------------------------------------------
        // Retry OUT/status with fresh tokens and replay DATA0 (USB 2.0 8.6.4).
        // Run checks:
        // * Earlier accepted bytes and the expected DATA0 toggle are preserved.
        // * An ACKed DATA replay adds no bytes.
        // * Status completion commits exactly 20 bytes once.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 0, 4);
        ocp_packet_emit_synthetic_packet(.pid(svt_usb_packet::DATA1),
            .rx(1'b1), .bad_crc(1'b1));
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::NYET);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(.pid(svt_usb_packet::DATA1),
            .rx(1'b1), .bad_crc(1'b1));
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20) &&
            (adapter.committed_byte_count() == 20) &&
            (adapter.partial_byte_count() == 0) &&
            adapter.indices_match(5, 0),
            "fresh-token retries preserve DATA0 toggle and commit once");
        ocp_packet_check_true(adapter.observe_reset(), "reset corrupt-response retries");
        `uvm_info("OCP_PACKET_SELFTEST",
            {"Corrupt-response histories: orphan ACK, NYET and status rejected; ",
             "fresh-token retries commit once."}, UVM_NONE)

        // -------------------------------------------------------------------------
        // Send an extra OUT ZLP after all declared write bytes were accepted.
        // Run checks:
        // * The extra OUT transaction makes the history invalid.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 0, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(16),
            "extra OUT after exact request length cannot allocate or complete");
        ocp_packet_check_true(adapter.observe_reset(), "reset extra OUT history");

        // -------------------------------------------------------------------------
        // Fill most of the FIFO, send short DATA, then supply an unsafe PING ACK.
        // Run checks:
        // * Short DATA fits even when a maximum-sized packet would not.
        // * PING ACK is rejected without space for a maximum-sized packet.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::NYET);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20),
            "capacity setup commit");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4) && (
            adapter.free_byte_count() == 4),
            "short packet fits although maximum packet PING does not");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "unsafe maximum-packet PING ACK caught");
        ocp_packet_check_true(adapter.observe_reset(), "reset clears interrupted batch");

        // -------------------------------------------------------------------------
        // Supply a safe PING/write, STALLed writes and an unexpected accepted write.
        // Run checks:
        // * The safe write commits; later STALLed writes leave its data unchanged.
        // * Packet acceptance is rejected when the request is expected to STALL.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "PING ACK with maximum capacity");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::STALL);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4, 0) &&
            (adapter.committed_byte_count() == 4), "rejected request has no effect");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(0, 0),
            "zero-length request rejection");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4, 0),
            "acceptance of rejected request caught");
        ocp_packet_check_true(adapter.observe_reset(), "reset rejected history");

        // -------------------------------------------------------------------------
        // Omit DATA/status ACK and vary packet length, toggle, target and capacity.
        // Run checks:
        // * Missing or invalid packets cannot establish acceptance or commit.
        // * Unattributed/duplicate handshakes and over-capacity DATA are rejected.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "status cannot substitute for packet acceptance");
        ocp_packet_check_true(adapter.observe_reset(), "reset incomplete history");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 3, svt_usb_packet::ACK);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "accepted wrong packet length caught");
        ocp_packet_check_true(adapter.observe_reset(), "reset bad length");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::ACK);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "initial wrong toggle cannot be a replay");
        ocp_packet_check_true(adapter.observe_reset(), "reset bad toggle");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "unattributed handshake rejected");
        ocp_packet_check_true(adapter.observe_reset(), "reset stray handshake");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "duplicate handshake rejected");
        ocp_packet_check_true(adapter.observe_reset(), "reset duplicate handshake");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 16, svt_usb_packet::NYET);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(32),
            "accepted over-capacity DATA caught");
        ocp_packet_check_true(adapter.observe_reset(), "reset over-capacity history");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1, 0);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            (adapter.committed_byte_count() == 0), "missing status ACK cannot commit");
        ocp_packet_check_true(adapter.observe_reset(), "reset missing completion");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT, 0, 0, 7'd6);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 0, 4);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1);
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4),
            "wrong target acceptance rejected");
        ocp_packet_check_true(adapter.observe_reset(), "reset wrong target");

        // -------------------------------------------------------------------------
        // Reset an unfinished write, complete a short write, then apply STALL/abort.
        // Run checks:
        // * Reset clears partial bytes and indices.
        // * The short write occupies one rounded DWORD.
        // * A later FIFO-write STALL or unrelated abort preserves that commit.
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20, 1, 0, 1) &&
            adapter.observe_reset() &&
            (adapter.partial_byte_count() == 0) &&
            (adapter.committed_byte_count() == 0) &&
            adapter.indices_match(0, 0), "reset discards observed partial batch");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 3, svt_usb_packet::NYET);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(3) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0), "packet adapter commits rounded short batch");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::STALL);
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(20) &&
            (adapter.partial_byte_count() == 0) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0), "owner STALL discards only current partial batch");
        ocp_packet_check_true(adapter.observe_abort(0) &&
            (adapter.committed_byte_count() == 4),
            "unrelated abort cannot discard a completed batch");

        // -------------------------------------------------------------------------
        // Exceed each image/USB/FIFO limit and drain an otherwise complete image.
        // Run checks:
        // * Image, USB-write and FIFO-transfer limits are enforced independently.
        // * Drain frees FIFO space but does not restore the consumed image budget.
        adapter.configure(8, 8, 16, 1'b1, 32, 1);
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(8),
            "over-image acceptance rejected");
        ocp_packet_check_true(adapter.observe_reset(), "reset over-image history");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            adapter.observe_drain(1),
            "complete image progress survives drain");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 1, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(1),
            "exhausted image cannot accept after drain");
        adapter.configure(8, 8, 16, 1'b1, 4, 8);
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(8),
            "USB write limit independently enforced");
        adapter.configure(8, 1, 16, 1'b1, 32, 8);
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(8),
            "FIFO transfer limit independently enforced");
    endfunction

    protected task ocp_packet_do_exercise_and_check_live_fifo();
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;
        bit [7:0] status_bytes[$], response[$], payload[$];
        int unsigned size_dwords, max_dwords, bytes;
        logic [15:0] live_generation;
        if (!agent_capabilities[OCP_CAP_INDIRECT_FIFO]) begin
            `uvm_info("OCP_PACKET_SELFTEST", "Live FIFO not advertised.", UVM_LOW)
            return;
        end
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_LIMITS");
        if (status_bytes.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
            `uvm_fatal("OCP_PACKET_SELFTEST", "Live FIFO limits truncated.")
        size_dwords = ocp_get_le32(status_bytes, OCP_OFF_IFS_FIFO_SIZE_B0);
        max_dwords = ocp_get_le32(status_bytes, OCP_OFF_IFS_MAX_TRANSFER_B0);
        // Keep an extra DWORD free beyond the normative reserved ring slot.
        // Select at most two HS packets; all limits are discovered at runtime.
        if ((size_dwords < 3) || (max_dwords == 0) ||
            (size_dwords > 32'h3FFF_FFFF) ||
            (max_dwords > 32'h3FFF_FFFF))
            `uvm_fatal("OCP_PACKET_SELFTEST", "No safe live FIFO capacity.")
        bytes = HS_CONTROL_PACKET_BYTES + 4;
        if (bytes > (size_dwords - 2) * 4) bytes = (size_dwords - 2) * 4;
        if (bytes > max_dwords * 4) bytes = max_dwords * 4;
        if (bytes > wMaxWrTransferSize) bytes = wMaxWrTransferSize;
        if (bytes == 0)
            `uvm_fatal("OCP_PACKET_SELFTEST", "No legal live FIFO transfer length.")
        ocp_do_recovery_ctrl_write(0, OCP_RC_IMAGE_SEL_CMS, 1'b0, "LIVE_FIFO_IMAGE");
        ocp_stall_do_configure_and_check_fifo((bytes + 3) / 4, "LIVE_FIFO_RESET");
        for (int unsigned i = 0; i < bytes; i++) payload.push_back(8'(i ^ 8'hA5));
        ocp_arb_open_observation_window(live_generation);
        ocp_do_fifo_data_write(payload, ignored_result, "LIVE_FIFO_DATA");
        ocp_arb_check_and_close_observation_window(live_generation, 4'h0);
        ocp_stall_check_single_accepted_setup("LIVE_FIFO_DATA");
        ocp_packet_check_true((fifo_packet_model.committed_byte_count() == ((bytes + 3) / 4) * 4) &&
            (fifo_packet_model.partial_byte_count() == 0), "live packet/status commit");
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_COMMIT");
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_PROT_CAP, response, "LIVE_FIFO_UNRELATED_READ");
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_UNCHANGED");
        ocp_packet_check_true(fifo_packet_model.committed_byte_count() == ((bytes + 3) / 4) * 4,
            "unrelated legal command cannot discard committed bytes");
        ocp_do_fifo_ctrl_write(0, 1'b1, (bytes + 3) / 4, "LIVE_FIFO_FINAL_RESET");
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_RESET_CHECK");
        ocp_packet_check_true(fifo_packet_model.committed_byte_count() == 0 &&
            fifo_packet_model.indices_match(0, 0), "live reset completion evidence");
        ocp_stall_note_check_completed("live packet-qualified FIFO commit, unrelated command, reset");
    endtask

    virtual task body();
        bit observed;
        caliptra_ss_usb_ocp_arbiter_packet_callback::packet_record_t record;
        caliptra_ss_usb_ocp_fifo_packet_model fifo_model;
        svt_usb_packet::pid_name_enum forbidden[5];
        svt_usb_packet::pid_name_enum probe_pids[3] = '{
            svt_usb_packet::IN, svt_usb_packet::OUT, svt_usb_packet::PING};
        svt_usb_packet::pid_name_enum prefixes[7] = '{
            svt_usb_packet::ACK, svt_usb_packet::NAK, svt_usb_packet::NYET,
            svt_usb_packet::STALL, svt_usb_packet::DATA0, svt_usb_packet::DATA1,
            svt_usb_packet::IN};

        // -------------------------------------------------------------------------
        // Initialize real transport, then exercise private callback/model objects.
        // Synthetic packet calls below do not transmit traffic to the DUT.
        ocp_stall_do_initialize_and_check_transport();
        observer = caliptra_ss_usb_ocp_arbiter_packet_callback::type_id::create(
            "observer");
        model = caliptra_ss_usb_ocp_stall_model::type_id::create("model");
        observer.enable_diagnostics();

        // -------------------------------------------------------------------------
        // Supply SETUP/DATA0/ACK, wait on recorded packets, then rearm the trigger.
        // Run checks:
        // * SETUP is accepted once and its ACK uses the host token's target.
        // * Already observed packets satisfy waits.
        // * Rearming does not reuse an old ACK.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(observer.accepted_setup_count() == 1, "adjacent setup");
        ocp_packet_check_true(observer.setup_stage_acked(), "retrospective setup");
        // The trigger predates the waiter: no event may be lost.
        observer.wait_for_setup_ack_trigger(1ns, observed);
        ocp_packet_check_true(observed, "sticky setup trigger");
        observer.wait_for_packet_count(3, 1ns, observed);
        ocp_packet_check_true(observed, "sticky packet count");
        record = observer.get_packet(2);
        ocp_packet_check_true(record.target_valid &&
                     (record.device_address == 5) &&
                     (record.endpoint_number == 0) &&
                     record.accepted_setup, "ACK token attribution");
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(observer.accepted_setup_count() == 1, "stray ACK ignored");
        observer.arm_setup_ack_trigger();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        observer.wait_for_setup_ack_trigger(1ns, observed);
        ocp_packet_check_true(!observed, "rearm cannot consume old ACK");

        // -------------------------------------------------------------------------
        // Supply an ACK without SETUP and an ACK after NAK cancelled SETUP.
        // Run checks:
        // * Neither ACK is recorded as successful SETUP acceptance.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "ACK without setup");
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "NAK cancels pending setup");
        observer.wait_for_setup_ack_trigger(1ns, observed);
        ocp_packet_check_true(!observed, "live tracker rejects stale ACK");

        // -------------------------------------------------------------------------
        // Interrupt pending SETUP with another token, host ACK or duplicate DATA.
        // Run checks:
        // * The interrupted SETUP is not accepted by a later device ACK.
        // * SETUP using DATA1 instead of DATA0 is rejected.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "wrong EP token cancels setup");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "PING cancels pending setup");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK);
            // TX ACK cannot be device acceptance.
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "TX ACK cancels setup");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 1'b0, 8);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "duplicate DATA cancels setup");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b0, 8);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "SETUP DATA1 rejected");

        // -------------------------------------------------------------------------
        // Replace SETUP, vary its DATA length and insert SOF records.
        // Run checks:
        // * Replacement SETUP needs its own DATA0 and device ACK.
        // * SETUP DATA is exactly eight bytes.
        // * SOF records leave pending SETUP tracking unchanged.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "new SETUP cancels old DATA0");
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 1'b0, 8);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(observer.accepted_setup_count() == 1,
                     "replacement SETUP accepts only its own DATA0");
        for (int unsigned size = 7; size <= 9; size += 2) begin
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 1'b0, size);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
            ocp_packet_check_true(!observer.setup_stage_acked(), "SETUP must be exactly 8 bytes");
        end
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SETUP);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SOF);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0, 1'b0, 8);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::SOF);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(observer.setup_stage_acked(), "SOF preserves setup");

        // -------------------------------------------------------------------------
        // Start packet waits, supply future packets, then abort/restart collection.
        // Run checks:
        // * Future packets wake the waiter; missing packets cause a timeout.
        // * Abort and a new collection clear pending SETUP.
        // * An old waiter cannot consume a new collection's packets.
        ocp_packet_open_synthetic_observation_window();
        fork
            begin
                observer.wait_for_packet_count(1, 10ns, observed);
            end
            begin
                #1ns;
                ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
            end
        join
        ocp_packet_check_true(observed, "packet waiter observes future packet");
        observer.wait_for_packet_count(2, 1ns, observed);
        ocp_packet_check_true(!observed && (observer.timeout_count() == 1),
                     "bounded packet timeout");
        ocp_packet_emit_synthetic_setup_pair();
        observer.note_abort();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked() &&
                     (observer.abort_count() == 1), "explicit abort clears pending");
        ocp_packet_emit_synthetic_setup_pair();
        observer.stop_window();
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "window reset clears pending");
        fork
            begin
                observer.wait_for_packet_count(2, 10ns, observed);
            end
            begin
                #1ns;
                ocp_packet_open_synthetic_observation_window();
                ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
                ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
            end
        join
        ocp_packet_check_true(!observed, "old waiter cannot consume new window packets");

        // -------------------------------------------------------------------------
        // Supply IN/PING STALL, duplicate replies and wrong/intervening tokens.
        // Run checks:
        // * A single correctly targeted STALL is recognized.
        // * Duplicate responses, wrong targets and DATA following PING are rejected.
        // * A PING token cannot make its response count as an earlier IN response.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "IN STALL probe");
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "duplicate STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "PING STALL probe");
        record = observer.get_packet(0);
        ocp_packet_check_true((record.pid_type === svt_usb_packet::SPECIAL) &&
                     record.target_valid && (record.device_address == 5) &&
                     (record.endpoint_number == 0), "SPECIAL PING token attribution");
        record = observer.get_packet(1);
        ocp_packet_check_true(record.target_valid && (record.device_address == 5) &&
                     (record.endpoint_number == 0), "PING STALL target attribution");
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "duplicate PING STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "wrong EP PING rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING, 1'b0, 0, 7'd6);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "wrong address PING rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "PING cannot carry OUT data");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
            "duplicate PING token rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "PING steals pending IN response");

        // -------------------------------------------------------------------------
        // Supply OUT/DATA/STALL, omit DATA and add traffic after a control STALL.
        // Run checks:
        // * OUT STALL needs preceding DATA; a zero-length DATA packet qualifies.
        // * Bare probes and control requests reject missing/unattributed responses.
        // * A control request cannot continue successfully after STALL.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b0, 3);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(ocp_packet_check_synthetic_stall_probe(svt_usb_packet::OUT),
            "OUT DATA1 STALL probe");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA0);
            // Zero-length DATA is still a data packet.
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(ocp_packet_check_synthetic_stall_probe(svt_usb_packet::OUT),
            "OUT ZLP STALL probe");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::OUT),
            "OUT without data rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control OUT token-only STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control unattributed STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::OUT);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b0, 3);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(observer.validate_control_stall(7'd5, 4'd0),
                     "control OUT DATA STALL accepted");
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::DATA1, 1'b1, 1);
        ocp_packet_check_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control continuation after STALL rejected");

        // -------------------------------------------------------------------------
        // Vary IN targets, insert another token, repeat transactions and add SETUP.
        // Run checks:
        // * Wrong targets, intervening tokens and duplicate transactions are rejected.
        // * A bare IN probe cannot include SETUP.
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN, 1'b0, 0, 7'd5, 4'd1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "wrong EP STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN, 1'b0, 0, 7'd6);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "wrong address steals response");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "duplicate token/STALL rejected");
        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "SETUP forbidden in probe");

        // -------------------------------------------------------------------------
        // Place ACK, NAK, NYET or DATA before and after an IN/PING STALL.
        // Run checks:
        // * Any response in addition to STALL makes the probe history invalid.
        forbidden = '{svt_usb_packet::ACK, svt_usb_packet::NAK,
                      svt_usb_packet::NYET, svt_usb_packet::DATA0,
                      svt_usb_packet::DATA1};
        foreach (forbidden[index]) begin
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
            ocp_packet_emit_synthetic_packet(forbidden[index], 1'b1);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
            ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
                         "forbidden target response before STALL");
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::IN);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
            ocp_packet_emit_synthetic_packet(forbidden[index], 1'b1);
            ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
                         "forbidden target response after STALL");
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
            ocp_packet_emit_synthetic_packet(forbidden[index], 1'b1);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
            ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
                         "forbidden PING response before STALL");
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::PING);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::STALL, 1'b1);
            ocp_packet_emit_synthetic_packet(forbidden[index], 1'b1);
            ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::PING),
                         "forbidden PING response after STALL");
        end

        // -------------------------------------------------------------------------
        // Prefix clean IN/OUT/PING probes with packets before their first token.
        // Run checks:
        // * Unattributed device responses and RX tokens invalidate the probe.
        // * SOF and complete transactions to another target remain distinct.
        foreach (probe_pids[p]) begin
            foreach (prefixes[r]) begin
                ocp_packet_open_synthetic_observation_window();
                ocp_packet_emit_synthetic_packet(prefixes[r], 1'b1);
                record = observer.get_packet(0);
                ocp_packet_emit_synthetic_stall_probe(probe_pids[p]);
                ocp_packet_check_true(!record.target_valid &&
                    !ocp_packet_check_synthetic_stall_probe(probe_pids[p]),
                    $sformatf("unattributed %s before %s probe rejected",
                        prefixes[r].name(), probe_pids[p].name()));
            end
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::SOF);
            ocp_packet_emit_synthetic_stall_probe(probe_pids[p]);
            ocp_packet_check_true(
                ocp_packet_check_synthetic_stall_probe(probe_pids[p]),
                "SOF before a clean probe is transparent");
            ocp_packet_open_synthetic_observation_window();
            ocp_packet_emit_synthetic_packet(svt_usb_packet::IN, 1'b0, 0, 7'd6);
            ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
            ocp_packet_emit_synthetic_stall_probe(probe_pids[p]);
            ocp_packet_check_true(
                ocp_packet_check_synthetic_stall_probe(probe_pids[p]),
                "attributed other-target transaction is not unsolicited");
        end
        `uvm_info("OCP_PACKET_SELFTEST",
            "Pre-token responses rejected for IN, OUT and PING; clean probes preserved.",
            UVM_NONE)

        // -------------------------------------------------------------------------
        // Exercise bounded retention, streaming summaries and live stage events.
        // Run checks:
        // * Control-read completion remains visible after trace truncation.
        // * Isolation and packet-history predicates reject overflowed windows.
        ocp_packet_check_synthetic_overflow();

        // -------------------------------------------------------------------------
        // Apply error, accepted-SETUP and status-read events directly to the model.
        // Run checks:
        // * Accepted SETUP clears STALL without clearing the error code.
        // * A status read clears the code without clearing STALL.
        // * Local policy retains the first unread error until a status read.
        model.reset();
        ocp_packet_check_true(!model.is_stalled(), "model reset clears stall");
        ocp_packet_check_true(!model.status_code_matches(8'h04), "negative status predicate");
        model.note_error(OCP_PROTOCOL_ERROR_LENGTH);
        model.note_error(OCP_PROTOCOL_ERROR_CRC);
        ocp_packet_check_true(model.require_stalled("injected error"), "error stalls");
        ocp_packet_check_true(model.status_code_matches(8'h03), "first error wins");
        ocp_packet_check_true(!model.status_code_matches(8'h04), "later error cannot win");
        model.note_accepted_setup();
        ocp_packet_check_true(!model.is_stalled() && model.status_code_matches(8'h03),
                     "accepted SETUP clears only stall");
        ocp_packet_check_true(model.check_status_code(8'h03, "first read"), "first read code");
        ocp_packet_check_true(model.status_code_matches(8'h00), "status is clear on read");
        ocp_packet_check_true(model.check_status_code(8'h00, "second read"), "second read zero");
        model.note_error(OCP_PROTOCOL_ERROR_CRC);
        ocp_packet_check_true(model.check_status_code(8'h04, "new error"), "new error after clear");
        ocp_packet_check_true(model.is_stalled(), "read does not itself clear stall");
        model.note_accepted_setup();
        model.note_error(OCP_PROTOCOL_ERROR_NONE);
        ocp_packet_check_true(!model.is_stalled(), "NONE does not induce stall");
        model.report("synthetic selftest");

        // -------------------------------------------------------------------------
        // Exercise FIFO arithmetic directly with separate FIFO/transfer/packet limits.
        // Run checks:
        // * Reserved capacity and short final packet length use the supplied limits.
        // * Commit and drain produce the expected byte counts and indices.
        fifo_model = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_model");
        fifo_model.configure(16, 12, 32, 1'b1);
        ocp_packet_check_true(fifo_model.free_byte_count() == 60,
                     "runtime FIFO reserves one ring slot");
        fifo_model.begin_batch(48);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 32 &&
                     fifo_model.can_accept_next_packet(), "runtime first packet limit");
        fifo_model.accept_packet(32);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 16 &&
                     fifo_model.partial_byte_count() == 32,
                     "runtime short final packet");
        fifo_model.accept_packet(16);
        fifo_model.commit_batch();
        ocp_packet_check_true(fifo_model.committed_byte_count() == 48 &&
                     fifo_model.partial_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(12, 0), "runtime batch commit");
        ocp_packet_check_true(!fifo_model.can_ack_ping(), "maximum packet PING capacity");
        fifo_model.drain(12);
        ocp_packet_check_true(fifo_model.committed_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 60 &&
                     fifo_model.indices_match(12, 12), "runtime drain reconciliation");

        // -------------------------------------------------------------------------
        // Select full-capacity storage, complete one write and abort the next.
        // Run checks:
        // * Actual packet size permits short DATA when maximum-packet PING cannot ACK.
        // * Partial bytes remain separate from prior commits.
        // * A FIFO-write abort discards only partial bytes.
        fifo_model.configure(8, 8, 16, 1'b0);
        ocp_packet_check_true(fifo_model.free_byte_count() == 32 &&
                     fifo_model.indices_match(0, 0), "reconfigure runtime FIFO limits");
        fifo_model.begin_batch(20);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 16 &&
                     fifo_model.can_accept_next_packet(), "16-byte packet capacity");
        fifo_model.accept_packet(16);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 4 &&
                     fifo_model.can_accept_next_packet(), "4-byte final packet capacity");
        fifo_model.accept_packet(4);
        fifo_model.commit_batch();
        ocp_packet_check_true(fifo_model.committed_byte_count() == 20 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(5, 0), "20-byte committed occupancy");
        fifo_model.begin_batch(8);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 8 &&
                     fifo_model.can_accept_next_packet() &&
                     !fifo_model.can_ack_ping(),
                     "short packet fits while maximum-packet PING cannot ACK");
        fifo_model.accept_packet(8);
        ocp_packet_check_true(fifo_model.partial_byte_count() == 8 &&
                     fifo_model.committed_byte_count() == 20,
                     "partial data separate from earlier commits");
        fifo_model.abort_batch(1'b1);
        ocp_packet_check_true(fifo_model.partial_byte_count() == 0 &&
                     fifo_model.committed_byte_count() == 20 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(5, 0),
                     "owned abort discards only partial batch");

        // -------------------------------------------------------------------------
        // Apply an unrelated abort, then a FIFO-write abort, then drain.
        // Run checks:
        // * An unrelated abort preserves partial and committed bytes.
        // * A FIFO-write abort drops partial bytes; drain consumes committed bytes.
        fifo_model.begin_batch(8);
        fifo_model.accept_packet(8);
        fifo_model.abort_batch(1'b0);
        ocp_packet_check_true(fifo_model.partial_byte_count() == 8 &&
                     fifo_model.committed_byte_count() == 20,
                     "unrelated abort preserves partial and committed data");
        fifo_model.abort_batch(1'b1);
        ocp_packet_check_true(fifo_model.partial_byte_count() == 0 &&
                     fifo_model.committed_byte_count() == 20,
                     "owned abort after unrelated abort cleans partial data");
        fifo_model.drain(5);
        ocp_packet_check_true(fifo_model.committed_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 32 &&
                     fifo_model.indices_match(5, 5), "prior commits drain independently");

        // -------------------------------------------------------------------------
        // Round a non-DWORD final write to storage words and drain those words.
        // Run checks:
        // * Partial data counts exact bytes; commit rounds storage to DWORDs.
        // * Both indices wrap at FIFO depth, not at the maximum transfer length.
        fifo_model.begin_batch(15);
        ocp_packet_check_true(fifo_model.next_packet_bytes() == 15 &&
                     fifo_model.can_accept_next_packet(), "rounded batch capacity");
        fifo_model.accept_packet(15);
        ocp_packet_check_true(fifo_model.partial_byte_count() == 15, "partial byte precision");
        fifo_model.commit_batch();
        ocp_packet_check_true(fifo_model.free_byte_count() == 16 &&
                     fifo_model.partial_byte_count() == 0 &&
                     fifo_model.indices_match(1, 5), "rounded commit wraps write index");
        fifo_model.drain(4);
        ocp_packet_check_true(fifo_model.free_byte_count() == 32 &&
                     fifo_model.committed_byte_count() == 0 &&
                     fifo_model.indices_match(1, 1), "rounded drain wraps read index");

        // -------------------------------------------------------------------------
        // Feed synthetic packet histories through the FIFO parser.
        // Run checks:
        // * Valid histories produce the expected FIFO byte counts and indices.
        // * Invalid acceptance or completion histories are rejected.
        observer.stop_window();
        ocp_packet_check_synthetic_fifo_adapter();

        // -------------------------------------------------------------------------
        // Perform a real FIFO write, unrelated read and reset, then finish through UVM.
        // Run checks:
        // * Packet-qualified commit agrees with the reported FIFO indices.
        // * The unrelated read preserves FIFO data.
        // * Reset clears the model and visible indices.
        observer.stop_window();
        ocp_packet_do_exercise_and_check_live_fifo();
        `uvm_info("OCP_PACKET_SELFTEST", "Observer/model synthetic checks complete", UVM_LOW)
        ocp_stall_do_final_read_and_check_completion("PACKET_OBSERVER_SELFTEST");
    endtask
endclass

`endif // CALIPTRA_SS_USB_OCP_PACKET_OBSERVER_SELFTEST_SEQUENCE_SVH
