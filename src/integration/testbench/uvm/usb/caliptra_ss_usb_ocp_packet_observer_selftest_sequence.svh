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

    protected function void require_true(input bit condition, input string label);
        if (!(condition === 1'b1))
            `uvm_fatal("OCP_PACKET_SELFTEST", label)
    endfunction

    protected function void open_window();
        generation++;
        observer.start_window(generation);
        observer.arm_setup_ack_trigger();
    endfunction

    protected function void emit(
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
            require_true(pkt.crc_error_detected(1'b1),
                "synthetic CRC marker retained");
        end
        if (rx) observer.usb_20_rx_packet_ended(null, pkt);
        else observer.usb_20_tx_packet_ended(null, pkt);
    endfunction

    protected function void setup_pair();
        emit(svt_usb_packet::SETUP);
        emit(svt_usb_packet::DATA0, 1'b0, 8);
    endfunction

    protected function bit valid_probe(input svt_usb_packet::pid_name_enum pid);
        return observer.check_stall_probe(pid, 7'd5, 4'd0, "synthetic");
    endfunction

    protected function void fifo_setup();
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
    endfunction

    protected function void fifo_out(
        input svt_usb_packet::pid_name_enum toggle,
        input int unsigned bytes,
        input svt_usb_packet::pid_name_enum reply);
        emit(svt_usb_packet::OUT);
        emit(toggle, 1'b0, bytes);
        emit(reply, 1'b1);
    endfunction

    protected function void fifo_status();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::DATA1, 1'b1, 0);
        emit(svt_usb_packet::ACK);
    endfunction

    protected function bit consume_fifo(
        input int unsigned bytes,
        input bit allowed = 1'b1,
        input bit owner_abort = 1'b0,
        input bit unrelated_abort = 1'b0);
        return adapter.observe_window(observer, generation, 7'd5,
            bytes, allowed, owner_abort, unrelated_abort);
    endfunction

    protected function void check_fifo_adapter();
        adapter = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_adapter");
        fifo_setup();
        require_true(!consume_fifo(4) && !adapter.observe_drain(1) &&
            !adapter.observe_abort(0) && !adapter.observe_reset(),
            "unconfigured lifecycle fails closed");

        // Reserved ring space is the default. ACK/NYET allocate exactly once;
        // a NAK followed by retry and an ACKed replay cannot inflate occupancy.
        adapter.configure(8, 8, 16, 1'b1, 32, 64);
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::NAK);
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::NYET);
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::ACK);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::NAK, 1'b1);
        fifo_status();
        require_true(consume_fifo(20) &&
            (adapter.committed_byte_count() == 20) &&
            (adapter.partial_byte_count() == 0) &&
            adapter.indices_match(5, 0), "packet-qualified ACK/NYET commit");
        require_true(!consume_fifo(20), "window replay rejected");
        require_true(!adapter.observe_drain(0) && !adapter.observe_drain(6) &&
            (adapter.committed_byte_count() == 20), "excess drain rejected");
        require_true(adapter.observe_drain(2) &&
            adapter.indices_match(5, 2), "independent drain evidence");

        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        require_true(consume_fifo(20, 1, 0, 1) &&
            (adapter.partial_byte_count() == 16) &&
            (adapter.committed_byte_count() == 12),
            "unrelated decoder abort preserves observed partial and prior commits");
        require_true(adapter.observe_abort(0) &&
            (adapter.partial_byte_count() == 16) &&
            adapter.observe_abort(1) &&
            (adapter.partial_byte_count() == 0) &&
            adapter.indices_match(5, 2), "only FIFO owner abort discards partial");
        require_true(!adapter.observe_abort(1), "duplicate owner abort rejected");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::NYET);
        require_true(consume_fifo(4, 1, 1) &&
            (adapter.committed_byte_count() == 12) &&
            adapter.indices_match(5, 2), "owner abort before status cannot commit");
        require_true(adapter.observe_drain(3) && adapter.indices_match(5, 5) &&
            adapter.observe_reset() && adapter.indices_match(0, 0),
            "drain and reset reconcile independently");

        fifo_setup();
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::DATA1, 0, 4, 7'd5, 4'd0, 1);
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::DATA1, 1, 0, 7'd5, 4'd0, 1);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::DATA1, 1, 0);
        fifo_status();
        require_true(consume_fifo(4) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0),
            "corrupt DATA/no-handshake and repeated status commit only once");
        require_true(adapter.observe_reset(), "reset retry history");
        fifo_setup();
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::DATA1, 0, 4, 7'd5, 4'd0, 1);
        emit(svt_usb_packet::ACK, 1);
        require_true(!consume_fifo(4),
            "ACK of corrupted DATA cannot manufacture acceptance");
        require_true(adapter.observe_reset(), "reset corrupt acceptance");

        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        fifo_out(svt_usb_packet::DATA0, 0, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(16),
            "extra OUT after exact request length cannot allocate or complete");
        require_true(adapter.observe_reset(), "reset extra OUT history");

        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::NYET);
        fifo_status();
        require_true(consume_fifo(20), "capacity setup commit");
        fifo_setup();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::NAK, 1'b1);
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        fifo_status();
        require_true(consume_fifo(4) && (adapter.free_byte_count() == 4),
            "short packet fits although maximum packet PING does not");
        fifo_setup();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!consume_fifo(4), "unsafe maximum-packet PING ACK caught");
        require_true(adapter.observe_reset(), "reset clears interrupted batch");

        fifo_setup();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::ACK, 1'b1);
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        fifo_status();
        require_true(consume_fifo(4), "PING ACK with maximum capacity");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::STALL);
        require_true(consume_fifo(4, 0) &&
            (adapter.committed_byte_count() == 4), "rejected request has no effect");
        fifo_setup();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(consume_fifo(0, 0), "zero-length request rejection");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(4, 0), "acceptance of rejected request caught");
        require_true(adapter.observe_reset(), "reset rejected history");

        fifo_setup();
        fifo_status();
        require_true(!consume_fifo(4), "status cannot substitute for packet acceptance");
        require_true(adapter.observe_reset(), "reset incomplete history");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 3, svt_usb_packet::ACK);
        require_true(!consume_fifo(4), "accepted wrong packet length caught");
        require_true(adapter.observe_reset(), "reset bad length");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::ACK);
        require_true(!consume_fifo(4), "initial wrong toggle cannot be a replay");
        require_true(adapter.observe_reset(), "reset bad toggle");
        fifo_setup();
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!consume_fifo(4), "unattributed handshake rejected");
        require_true(adapter.observe_reset(), "reset stray handshake");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!consume_fifo(4), "duplicate handshake rejected");
        require_true(adapter.observe_reset(), "reset duplicate handshake");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        fifo_out(svt_usb_packet::DATA0, 16, svt_usb_packet::NYET);
        require_true(!consume_fifo(32), "accepted over-capacity DATA caught");
        require_true(adapter.observe_reset(), "reset over-capacity history");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::DATA1, 1'b1, 0);
        require_true(!consume_fifo(4) &&
            (adapter.committed_byte_count() == 0), "missing status ACK cannot commit");
        require_true(adapter.observe_reset(), "reset missing completion");
        fifo_setup();
        emit(svt_usb_packet::OUT, 0, 0, 7'd6);
        emit(svt_usb_packet::DATA1, 0, 4);
        emit(svt_usb_packet::ACK, 1);
        require_true(!consume_fifo(4), "wrong target acceptance rejected");
        require_true(adapter.observe_reset(), "reset wrong target");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        require_true(consume_fifo(20, 1, 0, 1) &&
            adapter.observe_reset() &&
            (adapter.partial_byte_count() == 0) &&
            (adapter.committed_byte_count() == 0) &&
            adapter.indices_match(0, 0), "reset discards observed partial batch");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 3, svt_usb_packet::NYET);
        fifo_status();
        require_true(consume_fifo(3) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0), "packet adapter commits rounded short batch");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        fifo_out(svt_usb_packet::DATA0, 4, svt_usb_packet::STALL);
        require_true(consume_fifo(20) &&
            (adapter.partial_byte_count() == 0) &&
            (adapter.committed_byte_count() == 4) &&
            adapter.indices_match(1, 0), "owner STALL discards only current partial batch");
        require_true(adapter.observe_abort(0) &&
            (adapter.committed_byte_count() == 4),
            "unrelated abort cannot discard a completed batch");

        adapter.configure(8, 8, 16, 1'b1, 32, 1);
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(8), "over-image acceptance rejected");
        require_true(adapter.observe_reset(), "reset over-image history");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 4, svt_usb_packet::ACK);
        fifo_status();
        require_true(consume_fifo(4) && adapter.observe_drain(1),
            "complete image progress survives drain");
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 1, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(1), "exhausted image cannot accept after drain");
        adapter.configure(8, 8, 16, 1'b1, 4, 8);
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(8), "USB write limit independently enforced");
        adapter.configure(8, 1, 16, 1'b1, 32, 8);
        fifo_setup();
        fifo_out(svt_usb_packet::DATA1, 8, svt_usb_packet::ACK);
        fifo_status();
        require_true(!consume_fifo(8), "FIFO transfer limit independently enforced");
    endfunction

    protected task check_live_fifo();
        bit [7:0] status_bytes[$], response[$], payload[$];
        int unsigned size_dwords, max_dwords, bytes;
        logic [15:0] live_generation;
        if (!agent_capabilities[OCP_CAP_INDIRECT_FIFO]) begin
            `uvm_info("OCP_PACKET_SELFTEST", "Live FIFO not advertised.", UVM_LOW)
            return;
        end
        legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_LIMITS");
        if (status_bytes.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
            `uvm_fatal("OCP_PACKET_SELFTEST", "Live FIFO limits truncated.")
        size_dwords = get_le32(status_bytes, OCP_OFF_IFS_FIFO_SIZE_B0);
        max_dwords = get_le32(status_bytes, OCP_OFF_IFS_MAX_TRANSFER_B0);
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
        recovery_ctrl_write(0, OCP_RC_IMAGE_SEL_CMS, 1'b0, "LIVE_FIFO_IMAGE");
        prepare_modeled_fifo((bytes + 3) / 4, "LIVE_FIFO_RESET");
        for (int unsigned i = 0; i < bytes; i++) payload.push_back(8'(i ^ 8'hA5));
        open_observation_window(live_generation);
        indirect_fifo_data_write(payload, "LIVE_FIFO_DATA");
        close_observation_window(live_generation, 4'h0);
        require_accepted_setup("LIVE_FIFO_DATA");
        require_true((fifo_packet_model.committed_byte_count() == ((bytes + 3) / 4) * 4) &&
            (fifo_packet_model.partial_byte_count() == 0), "live packet/status commit");
        legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_COMMIT");
        legal_read(OCP_CMD_PROT_CAP, response, "LIVE_FIFO_UNRELATED_READ");
        legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_UNCHANGED");
        require_true(fifo_packet_model.committed_byte_count() == ((bytes + 3) / 4) * 4,
            "unrelated legal command cannot discard committed bytes");
        indirect_fifo_ctrl_write(0, 1'b1, (bytes + 3) / 4, "LIVE_FIFO_FINAL_RESET");
        legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, "LIVE_FIFO_RESET_CHECK");
        require_true(fifo_packet_model.committed_byte_count() == 0 &&
            fifo_packet_model.indices_match(0, 0), "live reset completion evidence");
        mark_check("live packet-qualified FIFO commit, unrelated command, reset");
    endtask

    virtual task body();
        bit observed;
        caliptra_ss_usb_ocp_arbiter_packet_callback::packet_record_t record;
        caliptra_ss_usb_ocp_fifo_packet_model fifo_model;
        svt_usb_packet::pid_name_enum forbidden[5];

        initialize_stall_transport();
        observer = caliptra_ss_usb_ocp_arbiter_packet_callback::type_id::create(
            "observer");
        model = caliptra_ss_usb_ocp_stall_model::type_id::create("model");
        observer.enable_diagnostics();

        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(observer.accepted_setup_count() == 1, "adjacent setup");
        require_true(observer.setup_stage_acked(), "retrospective setup");
        // The trigger predates the waiter: no event may be lost.
        observer.wait_for_setup_ack_trigger(1ns, observed);
        require_true(observed, "sticky setup trigger");
        observer.wait_for_packet_count(3, 1ns, observed);
        require_true(observed, "sticky packet count");
        record = observer.get_packet(2);
        require_true(record.target_valid &&
                     (record.device_address == 5) &&
                     (record.endpoint_number == 0) &&
                     record.accepted_setup, "ACK token attribution");
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(observer.accepted_setup_count() == 1, "stray ACK ignored");
        observer.arm_setup_ack_trigger();
        emit(svt_usb_packet::ACK, 1'b1);
        observer.wait_for_setup_ack_trigger(1ns, observed);
        require_true(!observed, "rearm cannot consume old ACK");

        open_window();
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "ACK without setup");
        setup_pair();
        emit(svt_usb_packet::NAK, 1'b1);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "NAK cancels pending setup");
        observer.wait_for_setup_ack_trigger(1ns, observed);
        require_true(!observed, "live tracker rejects stale ACK");

        open_window();
        setup_pair();
        emit(svt_usb_packet::IN, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "wrong EP token cancels setup");
        open_window();
        setup_pair();
        emit(svt_usb_packet::PING, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "PING cancels pending setup");
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK); // TX ACK cannot be device acceptance.
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "TX ACK cancels setup");
        open_window();
        setup_pair();
        emit(svt_usb_packet::DATA0, 1'b0, 8);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "duplicate DATA cancels setup");
        open_window();
        emit(svt_usb_packet::SETUP);
        emit(svt_usb_packet::DATA1, 1'b0, 8);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "SETUP DATA1 rejected");
        open_window();
        setup_pair();
        emit(svt_usb_packet::SETUP, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "new SETUP cancels old DATA0");
        emit(svt_usb_packet::SETUP, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::DATA0, 1'b0, 8);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(observer.accepted_setup_count() == 1,
                     "replacement SETUP accepts only its own DATA0");
        for (int unsigned size = 7; size <= 9; size += 2) begin
            open_window();
            emit(svt_usb_packet::SETUP);
            emit(svt_usb_packet::DATA0, 1'b0, size);
            emit(svt_usb_packet::ACK, 1'b1);
            require_true(!observer.setup_stage_acked(), "SETUP must be exactly 8 bytes");
        end
        open_window();
        emit(svt_usb_packet::SETUP);
        emit(svt_usb_packet::SOF);
        emit(svt_usb_packet::DATA0, 1'b0, 8);
        emit(svt_usb_packet::SOF);
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(observer.setup_stage_acked(), "SOF preserves setup");

        open_window();
        fork
            begin
                observer.wait_for_packet_count(1, 10ns, observed);
            end
            begin
                #1ns;
                emit(svt_usb_packet::IN);
            end
        join
        require_true(observed, "packet waiter observes future packet");
        observer.wait_for_packet_count(2, 1ns, observed);
        require_true(!observed && (observer.timeout_count() == 1),
                     "bounded packet timeout");
        setup_pair();
        observer.note_abort();
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked() &&
                     (observer.abort_count() == 1), "explicit abort clears pending");
        setup_pair();
        observer.stop_window();
        open_window();
        emit(svt_usb_packet::ACK, 1'b1);
        require_true(!observer.setup_stage_acked(), "window reset clears pending");
        fork
            begin
                observer.wait_for_packet_count(2, 10ns, observed);
            end
            begin
                #1ns;
                open_window();
                emit(svt_usb_packet::IN);
                emit(svt_usb_packet::STALL, 1'b1);
            end
        join
        require_true(!observed, "old waiter cannot consume new window packets");

        open_window();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(valid_probe(svt_usb_packet::IN), "IN STALL probe");
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "duplicate STALL rejected");
        open_window();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(valid_probe(svt_usb_packet::PING), "PING STALL probe");
        record = observer.get_packet(0);
        require_true((record.pid_type === svt_usb_packet::SPECIAL) &&
                     record.target_valid && (record.device_address == 5) &&
                     (record.endpoint_number == 0), "SPECIAL PING token attribution");
        record = observer.get_packet(1);
        require_true(record.target_valid && (record.device_address == 5) &&
                     (record.endpoint_number == 0), "PING STALL target attribution");
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::PING), "duplicate PING STALL rejected");
        open_window();
        emit(svt_usb_packet::PING, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::PING), "wrong EP PING rejected");
        open_window();
        emit(svt_usb_packet::PING, 1'b0, 0, 7'd6);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::PING), "wrong address PING rejected");
        open_window();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::DATA0);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::PING), "PING cannot carry OUT data");
        open_window();
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::PING), "duplicate PING token rejected");
        open_window();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::PING);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "PING steals pending IN response");
        open_window();
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::DATA1, 1'b0, 3);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(valid_probe(svt_usb_packet::OUT), "OUT DATA1 STALL probe");
        open_window();
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::DATA0); // Zero-length DATA is still a data packet.
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(valid_probe(svt_usb_packet::OUT), "OUT ZLP STALL probe");
        open_window();
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::OUT), "OUT without data rejected");
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control OUT token-only STALL rejected");
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control unattributed STALL rejected");
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
        emit(svt_usb_packet::OUT);
        emit(svt_usb_packet::DATA1, 1'b0, 3);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(observer.validate_control_stall(7'd5, 4'd0),
                     "control OUT DATA STALL accepted");
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::DATA1, 1'b1, 1);
        require_true(!observer.validate_control_stall(7'd5, 4'd0),
                     "control continuation after STALL rejected");
        open_window();
        emit(svt_usb_packet::IN, 1'b0, 0, 7'd5, 4'd1);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "wrong EP STALL rejected");
        open_window();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::IN, 1'b0, 0, 7'd6);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "wrong address steals response");
        open_window();
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::STALL, 1'b1);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "duplicate token/STALL rejected");
        open_window();
        setup_pair();
        emit(svt_usb_packet::ACK, 1'b1);
        emit(svt_usb_packet::IN);
        emit(svt_usb_packet::STALL, 1'b1);
        require_true(!valid_probe(svt_usb_packet::IN), "SETUP forbidden in probe");

        forbidden = '{svt_usb_packet::ACK, svt_usb_packet::NAK,
                      svt_usb_packet::NYET, svt_usb_packet::DATA0,
                      svt_usb_packet::DATA1};
        foreach (forbidden[index]) begin
            open_window();
            emit(svt_usb_packet::IN);
            emit(forbidden[index], 1'b1);
            emit(svt_usb_packet::STALL, 1'b1);
            require_true(!valid_probe(svt_usb_packet::IN),
                         "forbidden target response before STALL");
            open_window();
            emit(svt_usb_packet::IN);
            emit(svt_usb_packet::STALL, 1'b1);
            emit(forbidden[index], 1'b1);
            require_true(!valid_probe(svt_usb_packet::IN),
                         "forbidden target response after STALL");
            open_window();
            emit(svt_usb_packet::PING);
            emit(forbidden[index], 1'b1);
            emit(svt_usb_packet::STALL, 1'b1);
            require_true(!valid_probe(svt_usb_packet::PING),
                         "forbidden PING response before STALL");
            open_window();
            emit(svt_usb_packet::PING);
            emit(svt_usb_packet::STALL, 1'b1);
            emit(forbidden[index], 1'b1);
            require_true(!valid_probe(svt_usb_packet::PING),
                         "forbidden PING response after STALL");
        end
        open_window();
        for (int unsigned i = 0; i <= 4096; i++) emit(svt_usb_packet::SOF);
        require_true(observer.overflowed() && (observer.packet_count() == 4096),
                     "bounded packet retention");
        require_true(!valid_probe(svt_usb_packet::IN), "overflow fails closed");

        // Explicit expected state first; no packet observation updates it.
        model.reset();
        require_true(!model.is_stalled(), "model reset clears stall");
        require_true(!model.status_code_matches(8'h04), "negative status predicate");
        model.note_error(OCP_PROTOCOL_ERROR_LENGTH);
        model.note_error(OCP_PROTOCOL_ERROR_CRC);
        require_true(model.require_stalled("injected error"), "error stalls");
        require_true(model.status_code_matches(8'h03), "first error wins");
        require_true(!model.status_code_matches(8'h04), "later error cannot win");
        model.note_accepted_setup();
        require_true(!model.is_stalled() && model.status_code_matches(8'h03),
                     "accepted SETUP clears only stall");
        require_true(model.check_status_code(8'h03, "first read"), "first read code");
        require_true(model.status_code_matches(8'h00), "status is clear on read");
        require_true(model.check_status_code(8'h00, "second read"), "second read zero");
        model.note_error(OCP_PROTOCOL_ERROR_CRC);
        require_true(model.check_status_code(8'h04, "new error"), "new error after clear");
        require_true(model.is_stalled(), "read does not itself clear stall");
        model.note_accepted_setup();
        model.note_error(OCP_PROTOCOL_ERROR_NONE);
        require_true(!model.is_stalled(), "NONE does not induce stall");
        model.report("synthetic selftest");

        fifo_model = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_model");
        // Runtime FIFO, transfer and packet limits are independent inputs.
        fifo_model.configure(16, 12, 32, 1'b1);
        require_true(fifo_model.free_byte_count() == 60,
                     "runtime FIFO reserves one ring slot");
        fifo_model.begin_batch(48);
        require_true(fifo_model.next_packet_bytes() == 32 &&
                     fifo_model.can_accept_next_packet(), "runtime first packet limit");
        fifo_model.accept_packet(32);
        require_true(fifo_model.next_packet_bytes() == 16 &&
                     fifo_model.partial_byte_count() == 32,
                     "runtime short final packet");
        fifo_model.accept_packet(16);
        fifo_model.commit_batch();
        require_true(fifo_model.committed_byte_count() == 48 &&
                     fifo_model.partial_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(12, 0), "runtime batch commit");
        require_true(!fifo_model.can_ack_ping(), "maximum packet PING capacity");
        fifo_model.drain(12);
        require_true(fifo_model.committed_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 60 &&
                     fifo_model.indices_match(12, 12), "runtime drain reconciliation");

        fifo_model.configure(8, 8, 16, 1'b0);
        require_true(fifo_model.free_byte_count() == 32 &&
                     fifo_model.indices_match(0, 0), "reconfigure runtime FIFO limits");
        fifo_model.begin_batch(20);
        require_true(fifo_model.next_packet_bytes() == 16 &&
                     fifo_model.can_accept_next_packet(), "16-byte packet capacity");
        fifo_model.accept_packet(16);
        require_true(fifo_model.next_packet_bytes() == 4 &&
                     fifo_model.can_accept_next_packet(), "4-byte final packet capacity");
        fifo_model.accept_packet(4);
        fifo_model.commit_batch();
        require_true(fifo_model.committed_byte_count() == 20 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(5, 0), "20-byte committed occupancy");
        fifo_model.begin_batch(8);
        require_true(fifo_model.next_packet_bytes() == 8 &&
                     fifo_model.can_accept_next_packet() &&
                     !fifo_model.can_ack_ping(),
                     "short packet fits while maximum-packet PING cannot ACK");
        fifo_model.accept_packet(8);
        require_true(fifo_model.partial_byte_count() == 8 &&
                     fifo_model.committed_byte_count() == 20,
                     "partial data separate from earlier commits");
        fifo_model.abort_batch(1'b1);
        require_true(fifo_model.partial_byte_count() == 0 &&
                     fifo_model.committed_byte_count() == 20 &&
                     fifo_model.free_byte_count() == 12 &&
                     fifo_model.indices_match(5, 0),
                     "owned abort discards only partial batch");

        fifo_model.begin_batch(8);
        fifo_model.accept_packet(8);
        fifo_model.abort_batch(1'b0);
        require_true(fifo_model.partial_byte_count() == 8 &&
                     fifo_model.committed_byte_count() == 20,
                     "unrelated abort preserves partial and committed data");
        fifo_model.abort_batch(1'b1);
        require_true(fifo_model.partial_byte_count() == 0 &&
                     fifo_model.committed_byte_count() == 20,
                     "owned abort after unrelated abort cleans partial data");
        fifo_model.drain(5);
        require_true(fifo_model.committed_byte_count() == 0 &&
                     fifo_model.free_byte_count() == 32 &&
                     fifo_model.indices_match(5, 5), "prior commits drain independently");

        // A non-dword final payload occupies a rounded FIFO word. The write
        // index wraps modulo runtime depth, not modulo max transfer length.
        fifo_model.begin_batch(15);
        require_true(fifo_model.next_packet_bytes() == 15 &&
                     fifo_model.can_accept_next_packet(), "rounded batch capacity");
        fifo_model.accept_packet(15);
        require_true(fifo_model.partial_byte_count() == 15, "partial byte precision");
        fifo_model.commit_batch();
        require_true(fifo_model.free_byte_count() == 16 &&
                     fifo_model.partial_byte_count() == 0 &&
                     fifo_model.indices_match(1, 5), "rounded commit wraps write index");
        fifo_model.drain(4);
        require_true(fifo_model.free_byte_count() == 32 &&
                     fifo_model.committed_byte_count() == 0 &&
                     fifo_model.indices_match(1, 1), "rounded drain wraps read index");
        observer.stop_window();
        check_fifo_adapter();
        observer.stop_window();
        check_live_fifo();
        `uvm_info("OCP_PACKET_SELFTEST", "Observer/model synthetic checks complete", UVM_LOW)
        finish_stall_test("PACKET_OBSERVER_SELFTEST");
    endtask
endclass

`endif // CALIPTRA_SS_USB_OCP_PACKET_OBSERVER_SELFTEST_SEQUENCE_SVH
