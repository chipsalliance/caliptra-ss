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
        adapter = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_adapter");
        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(4) &&
            !adapter.observe_drain(1) &&
            !adapter.observe_abort(0) && !adapter.observe_reset(),
            "unconfigured lifecycle fails closed");

        // Reserved ring space is the default. ACK/NYET allocate exactly once;
        // a NAK followed by retry and an ACKed replay cannot inflate occupancy.
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

        ocp_packet_emit_synthetic_fifo_setup();
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA1, 16, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_out(svt_usb_packet::DATA0, 0, svt_usb_packet::ACK);
        ocp_packet_emit_synthetic_fifo_status();
        ocp_packet_check_true(!ocp_packet_check_and_consume_synthetic_fifo_window(16),
            "extra OUT after exact request length cannot allocate or complete");
        ocp_packet_check_true(adapter.observe_reset(), "reset extra OUT history");

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

        ocp_stall_do_initialize_and_check_transport();
        observer = caliptra_ss_usb_ocp_arbiter_packet_callback::type_id::create(
            "observer");
        model = caliptra_ss_usb_ocp_stall_model::type_id::create("model");
        observer.enable_diagnostics();

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

        ocp_packet_open_synthetic_observation_window();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "ACK without setup");
        ocp_packet_emit_synthetic_setup_pair();
        ocp_packet_emit_synthetic_packet(svt_usb_packet::NAK, 1'b1);
        ocp_packet_emit_synthetic_packet(svt_usb_packet::ACK, 1'b1);
        ocp_packet_check_true(!observer.setup_stage_acked(), "NAK cancels pending setup");
        observer.wait_for_setup_ack_trigger(1ns, observed);
        ocp_packet_check_true(!observed, "live tracker rejects stale ACK");

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
        ocp_packet_open_synthetic_observation_window();
        for (int unsigned i = 0; i <= 4096; i++) ocp_packet_emit_synthetic_packet(
            svt_usb_packet::SOF);
        ocp_packet_check_true(observer.overflowed() && (observer.packet_count() == 4096),
                     "bounded packet retention");
        ocp_packet_check_true(!ocp_packet_check_synthetic_stall_probe(svt_usb_packet::IN),
            "overflow fails closed");

        // Explicit expected state first; no packet observation updates it.
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

        fifo_model = caliptra_ss_usb_ocp_fifo_packet_model::type_id::create(
            "synthetic_fifo_model");
        // Runtime FIFO, transfer and packet limits are independent inputs.
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

        // A non-dword final payload occupies a rounded FIFO word. The write
        // index wraps modulo runtime depth, not modulo max transfer length.
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
        observer.stop_window();
        ocp_packet_check_synthetic_fifo_adapter();
        observer.stop_window();
        ocp_packet_do_exercise_and_check_live_fifo();
        `uvm_info("OCP_PACKET_SELFTEST", "Observer/model synthetic checks complete", UVM_LOW)
        ocp_stall_do_final_read_and_check_completion("PACKET_OBSERVER_SELFTEST");
    endtask
endclass

`endif // CALIPTRA_SS_USB_OCP_PACKET_OBSERVER_SELFTEST_SEQUENCE_SVH
