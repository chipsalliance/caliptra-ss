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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_LOCAL_BEHAVIOR_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_FIFO_LOCAL_BEHAVIOR_SEQUENCE_SVH

// Explicit local full-capacity contract. This does NOT replace the normative
// OCP Recovery v1.1 8.2.5 reserve-slot verdict in the ring testcase.
// State space: full/near-full/empty x publication held/released x
// OUT/PING/status x valid/zero/envelope/remainder length.
class caliptra_ss_usb_ocp_fifo_local_behavior_sequence
    extends caliptra_ss_usb_ocp_persistent_stall_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_fifo_local_behavior_sequence)

    typedef caliptra_ss_usb_ocp_arbiter_packet_callback cb_t;
    localparam time RAW_ACCEPTANCE_BOUND = 2ms;
    localparam time RAW_RETRY_INTERVAL = 125us;
    protected int unsigned capacity_bytes;
    protected int unsigned write_chunk_bytes;
    protected int unsigned packet_bytes;
    protected int unsigned maximum_transfer_dwords;

    function new(string name = "caliptra_ss_usb_ocp_fifo_local_behavior_sequence");
        super.new(name);
    endfunction

    protected task ocp_local_pace_retry(input time deadline);
        time interval;
        if ($time >= deadline) return;
        interval = deadline - $time;
        if (interval > RAW_RETRY_INTERVAL) interval = RAW_RETRY_INTERVAL;
        #(interval);
    endtask

    protected task ocp_local_wait_publication(
        input bit expected, output bit observed);
        observed = 1'b0;
        fork : bounded_publication
            begin
                wait (semantics_vif.recovery_payload_available === expected);
                observed = 1'b1;
            end
            begin
                #(FW_SERVICE_BOUND);
            end
        join_any
        disable bounded_publication;
    endtask

    protected task ocp_local_do_reset_and_check_fifo(
        input int unsigned image_dwords, input string label);
        // Every caller has completed all byte groups. Pending PING-only
        // cleanup closes capture before reset; no accepted DATA is abandoned.
        fifo_model_configured = 1'b0;
        ocp_stall_do_configure_and_check_fifo(image_dwords, label, 1'b0);
        if ((fifo_packet_model.committed_byte_count() != 0) ||
            (fifo_packet_model.partial_byte_count() != 0) ||
            !fifo_packet_model.lifecycle_idle())
            `uvm_fatal("OCP_LOCAL_FIFO", {label, ": reset model is not empty/idle."})
    endtask

    protected task ocp_local_do_token_and_get_reply(
        input svt_usb_packet::pid_name_enum token,
        output cb_t::packet_record_t reply, input string label);
        bit [7:0] empty_payload[$];
        int unsigned first_record;
        first_record = checker.packet_callback.packet_count();
        ocp_stall_do_transmit_packet_and_check_completion(token, empty_payload);
        ocp_stall_wait_reply(first_record, reply, label, "OCP_LOCAL_PACKET");
    endtask

    protected task ocp_local_do_data_and_get_reply(
        ref bit [7:0] payload[$], output cb_t::packet_record_t reply,
        input string label);
        bit [7:0] empty_payload[$];
        int unsigned first_record;
        first_record = checker.packet_callback.packet_count();
        ocp_stall_do_transmit_packet_and_check_completion(
            svt_usb_packet::OUT, empty_payload);
        ocp_stall_do_transmit_packet_and_check_completion(
            svt_usb_packet::DATA1, payload);
        ocp_stall_wait_reply(first_record, reply, label, "OCP_LOCAL_PACKET");
    endtask

    protected function void ocp_local_check_accepted_reply(
        input cb_t::packet_record_t reply, input string label,
        input bit require_nyet = 1'b0);
        // USB 2.0 8.5.3/8.5.1: both ACK and NYET accept HS OUT DATA.
        if (!((reply.pid_name === svt_usb_packet::ACK) ||
              (reply.pid_name === svt_usb_packet::NYET)) ||
            (require_nyet && !(reply.pid_name === svt_usb_packet::NYET)))
            `uvm_fatal("OCP_LOCAL_PACKET",
                $sformatf("%s DATA reply=%s; expected %s.", label,
                    reply.pid_name.name(), require_nyet ? "NYET" : "ACK/NYET"))
    endfunction

    protected task ocp_local_do_status_and_check_completion(input string label);
        cb_t::packet_record_t reply;
        bit [7:0] empty_payload[$];
        time deadline;
        deadline = $time + RAW_ACCEPTANCE_BOUND;
        while ($time < deadline) begin
            ocp_local_do_token_and_get_reply(svt_usb_packet::IN, reply, label);
            if (reply.pid_name === svt_usb_packet::NAK) begin
                ocp_local_pace_retry(deadline);
                continue;
            end
            if (!(reply.pid_name === svt_usb_packet::DATA1) ||
                (reply.data_length != 0))
                `uvm_fatal("OCP_LOCAL_PACKET", {label, ": expected DATA1 ZLP status."})
            ocp_stall_do_transmit_packet_and_check_completion(
                svt_usb_packet::ACK, empty_payload);
            return;
        end
        `uvm_fatal("OCP_LOCAL_PACKET", {label, ": status completion exceeded 2ms."})
    endtask

    protected task ocp_local_do_ping_and_check_ready(input string label);
        cb_t::packet_record_t reply;
        time deadline;
        deadline = $time + RAW_ACCEPTANCE_BOUND;
        while ($time < deadline) begin
            ocp_local_do_token_and_get_reply(svt_usb_packet::PING, reply, label);
            if (reply.pid_name === svt_usb_packet::ACK) return;
            if (!(reply.pid_name === svt_usb_packet::NAK))
                `uvm_fatal("OCP_LOCAL_PACKET", {label, ": PING returned neither ACK nor NAK."})
            // Pacing protects bounded callback history; only ACK proves ready.
            ocp_local_pace_retry(deadline);
        end
        `uvm_fatal("OCP_LOCAL_LIVENESS", {label, ": no PING ACK within 2ms after confirmed drain."})
    endtask

    protected task ocp_local_do_close_and_check_fifo_window(
        input logic [15:0] generation, input int unsigned length,
        input int unsigned expected_committed, input string label);
        if (fifo_window_pending)
            `uvm_fatal("OCP_LOCAL_FIFO", "Raw window was also registered as an automatic FIFO window.")
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        fifo_scoreboard.observe_fifo_window(checker.packet_callback,
            generation, 7'(dev_addr_v), length, 1'b1);
        if ((fifo_packet_model.committed_byte_count() != expected_committed) ||
            (fifo_packet_model.partial_byte_count() != 0) ||
            !fifo_packet_model.lifecycle_idle())
            `uvm_fatal("OCP_LOCAL_FIFO", {label, ": exact packet/status commit accounting failed."})
    endtask

    protected task ocp_local_do_write_and_check_commit(
        ref bit [7:0] payload[$], input string label,
        input bit require_nyet = 1'b0);
        logic [15:0] generation;
        cb_t::packet_record_t reply;
        int unsigned expected_committed;
        expected_committed = fifo_packet_model.committed_byte_count() + payload.size();
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_stall_do_setup_and_check_ack(0, OCP_CMD_INDIRECT_FIFO_DATA,
            16'(payload.size()), label, "OCP_LOCAL_PACKET");
        ocp_local_do_data_and_get_reply(payload, reply, label);
        ocp_local_check_accepted_reply(reply, label, require_nyet);
        ocp_local_do_status_and_check_completion(label);
        ocp_local_do_close_and_check_fifo_window(
            generation, payload.size(), expected_committed, label);
        if (checker.packet_callback.count_pid(svt_usb_packet::DATA1, cb_t::PACKET_TX) != 1)
            `uvm_fatal("OCP_LOCAL_PACKET", {label, ": expected exactly one transmitted DATA1."})
    endtask

    protected task ocp_local_do_fill_and_check_commits(
        input int unsigned total_bytes, ref bit [7:0] expected[$],
        input string label, input bit require_final_nyet = 1'b0);
        bit [7:0] payload[$];
        int unsigned chunk;
        expected.delete();
        while (expected.size() < total_bytes) begin
            chunk = total_bytes - expected.size();
            if (chunk > write_chunk_bytes) chunk = write_chunk_bytes;
            payload.delete();
            repeat (chunk) begin
                payload.push_back(8'(8'h39 ^ expected.size() ^ (expected.size() >> 8)));
                expected.push_back(payload[$]);
            end
            ocp_local_do_write_and_check_commit(payload, label,
                require_final_nyet && (expected.size() == total_bytes));
        end
    endtask

    protected task ocp_local_do_drain_and_check_content(
        ref bit [7:0] expected[$], input string label);
        logic [7:0] value;
        bit published, released;
        if ((expected.size() == 0) || ((expected.size() % 4) != 0))
            `uvm_fatal("OCP_LOCAL_FW", {label, ": drain must finish complete DWORD byte groups."})
        ocp_local_wait_publication(1'b1, published);
        if (!published)
            `uvm_fatal("OCP_LOCAL_LIVENESS", {label, ": no legal firmware publication within 200us."})
        foreach (expected[i]) begin
            ocp_stall_execute_fw_command(FW_READ_FIFO_BYTE,
                semantics_vif.FW_STATE_PATH_READY, value, label, "OCP_LOCAL_FW");
            if (!(value === expected[i]))
                `uvm_error("OCP_LOCAL_CONTENT",
                    $sformatf("%s byte[%0d]=%02h expected=%02h.",
                        label, i, value, expected[i]))
            // Four fresh, acknowledged byte commands independently confirm
            // one DMA pop plus all three cached bytes. Never use index deltas.
            if ((i % 4) == 3) fifo_scoreboard.observe_fifo_drain(1);
        end
        ocp_local_wait_publication(1'b0, released);
        if (!released)
            `uvm_fatal("OCP_LOCAL_LIVENESS", {label, ": publication did not release after entire drain."})
    endtask

    protected task ocp_local_do_read_and_check_flags(
        input bit full, input bit empty, input string label);
        bit [7:0] status[$];
        ocp_stall_do_read_and_check_no_stall(OCP_CMD_INDIRECT_FIFO_STATUS, status, label);
        // Shared reader requires the complete 20-byte record and checks both
        // modulo indices against the acceptance/independent-drain model.
        if (!((status[OCP_OFF_IFS_STATUS] & OCP_IFS_FULL_MASK) ===
              (full ? OCP_IFS_FULL_MASK : 8'h00)) ||
            !((status[OCP_OFF_IFS_STATUS] & OCP_IFS_EMPTY_MASK) ===
              (empty ? OCP_IFS_EMPTY_MASK : 8'h00)))
            `uvm_error("OCP_LOCAL_FIFO", {label, ": FULL/EMPTY flags disagree with local contract."})
        if (full &&
            !(ocp_get_le32(status, OCP_OFF_IFS_WRITE_INDEX_B0) ===
              ocp_get_le32(status, OCP_OFF_IFS_READ_INDEX_B0)))
            `uvm_error("OCP_LOCAL_FIFO", {label, ": full capacity must have equal modulo indices."})
    endtask

    protected task ocp_local_do_full_nak_ping_retry();
        bit [7:0] expected[$], retry_payload[$];
        cb_t::packet_record_t reply, record;
        logic [15:0] generation;
        int unsigned pending_first_record;
        // Image remainder keeps the blocked request legal. Full publication,
        // not an autonomous firmware consumer, releases the first batch.
        ocp_local_do_reset_and_check_fifo(
            (capacity_bytes + write_chunk_bytes) / 4, "FULL_RESET");
        ocp_local_do_fill_and_check_commits(
            capacity_bytes, expected, "FILL_ADVERTISED_CAPACITY", 1'b1);
        ocp_local_do_read_and_check_flags(1, 0, "FULL_EQUAL_INDICES");
        ocp_stall_do_read_and_check_device_status("FULL_NO_PROTOCOL_ERROR");
        ocp_stall_note_check_completed("LOCAL_1_FILL_RUNTIME_CAPACITY");

        for (int unsigned i = 0; i < write_chunk_bytes; i++)
            retry_payload.push_back(8'(8'hC7 ^ i));
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_stall_do_setup_and_check_ack(0, OCP_CMD_INDIRECT_FIFO_DATA,
            16'(retry_payload.size()), "FULL_PENDING", "OCP_LOCAL_PACKET");
        pending_first_record = checker.packet_callback.packet_count();
        ocp_local_do_data_and_get_reply(retry_payload, reply, "FULL_EXPLICIT_OUT");
        if (!(reply.pid_name === svt_usb_packet::NAK))
            `uvm_fatal("OCP_LOCAL_PACKET", "FULL explicit OUT/DATA must NAK without STALL/commit.")
        ocp_local_do_token_and_get_reply(svt_usb_packet::PING, reply, "FULL_PING");
        if (!(reply.pid_name === svt_usb_packet::NAK))
            `uvm_fatal("OCP_LOCAL_PACKET", "FULL PING must NAK.")
        // No USB status reads here: any new SETUP would discard this request.
        // Reject even an extra delayed accepting response before the drain.
        for (int unsigned i = pending_first_record;
             i < checker.packet_callback.packet_count(); i++) begin
            record = checker.packet_callback.get_packet(i);
            if ((record.direction === cb_t::PACKET_RX) &&
                !(record.pid_name === svt_usb_packet::SOF) &&
                !(record.pid_name === svt_usb_packet::NAK))
                `uvm_fatal("OCP_LOCAL_PACKET", "FULL history accepted DATA or reported protocol STALL before drain.")
        end
        ocp_stall_note_check_completed("LOCAL_2_FULL_OUT_NAK_REQUEST_RETAINED");
        // The entire published batch is drained, even if a single DWORD
        // would suffice for space. payload_available gates CPUif access/ready.
        // Model consumption precedes final window parsing, but explicit
        // chronological NAK checks above forbid any pre-drain acceptance.
        ocp_local_do_drain_and_check_content(expected, "FULL_CONFIRMED_DRAIN");
        ocp_local_do_ping_and_check_ready("DRAINED_PING");
        ocp_local_do_data_and_get_reply(retry_payload, reply, "SAME_DATA1_RETRY");
        ocp_local_check_accepted_reply(reply, "SAME_DATA1_RETRY");
        ocp_local_do_status_and_check_completion("SAME_REQUEST_STATUS");
        ocp_local_do_close_and_check_fifo_window(
            generation, retry_payload.size(), retry_payload.size(), "FULL_RETRY");
        if ((checker.packet_callback.accepted_setup_count() != 1) ||
            (checker.packet_callback.count_pid(svt_usb_packet::DATA1, cb_t::PACKET_TX) != 2))
            `uvm_fatal("OCP_LOCAL_PACKET", "FULL retry requires one SETUP and exactly NAKed/retried DATA1.")
        ocp_local_do_drain_and_check_content(retry_payload, "RETRY_TERMINAL_DRAIN");
        ocp_local_do_read_and_check_flags(0, 1, "FULL_RETRY_EMPTY");
        ocp_stall_do_read_and_check_device_status("FULL_RETRY_NO_PROTOCOL_ERROR");
        ocp_stall_note_check_completed("LOCAL_3_PING_TRANSITION_EXACT_RETRY_AND_DRAIN");
    endtask

    protected task ocp_local_do_close_and_check_pending_fifo_reset(
        input logic [15:0] generation, input int unsigned length,
        input int unsigned expected_committed, input string label);
        if (fifo_window_pending)
            `uvm_fatal("OCP_LOCAL_FIFO", "Raw pending window was also registered as an automatic FIFO window.")
        // Preserve the actual PING-only history, including any mismatch.
        // The model may reject that history; never convert it into a valid
        // completed transfer. Retain the unfinished owner until explicit reset.
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        fifo_scoreboard.observe_fifo_window(checker.packet_callback,
            generation, 7'(dev_addr_v), length, 1'b1, 1'b0, 1'b1);
        if ((fifo_packet_model.committed_byte_count() != expected_committed) ||
            (fifo_packet_model.partial_byte_count() != 0))
            `uvm_fatal("OCP_LOCAL_FIFO", "Near-full PING-only request changed modeled content.")
        ocp_local_do_reset_and_check_fifo(1, label);
    endtask

    protected task ocp_local_do_near_full_liveness();
        bit [7:0] prefix[$], tail[$], expected[$];
        logic [15:0] generation;
        cb_t::packet_record_t reply;
        bit published;
        int unsigned committed;
        // Leave one DWORD: insufficient for PING's maximum packet policy,
        // yet sufficient for a legal terminal actual-size DATA packet.
        ocp_local_do_reset_and_check_fifo(capacity_bytes / 4, "NEAR_FULL_RESET");
        ocp_local_do_fill_and_check_commits(capacity_bytes - 4, prefix, "NEAR_FULL_PREFIX");
        ocp_local_do_read_and_check_flags(0, 0, "NEAR_FULL_BASELINE");
        tail = '{8'h19, 8'hD2, 8'h63, 8'hA4};
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_stall_do_setup_and_check_ack(0, OCP_CMD_INDIRECT_FIFO_DATA,
            16'(tail.size()), "NEAR_FULL_PENDING", "OCP_LOCAL_PACKET");
        ocp_local_do_token_and_get_reply(svt_usb_packet::PING, reply, "NEAR_FULL_PING");
        if (!(reply.pid_name === svt_usb_packet::NAK)) begin
            // USB 2.0 8.5.1: PING ACK requires wMaxPacketSize space;
            // a short remaining control payload does not relax that verdict.
            `uvm_error("OCP_LOCAL_PACKET",
                $sformatf("LOCAL_4 NEAR_FULL_PING reply=%s(0x%0h) expected=NAK: model_free_bytes=%0d packet_bytes=%0d capacity_bytes=%0d model_committed_bytes=%0d model_partial_bytes=%0d request_bytes=%0d payload_available=%0b. Maximum-packet PING requirement failed; LOCAL_4 is not credited.",
                    reply.pid_name.name(), reply.pid_name,
                    fifo_packet_model.free_byte_count(), packet_bytes,
                    capacity_bytes, fifo_packet_model.committed_byte_count(),
                    fifo_packet_model.partial_byte_count(), tail.size(),
                    semantics_vif.recovery_payload_available))
            // No OUT DATA or firmware byte command has been issued for this
            // request. Isolate the failure without pretending readiness or
            // progress, then let the separate short/negative cases execute.
            ocp_local_do_close_and_check_pending_fifo_reset(
                generation, tail.size(), prefix.size(), "NEAR_FULL_PING_MISMATCH_RESET");
            return;
        end
        ocp_local_wait_publication(1'b1, published);
        if (published) begin
            ocp_local_do_drain_and_check_content(prefix, "NEAR_FULL_PUBLISHED_DRAIN");
            ocp_local_do_ping_and_check_ready("NEAR_FULL_DRAINED_PING");
            expected = tail;
            committed = tail.size();
        end else begin
            // The near-full/PING-NAK state IS reached. Publication stayed low
            // for the independent bound, so no permitted consumer command can
            // establish drain progress. This is a liveness gap, NOT an
            // unreachable-state claim or an executable liveness pass.
            `uvm_warning("OCP_LOCAL_LIVENESS_UNCLOSED",
                "LOCAL_4: near-full/PING-NAK reached with 4 free bytes; payload_available did not assert within 200us, prohibiting firmware drain. Bounded progress is unclosed: block/formal must establish publication/consumer progress or specify required host intervention, and cover published near-full drain plus eventual PING readiness. This is not a pass.")
            // USB 2.0 8.5.1/8.5.1.1: after PING-NAK the host must remain
            // in PING until ACK; direct short OUT is NOT a legal recovery.
            // End capture with the owner still pending, then explicitly reset
            // via FIFO_CTRL. No accepted DATA or partial bytes are abandoned.
            // This cleanup intentionally discards the unpublished prefix:
            // it asserts neither preservation across interruption nor drain
            // progress. The separate short test never follows PING-NAK.
            ocp_local_do_close_and_check_pending_fifo_reset(
                generation, tail.size(), prefix.size(), "NEAR_FULL_GAP_DISPOSITION_RESET");
            return;
        end
        // Only a confirmed drain followed by PING ACK reaches this DATA.
        // Complete the SAME request, without a replacement SETUP/reset.
        ocp_local_do_data_and_get_reply(tail, reply, "NEAR_FULL_TERMINAL_DATA");
        ocp_local_check_accepted_reply(reply, "NEAR_FULL_TERMINAL_DATA");
        ocp_local_do_status_and_check_completion("NEAR_FULL_STATUS");
        ocp_local_do_close_and_check_fifo_window(
            generation, tail.size(), committed, "NEAR_FULL_COMPLETE");
        ocp_local_do_drain_and_check_content(expected, "NEAR_FULL_TERMINAL_DRAIN");
        ocp_local_do_read_and_check_flags(0, 1, "NEAR_FULL_EMPTY");
        ocp_stall_do_read_and_check_device_status("NEAR_FULL_NO_PROTOCOL_ERROR");
        ocp_stall_note_check_completed("LOCAL_4_REACHABLE_PUBLISHED_NEAR_FULL_DRAIN");
    endtask

    protected task ocp_local_do_short_final_packet();
        bit [7:0] expected[$], tail[$];
        // OCP 8.2.5/9.2: DWORD-aligned payload avoids adding padding policy.
        // Image length comes from the protocol control request, not firmware.
        ocp_local_do_reset_and_check_fifo(capacity_bytes / 4, "SHORT_RESET");
        ocp_local_do_fill_and_check_commits(capacity_bytes - 4, expected, "SHORT_PREFIX");
        if ((fifo_packet_model.free_byte_count() != 4) ||
            (fifo_packet_model.free_byte_count() >= write_chunk_bytes) ||
            (fifo_packet_model.free_byte_count() >= packet_bytes))
            `uvm_fatal("OCP_LOCAL_CAPS", "Short actual-size admission precondition was not established.")
        ocp_local_do_read_and_check_flags(0, 0, "SHORT_BEFORE");
        tail = '{8'hB1, 8'h42, 8'h93, 8'hE4};
        // Direct OUT/DATA, without automatic PING masking actual-size admission.
        ocp_local_do_write_and_check_commit(tail, "SHORT_ACTUAL_SIZE_ADMISSION");
        foreach (tail[i]) expected.push_back(tail[i]);
        ocp_local_do_drain_and_check_content(expected, "SHORT_TERMINAL_BYTE_EXACT_DRAIN");
        ocp_local_do_read_and_check_flags(0, 1, "SHORT_EMPTY");
        ocp_stall_do_read_and_check_device_status("SHORT_NO_PROTOCOL_ERROR");
        ocp_stall_note_check_completed("LOCAL_5_SHORT_FINAL_PACKET");
    endtask

    protected task ocp_local_do_invalid_length_and_check_recovery(
        input int unsigned length, input int unsigned image_dwords,
        input string label);
        bit [7:0] payload[$], response[$];
        bit [7:0] rc_before[$], fc_before[$], fs_before[$];
        bit [7:0] rc_after[$], fc_after[$], fs_after[$];
        ocp_local_do_reset_and_check_fifo(image_dwords, {label, "_RESET"});
        // Empty isolated state prevents the interruption FIFO-flush defect
        // from being confused with the invalid-length verdict.
        ocp_stall_do_read_and_check_device_status({label, "_CLEAN_CODE"});
        ocp_stall_do_read_and_check_command_state(
            rc_before, fc_before, fs_before, {label, "_BEFORE"});
        repeat (length) payload.push_back(8'(8'h76 ^ payload.size()));
        // OCP Recovery v1.1 8.2.5, 8.5.1 and 9.2: exact length error 03.
        // In particular, do NOT accommodate the known image-remainder
        // rejection issue by expecting NAK, success or a different error.
        ocp_stall_do_request_and_check_stall(0, OCP_CMD_INDIRECT_FIFO_DATA,
            16'(length), payload, OCP_PROTOCOL_ERROR_LENGTH, label);
        ocp_stall_do_probe_and_check_all_tokens({label, "_PERSISTENT"});
        ocp_stall_do_read_and_check_device_status({label, "_EXACT_CODE03"});
        ocp_stall_do_read_and_check_device_status({label, "_CODE_CLEAR"});
        ocp_stall_do_read_and_check_command_state(
            rc_after, fc_after, fs_after, {label, "_AFTER"});
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after) ||
            (fifo_packet_model.committed_byte_count() != 0) ||
            (fifo_packet_model.partial_byte_count() != 0) ||
            !fifo_packet_model.lifecycle_idle())
            `uvm_error("OCP_LOCAL_FIFO", {label, ": rejected length changed state or committed bytes."})
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_PROT_CAP, response, {label, "_LEGAL_RECOVERY"});
        ocp_stall_note_check_completed(label);
    endtask

    virtual task body();
        bit [7:0] status[$];
        logic [7:0] ignored_data;
        int unsigned fifo_dwords;
        ocp_stall_do_initialize_and_check_transport();
        if (!agent_capabilities[OCP_CAP_INDIRECT_FIFO])
            `uvm_fatal("OCP_LOCAL_CAPS", "Local FIFO campaign requires advertised FIFO support.")
        packet_bytes = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_packet_size;
        // USB 2.0 5.5.3, not a DUT-derived constant.
        if (packet_bytes != HS_CONTROL_PACKET_BYTES)
            `uvm_fatal("OCP_LOCAL_CAPS", "Local HS FIFO campaign requires USB HS EP0 MPS=64.")
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_INDIRECT_FIFO_STATUS, status, "LOCAL_RUNTIME_CAPABILITIES");
        fifo_dwords = ocp_get_le32(status, OCP_OFF_IFS_FIFO_SIZE_B0);
        maximum_transfer_dwords = ocp_get_le32(status, OCP_OFF_IFS_MAX_TRANSFER_B0);
        if ((fifo_dwords < 2) || (fifo_dwords > (32'hFFFF_FFFF / 8)) ||
            (maximum_transfer_dwords == 0) ||
            (maximum_transfer_dwords > (32'hFFFF_FFFF / 4)) ||
            (wMaxWrTransferSize >= 16'hFFFF))
            `uvm_fatal("OCP_LOCAL_CAPS", "Unsupported/invalid runtime FIFO or USB write limits.")
        capacity_bytes = fifo_dwords * 4;
        write_chunk_bytes = packet_bytes;
        if (write_chunk_bytes > wMaxWrTransferSize)
            write_chunk_bytes = wMaxWrTransferSize;
        if (write_chunk_bytes > maximum_transfer_dwords * 4)
            write_chunk_bytes = maximum_transfer_dwords * 4;
        if (write_chunk_bytes > capacity_bytes) write_chunk_bytes = capacity_bytes;
        write_chunk_bytes = (write_chunk_bytes / 4) * 4;
        if (write_chunk_bytes <= 4)
            `uvm_fatal("OCP_LOCAL_CAPS", "Runtime limits cannot establish short/remainder test preconditions.")
        p_sequencer.usb_20_pkt_sequencer.reconfigure(usb_cfg);
        raw_response_callback =
            caliptra_ss_usb_ocp_raw_response_callback::type_id::create(
                "raw_response_callback");
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::add(
            host_agent_h.prot, raw_response_callback);
        ocp_local_do_full_nak_ping_retry();
        // verilog_lint: waive plusarg-assignment
        if ($test$plusargs("USB_OCP_CHECK_NEAR_FULL_PING")) begin
            `uvm_info("OCP_LOCAL_CONFORMANCE",
                {"LOCAL_4 enabled: strict near-full PING checking; ",
                 "USB-PING-001 remains a documented compliance deviation."},
                UVM_NONE)
            ocp_local_do_near_full_liveness();
        end else begin
            `uvm_info("OCP_LOCAL_WAIVER",
                {"LOCAL_4 stimulus/checks omitted under USB-PING-001; no coverage credit. ",
                 "Enable +USB_OCP_CHECK_NEAR_FULL_PING to exercise the strict scenario. ",
                 "See docs/usb2_streaming_boot_spec/README.md Section 11.2."},
                UVM_NONE)
        end
        ocp_local_do_short_final_packet();
        // Negative cases last; each starts with an empty isolated FIFO.
        ocp_local_do_invalid_length_and_check_recovery(
            0, 1, "LOCAL_6_ZERO_LENGTH");
        ocp_local_do_invalid_length_and_check_recovery(
            int'(wMaxWrTransferSize) + 1,
            (int'(wMaxWrTransferSize) + 4) / 4, "LOCAL_6_MAXWR_PLUS_ONE");
        // Eight bytes is within all discovered packet/write/transfer limits
        // above, but exceeds this protocol-programmed one-DWORD image.
        ocp_local_do_invalid_length_and_check_recovery(
            8, 1, "LOCAL_6_IMAGE_REMAINDER");
        ocp_stall_do_final_read_and_check_completion("FIFO_LOCAL_BEHAVIOR");
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::delete(
            host_agent_h.prot, raw_response_callback);
        ocp_stall_execute_fw_command(semantics_vif.FW_COMMAND_FLOW_COMPLETE,
            semantics_vif.FW_STATE_FLOW_COMPLETE, ignored_data,
            "LOCAL_FINAL_COMPLETION", "OCP_LOCAL_FW");
    endtask
endclass

`endif
