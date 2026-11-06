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

`ifndef CALIPTRA_SS_USB_OCP_INTERRUPTED_TRANSFER_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_INTERRUPTED_TRANSFER_SEQUENCE_SVH

class caliptra_ss_usb_ocp_malformed_timeout_catcher extends uvm_report_catcher;
    bit armed;
    int unsigned expected_timeouts;

    function new(string name = "ocp_malformed_timeout_catcher");
        super.new(name);
    endfunction

    virtual function action_e catch();
        if (armed && (expected_timeouts == 0) &&
            (get_severity() == UVM_ERROR) &&
            (get_id() == {"register_fail:LINK 20 TIMING CHECKS:COMMON:",
                          "tend_to_end_delay_check"})) begin
            expected_timeouts++;
            `uvm_info("OCP_ABORT_EXPECTED_NO_RESPONSE",
                "Observed expected native no-response timeout for malformed OUT DATA.",
                UVM_NONE)
            return CAUGHT;
        end
        return THROW;
    endfunction
endclass

class caliptra_ss_usb_ocp_interrupted_transfer_sequence
    extends caliptra_ss_usb_ocp_persistent_stall_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_interrupted_transfer_sequence)

    typedef caliptra_ss_usb_ocp_arbiter_packet_callback cb_t;
    localparam int unsigned COMMITTED_DWORDS = 2;
    localparam int unsigned MALFORMED_REQUEST_BYTES = 8;
    // Give maxWr+1 room in the image so rejection tests the USB envelope,
    // not a simultaneous image-remainder violation. Complete with legal pushes.
    localparam int unsigned IMAGE_DWORDS =
        COMMITTED_DWORDS + (HS_CONTROL_PACKET_BYTES + 4) / 4 + 1;
    localparam int unsigned TRUNCATION_BYTE_OFFSET = 4;
    localparam int TRUNCATION_BIT_OFFSET = 3;
    // Same infrastructure liveness budget as the normal transfer waiter.
    localparam time RAW_ACCEPTANCE_BOUND = 2ms;
    // Pace NAK retries by one HS microframe so bounded capture retains the
    // whole request. Elapsed time never establishes endpoint readiness.
    localparam time RAW_RETRY_INTERVAL = 125us;
    protected int unsigned raw_requests;
    protected int unsigned control_packet_bytes;

    function new(string name = "caliptra_ss_usb_ocp_interrupted_transfer_sequence");
        super.new(name);
    endfunction

    protected task ocp_abort_execute_fw_command(
        input logic [7:0] opcode, input logic [7:0] expected_state,
        output logic [7:0] data, input string label);
        ocp_stall_execute_fw_command(opcode, expected_state, data, label);
    endtask

    protected task ocp_abort_check_batch_aborted(
        input bit expected, input string label,
        input bit diagnostic_only = 1'b0);
        logic [7:0] observed;
        ocp_abort_execute_fw_command(FW_READ_BATCH_ABORTED,
            semantics_vif.FW_STATE_PATH_READY, observed, label);
        if (diagnostic_only) begin
            // No local contract requires BATCH_ABORTED for rejected DATA
            // which never acquired packet-qualified partial bytes.
            `uvm_info("OCP_ABORT_BATCH",
                $sformatf("%s BATCH_ABORTED=%02h (diagnostic only).",
                    label, observed), UVM_LOW)
        end else if (observed !== {7'b0, expected})
            `uvm_error("OCP_ABORT_BATCH",
                $sformatf("%s BATCH_ABORTED=%02h expected=%0b (local contract).",
                    label, observed, expected))
    endtask

    protected task ocp_abort_do_commit_and_check_baseline(
        input int unsigned scenario, ref bit [7:0] committed[$],
        ref bit [7:0] status[$], input string label);
        logic [15:0] generation;
        caliptra_ss_usb_ocp_xfer_result_e result;
        committed.delete();
        for (int unsigned i = 0; i < COMMITTED_DWORDS * 4; i++)
            committed.push_back(8'(8'h31 + scenario * 17 + i));
        if (wMaxWrTransferSize < committed.size())
            `uvm_fatal("OCP_ABORT_CAPS", "Advertised write envelope cannot hold the baseline.")
        fifo_model_configured = 1'b0;
        ocp_stall_do_configure_and_check_fifo(IMAGE_DWORDS, {label, "_RESET"});
        ocp_abort_check_batch_aborted(1'b0, {label, "_RESET_ABORT_FLAG"});
        ocp_arb_open_observation_window(generation);
        ocp_do_fifo_data_write(committed, result, {label, "_COMMIT"});
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        ocp_stall_check_single_accepted_setup({label, "_COMMIT"});
        if ((fifo_packet_model.committed_byte_count() != committed.size()) ||
            (fifo_packet_model.partial_byte_count() != 0))
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Baseline lacks packet/status-qualified commit.")
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_INDIRECT_FIFO_STATUS, status, {label, "_BASELINE"});
    endtask

    protected task ocp_abort_do_check_preservation_and_drain(
        ref bit [7:0] committed[$], ref bit [7:0] before_status[$],
        input bit expected_abort, input string label,
        input bit diagnostic_abort_only = 1'b0);
        bit [7:0] after_status[$];
        bit [7:0] expected[$], filler[$];
        logic [7:0] value;
        logic [15:0] generation;
        caliptra_ss_usb_ocp_xfer_result_e result;
        int unsigned chunk_bytes, maximum_transfer, fifo_size;
        bit payload_ready;
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_INDIRECT_FIFO_STATUS, after_status, {label, "_AFTER"});
        if (before_status != after_status)
            `uvm_error("OCP_ABORT_FIFO", {label, ": abort/stall changed committed FIFO state."})
        ocp_abort_check_batch_aborted(expected_abort, {label, "_ABORT_FLAG"}, diagnostic_abort_only);
        // Complete the configured image only after checking interruption
        // evidence. Keep the retained prefix in place; never reset to drain.
        // OCP Recovery v1.1 8.2.5 bounds each push by the discovered limits.
        maximum_transfer = ocp_get_le32(after_status, OCP_OFF_IFS_MAX_TRANSFER_B0);
        fifo_size = ocp_get_le32(after_status, OCP_OFF_IFS_FIFO_SIZE_B0);
        if ((maximum_transfer == 0) || (fifo_size <= IMAGE_DWORDS))
            `uvm_fatal("OCP_ABORT_CAPS", "Configured image cannot be completed without draining.")
        expected = committed;
        while (expected.size() < IMAGE_DWORDS * 4) begin
            chunk_bytes = IMAGE_DWORDS * 4 - expected.size();
            if (chunk_bytes > wMaxWrTransferSize) chunk_bytes = wMaxWrTransferSize;
            if (chunk_bytes / 4 > maximum_transfer) chunk_bytes = maximum_transfer * 4;
            chunk_bytes = (chunk_bytes / 4) * 4;
            if (chunk_bytes == 0)
                `uvm_fatal("OCP_ABORT_CAPS", "No legal DWORD-sized image completion push.")
            filler.delete();
            repeat (chunk_bytes) begin
                filler.push_back(8'(8'hD7 ^ expected.size()));
                expected.push_back(filler[$]);
            end
            ocp_arb_open_observation_window(generation);
            ocp_do_fifo_data_write(filler, result, {label, "_COMPLETE_IMAGE"});
            ocp_arb_check_and_close_observation_window(generation, 4'h0);
            ocp_stall_check_single_accepted_setup({label, "_COMPLETE_IMAGE"});
            if ((fifo_packet_model.committed_byte_count() != expected.size()) ||
                (fifo_packet_model.partial_byte_count() != 0))
                `uvm_fatal("OCP_ABORT_EVIDENCE", "Image completion lacks packet-qualified commits.")
        end
        // Existing architectural output, not a new internal FIFO probe.
        payload_ready = 1'b0;
        fork : wait_payload_ready
            begin
                wait (semantics_vif.recovery_payload_available === 1'b1);
                payload_ready = 1'b1;
            end
            begin
                #(FW_SERVICE_BOUND);
            end
        join_any
        disable wait_payload_ready;
        if (!payload_ready)
            `uvm_fatal("OCP_ABORT_FW", {label, ": completed image did not release payload."})
        foreach (expected[i]) begin
            ocp_abort_execute_fw_command(FW_READ_FIFO_BYTE,
                semantics_vif.FW_STATE_PATH_READY, value, label);
            if (value !== expected[i])
                `uvm_error("OCP_ABORT_CONTENT",
                    $sformatf("%s retained byte[%0d]=%02h expected=%02h.",
                        label, i, value, expected[i]))
        end
        fifo_scoreboard.observe_fifo_drain(IMAGE_DWORDS);
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_INDIRECT_FIFO_STATUS, after_status, {label, "_DRAINED"});
        if (after_status.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
            `uvm_fatal("OCP_ABORT_FIFO", {label, ": truncated drained FIFO status."})
        if ((after_status[OCP_OFF_IFS_STATUS] & OCP_IFS_EMPTY_MASK) == 0)
            `uvm_error("OCP_ABORT_FIFO", {label, ": unexpected data remains after exact drain."})
        ocp_abort_check_batch_aborted(expected_abort, {label, "_STICKY_ABORT_FLAG"}, diagnostic_abort_only);
        ocp_stall_note_check_completed(label);
    endtask

    protected task ocp_abort_do_setup_and_check_ack(
        input bit dir_in, input ocp_cmd_t command,
        input bit [15:0] length, input string label);
        ocp_stall_do_setup_and_check_ack(dir_in, command, length, label);
        raw_requests++;
    endtask

    protected task ocp_abort_wait_reply(
        input int unsigned first_record, output cb_t::packet_record_t reply,
        input string label);
        ocp_stall_wait_reply(first_record, reply, label);
    endtask

    protected task ocp_abort_do_accept_in_data(
        output cb_t::packet_record_t reply, input string label);
        bit [7:0] empty_payload[$];
        int unsigned first_record;
        time deadline;
        deadline = $time + RAW_ACCEPTANCE_BOUND;
        while ($time < deadline) begin
            first_record = checker.packet_callback.packet_count();
            ocp_stall_do_transmit_packet_and_check_completion(
                svt_usb_packet::IN, empty_payload);
            ocp_abort_wait_reply(first_record, reply, label);
            if (reply.pid_name == svt_usb_packet::NAK) begin
                ocp_abort_pace_retry(deadline);
                continue;
            end
            if ((reply.pid_name != svt_usb_packet::DATA1) || (reply.data_length == 0))
                `uvm_fatal("OCP_ABORT_EVIDENCE", {label, ": expected first control DATA1."})
            ocp_stall_do_transmit_packet_and_check_completion(
                svt_usb_packet::ACK, empty_payload);
            return;
        end
        `uvm_fatal("OCP_ABORT_EVIDENCE", {label, ": IN acceptance exceeded its liveness bound."})
    endtask

    protected task ocp_abort_pace_retry(input time deadline);
        time interval;
        if ($time >= deadline) return;
        interval = deadline - $time;
        if (interval > RAW_RETRY_INTERVAL) interval = RAW_RETRY_INTERVAL;
        #(interval);
    endtask

    protected task ocp_abort_do_control_in_interruption();
        logic [15:0] generation;
        bit [7:0] committed[$], before_status[$], response[$];
        cb_t::packet_record_t reply;
        ocp_abort_do_commit_and_check_baseline(
            1, committed, before_status, "CONTROL_IN");
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_abort_do_setup_and_check_ack(
            1, OCP_CMD_DEVICE_STATUS, wMaxRdTransferSize, "CONTROL_IN");
        ocp_abort_do_accept_in_data(reply, "CONTROL_IN_DATA");
        // USB 2.0 8.5.3: replace the control read before its OUT status stage.
        ocp_abort_do_setup_and_check_ack(
            1, OCP_CMD_PROT_CAP, wMaxRdTransferSize, "CONTROL_IN_REPLACEMENT");
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        fifo_scoreboard.observe_fifo_abort(1'b0);
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_PROT_CAP, response, "CONTROL_IN_CONTINUATION");
        ocp_stall_do_read_and_check_device_status("CONTROL_IN_NO_ERROR");
        ocp_abort_do_check_preservation_and_drain(
            committed, before_status, 1'b0, "CONTROL_IN_PRESERVES_COMMITTED");
    endtask

    protected task ocp_abort_do_oversize_fifo_rejection();
        logic [15:0] generation;
        bit [7:0] committed[$], before_status[$], payload[$], empty_payload[$];
        bit [7:0] rc_before[$], fc_before[$], fs_before[$];
        bit [7:0] rc_after[$], fc_after[$], fs_after[$];
        cb_t::packet_record_t reply;
        int unsigned request_bytes, first_record, packet_bytes;
        ocp_abort_do_commit_and_check_baseline(2, committed, before_status, "OCP_ABORT_004_OVERSIZE_PRESERVES_FIFO");
        if (wMaxWrTransferSize >= 16'hFFFF)
            `uvm_fatal("OCP_ABORT_CAPS", "maxWr+1 cannot be represented in USB wLength.")
        request_bytes = int'(wMaxWrTransferSize) + 1;
        if (IMAGE_DWORDS * 4 - committed.size() < request_bytes)
            `uvm_fatal("OCP_ABORT_CAPS", "Oversized USB request also exceeds image remainder.")
        packet_bytes = request_bytes;
        if (packet_bytes > control_packet_bytes) packet_bytes = control_packet_bytes;
        for (int unsigned i = 0; i < packet_bytes; i++)
            payload.push_back(8'(8'hB0 ^ i));
        ocp_stall_do_read_and_check_command_state(rc_before, fc_before, fs_before, "OVERSIZE_BEFORE");
        // OCP Recovery v1.1 8.5.1: wMaxWrTransferSize bounds the whole
        // request. Deliver DATA explicitly even when SETUP decoding rejects
        // it, without protocol-layer PING or automatic DATA retries.
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_abort_do_setup_and_check_ack(0, OCP_CMD_INDIRECT_FIFO_DATA, 16'(request_bytes), "OVERSIZE_FIFO");
        first_record = checker.packet_callback.packet_count();
        ocp_stall_do_transmit_packet_and_check_completion(svt_usb_packet::OUT, empty_payload);
        ocp_stall_do_transmit_packet_and_check_completion(svt_usb_packet::DATA1, payload);
        ocp_abort_wait_reply(first_record, reply, "OVERSIZE_FIFO_DATA");
        if (!(reply.pid_name === svt_usb_packet::STALL))
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Oversized FIFO DATA did not receive STALL.")
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        if (!checker.packet_callback.validate_control_stall(7'(dev_addr_v), 4'h0) ||
            (checker.packet_callback.count_pid(svt_usb_packet::DATA1,
                cb_t::PACKET_TX) != 1))
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Oversized request lacks one DATA/STALL history.")
        fifo_scoreboard.observe_fifo_window(checker.packet_callback, generation,
            7'(dev_addr_v), request_bytes, 1'b0);
        if ((fifo_packet_model.committed_byte_count() != committed.size()) ||
            (fifo_packet_model.partial_byte_count() != 0) ||
            !fifo_packet_model.lifecycle_idle())
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Oversized request changed modeled FIFO state.")
        stall_model.note_error(OCP_PROTOCOL_ERROR_LENGTH);
        void'(stall_model.require_stalled("OVERSIZE_FIFO"));
        ocp_stall_do_read_and_check_device_status("OVERSIZE_CODE03");
        ocp_stall_do_read_and_check_device_status("OVERSIZE_CODE_CLEAR");
        ocp_stall_do_read_and_check_command_state(rc_after, fc_after, fs_after, "OVERSIZE_AFTER");
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after))
            `uvm_error("OCP_ABORT_FIFO", "Oversized request changed command/FIFO state.")
        ocp_abort_do_check_preservation_and_drain(committed, before_status, 1'b0, "OVERSIZE_PRESERVES_COMMITTED");
    endtask

    protected task ocp_abort_do_malformed_fifo_rejection();
        logic [15:0] generation;
        bit [7:0] committed[$], before_status[$], payload[$], empty_payload[$];
        bit [7:0] response[$];
        cb_t::packet_record_t record;
        caliptra_ss_usb_ocp_malformed_timeout_catcher timeout_catcher;
        int unsigned first_record, data_packets, out_packets;
        bit data_intent_valid;
        ocp_abort_do_commit_and_check_baseline(
            4, committed, before_status, "OCP_ABORT_005_MALFORMED_DATA_PRESERVES_FIFO");
        if ((wMaxWrTransferSize < MALFORMED_REQUEST_BYTES) ||
            (control_packet_bytes < MALFORMED_REQUEST_BYTES) ||
            (ocp_get_le32(before_status, OCP_OFF_IFS_MAX_TRANSFER_B0) <
                (MALFORMED_REQUEST_BYTES + 3) / 4))
            `uvm_fatal("OCP_ABORT_CAPS", "No legal single-packet malformed FIFO request.")
        for (int unsigned i = 0; i < MALFORMED_REQUEST_BYTES; i++)
            payload.push_back(8'(8'hA6 ^ i));
        ocp_arb_open_observation_window(generation);
        raw_response_callback.enabled = 1'b1;
        ocp_abort_do_setup_and_check_ack(
            0, OCP_CMD_INDIRECT_FIFO_DATA, MALFORMED_REQUEST_BYTES, "MALFORMED_FIFO");
        first_record = checker.packet_callback.packet_count();
        timeout_catcher = new();
        uvm_report_cb::add(host_agent_h.link, timeout_catcher);
        timeout_catcher.armed = 1'b1;
        ocp_stall_do_transmit_packet_and_check_completion(
            svt_usb_packet::OUT, empty_payload);
        // Trust this waveform-qualified VIP truncation on the current HS PHY.
        // Requalify in waveforms if stimulus, injection settings, VIP version,
        // or PHY configuration changes; link callbacks retain packet intent.
        // Deterministic verification that the packet corruption actually occurs
        // at the DUT boundary is not provable via current VIP features, so changes
        // to stimulus or configuration require reverification that the VIP-requested
        // corruption is actually propagating to physical stimulus.
        ocp_stall_do_transmit_packet_and_check_completion(
            svt_usb_packet::DATA1, payload, 1'b0, 1'b1,
            TRUNCATION_BYTE_OFFSET, TRUNCATION_BIT_OFFSET);
        // USB 2.0 8.7.1/8.7.2: ignore corrupt packets and discard data.
        // Observe the entire no-response bound BEFORE any retry/new SETUP.
        // The raw response callback prevents automatic protocol recovery.
        #(PACKET_RESPONSE_BOUND);
        timeout_catcher.armed = 1'b0;
        uvm_report_cb::delete(host_agent_h.link, timeout_catcher);
        if (timeout_catcher.expected_timeouts != 1)
            `uvm_error("OCP_ABORT_EVIDENCE",
                "Malformed OUT did not produce its single native no-response timeout.")
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        data_packets = 0;
        out_packets = 0;
        data_intent_valid = 1'b0;
        if (checker.packet_callback.overflowed())
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Malformed FIFO packet history overflowed.")
        for (int unsigned i = first_record;
             i < checker.packet_callback.packet_count(); i++) begin
            record = checker.packet_callback.get_packet(i);
            if (record.pid_name === svt_usb_packet::SOF) continue;
            if (!(record.generation === generation) || !record.target_valid ||
                !(record.device_address === 7'(dev_addr_v)) ||
                !(record.endpoint_number === 4'd0))
                `uvm_fatal("OCP_ABORT_EVIDENCE", "Malformed FIFO evidence has invalid attribution.")
            if (record.direction === cb_t::PACKET_RX)
                `uvm_fatal("OCP_ABORT_EVIDENCE",
                    $sformatf("Malformed FIFO DATA received %s before recovery; no handshake allowed.",
                        record.pid_name.name()))
            if (record.pid_name === svt_usb_packet::DATA1) begin
                if (out_packets != 1)
                    `uvm_fatal("OCP_ABORT_EVIDENCE", "Malformed DATA lacks its single preceding OUT.")
                data_packets++;
                `uvm_info("OCP_ABORT_PACKET",
                    $sformatf("Malformed link DATA1: bytes=%0d retry=%0d crc_error=%0b data_error=%0b.",
                        record.data_length, record.retry_number,
                        record.crc_error_detected, record.data_error_detected),
                    UVM_NONE)
                data_intent_valid =
                    (record.retry_number == 0) &&
                    (record.data_length == MALFORMED_REQUEST_BYTES);
            end else if (record.pid_name === svt_usb_packet::OUT) begin
                out_packets++;
                if ((data_packets != 0) || (record.retry_number != 0) ||
                    record.crc_error_detected || record.data_error_detected)
                    `uvm_fatal("OCP_ABORT_EVIDENCE", "Unexpected corrupt/retried OUT before recovery.")
            end else
                `uvm_fatal("OCP_ABORT_EVIDENCE", "Unexpected packet/retry before malformed recovery.")
        end
        if ((out_packets != 1) || (data_packets != 1) || !data_intent_valid)
            `uvm_fatal("OCP_ABORT_EVIDENCE",
                $sformatf("Malformed FIFO requires one OUT/DATA1 without retry: OUT/DATA=%0d/%0d intent=%0b.",
                    out_packets, data_packets, data_intent_valid))
        // Rejected DATA contributes no accepted partial bytes. In particular,
        // do not select owner_abort (which presumes an accepted partial batch).
        fifo_scoreboard.observe_fifo_window(checker.packet_callback, generation,
            7'(dev_addr_v), MALFORMED_REQUEST_BYTES, 1'b0, 1'b0, 1'b1);
        if ((fifo_packet_model.committed_byte_count() != committed.size()) ||
            (fifo_packet_model.partial_byte_count() != 0) ||
            !fifo_packet_model.lifecycle_idle())
            `uvm_fatal("OCP_ABORT_EVIDENCE", "Malformed DATA acquired packet-qualified FIFO bytes.")
        if (semantics_vif.recovery_payload_available !== 1'b0)
            `uvm_error("OCP_ABORT_FIFO", "Rejected DATA prematurely released the incomplete image.")
        ocp_abort_check_batch_aborted(1'b0, "MALFORMED_BEFORE_NEW_SETUP", 1'b1);
        // USB 2.0 8.5.3: explicitly replace the unfinished control transfer.
        ocp_arb_open_observation_window(generation);
        ocp_abort_do_setup_and_check_ack(
            1, OCP_CMD_PROT_CAP, wMaxRdTransferSize, "MALFORMED_REPLACEMENT");
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        ocp_stall_do_read_and_check_no_stall(
            OCP_CMD_PROT_CAP, response, "MALFORMED_CONTINUATION");
        ocp_stall_do_read_and_check_device_status("MALFORMED_NO_PROTOCOL_ERROR");
        ocp_abort_do_check_preservation_and_drain(
            committed, before_status, 1'b0, "MALFORMED_PRESERVES_COMMITTED", 1'b1);
    endtask

    virtual task body();
        bit [7:0] committed[$], before_status[$], payload[$];
        logic [7:0] ignored_data;
        uvm_report_server report_server;
        int unsigned qualification_errors;
        report_server = uvm_report_server::get_server();
        qualification_errors = report_server.get_severity_count(UVM_ERROR);
        ocp_stall_do_initialize_and_check_transport();
        control_packet_bytes =
            usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_packet_size;
        if (control_packet_bytes == 0)
            `uvm_fatal("OCP_ABORT_CAPS", "EP0 maximum packet size is zero.")
        if (!agent_capabilities[OCP_CAP_INDIRECT_FIFO])
            `uvm_fatal("OCP_ABORT_CAPS", "FIFO abort test requires advertised FIFO support.")
        p_sequencer.usb_20_pkt_sequencer.reconfigure(usb_cfg);
        raw_response_callback =
            caliptra_ss_usb_ocp_raw_response_callback::type_id::create(
                "raw_response_callback");
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::add(
            host_agent_h.prot, raw_response_callback);
        ocp_abort_do_control_in_interruption();
        if (report_server.get_severity_count(UVM_ERROR) != qualification_errors)
            `uvm_fatal("OCP_ABORT_PROFILE",
                "Nominal packet/content/FIFO checks failed; rejection stimulus is unqualified.")
        ocp_abort_do_oversize_fifo_rejection();
        ocp_abort_do_malformed_fifo_rejection();
        ocp_abort_do_commit_and_check_baseline( 3, committed, before_status, "RESERVED_COMMAND");
        payload = '{8'h00};
        ocp_stall_do_request_and_check_stall(0, RESERVED_COMMAND,
            payload.size(), payload, OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
            "RESERVED_COMMAND");
        ocp_stall_do_probe_and_check_all_tokens("RESERVED_COMMAND_PERSISTENCE");
        ocp_stall_do_read_and_check_device_status("RESERVED_COMMAND_CODE");
        ocp_stall_do_read_and_check_device_status("RESERVED_COMMAND_CODE_CLEAR");
        ocp_abort_do_check_preservation_and_drain(
            committed, before_status, 1'b0, "RESERVED_STALL_PRESERVES_COMMITTED");
        ocp_stall_do_final_read_and_check_completion("INTERRUPTED_TRANSFER");
        `uvm_info("OCP_ABORT",
            $sformatf("Completed abort campaign with %0d raw claimed SETUPs.", raw_requests),
            UVM_NONE)
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::delete(
            host_agent_h.prot, raw_response_callback);
        ocp_abort_execute_fw_command(semantics_vif.FW_COMMAND_FLOW_COMPLETE,
            semantics_vif.FW_STATE_FLOW_COMPLETE, ignored_data, "FINAL_COMPLETION");
    endtask
endclass

`endif
