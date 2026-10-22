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

`ifndef CALIPTRA_SS_USB_OCP_PERSISTENT_STALL_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_PERSISTENT_STALL_SEQUENCE_SV

class caliptra_ss_usb_ocp_persistent_stall_sequence
    extends caliptra_ss_usb_ocp_stall_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_persistent_stall_sequence)

    localparam time PACKET_RESPONSE_BOUND = 5us;
    localparam int unsigned PROBE_REPETITIONS = 2;
    // USB 2.0 Section 9.4.1, Table 9-6.
    localparam bit [7:0] CLEAR_FEATURE_REQUEST = 8'h01;
    localparam bit [15:0] ENDPOINT_HALT_FEATURE = 16'h0000;
    protected caliptra_ss_usb_ocp_raw_response_callback raw_response_callback;

    function new(string name = "caliptra_ss_usb_ocp_persistent_stall_sequence");
        super.new(name);
    endfunction

    protected task transmit_packet(
        input svt_usb_packet::pid_name_enum pid,
        ref bit [7:0] payload[$], input bit corrupt_crc = 1'b0);
        caliptra_ss_usb_ocp_directed_packet_sequence packet_sequence;
        bit transmitted;
        packet_sequence =
            caliptra_ss_usb_ocp_directed_packet_sequence::type_id::create(
                "packet_sequence");
        packet_sequence.pid = pid;
        packet_sequence.device_address = 7'(dev_addr_v);
        packet_sequence.endpoint_number = 0;
        packet_sequence.payload_bytes = payload;
        packet_sequence.corrupt_crc = corrupt_crc;
        packet_sequence.packet_configuration = usb_cfg;
        transmitted = 1'b0;
        fork : bounded_packet_transmission
            begin
                packet_sequence.start(p_sequencer.usb_20_pkt_sequencer);
                transmitted = 1'b1;
            end
            begin
                #(PACKET_RESPONSE_BOUND);
            end
        join_any
        disable bounded_packet_transmission;
        if (!transmitted) begin
            packet_sequence.kill();
            `uvm_fatal("OCP_STALL", "Directed packet did not complete within its bound.")
        end
    endtask

    protected task probe_stall(
        input svt_usb_packet::pid_name_enum pid, input string label);
        bit [7:0] payload[$];
        logic [15:0] generation;
        bit observed;
        int unsigned expected_packets;

        void'(stall_model.require_stalled(label));
        open_observation_window(generation);
        checker.expect_packet_only_window();
        raw_response_callback.enabled = 1'b1;
        transmit_packet(pid, payload);
        expected_packets = 2;
        if (pid == svt_usb_packet::OUT) begin
            // A stalled OUT still consists of token + DATA + device handshake.
            transmit_packet(svt_usb_packet::DATA1, payload);
            expected_packets++;
        end
        checker.packet_callback.wait_for_packet_count(
            expected_packets, PACKET_RESPONSE_BOUND, observed);
        if (!observed)
            `uvm_error("OCP_STALL", {label, ": response observation timed out."})
        // Snapshot collection keeps observation active after the first
        // response, so duplicate or delayed responses cannot escape checking.
        close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        if (!checker.packet_callback.check_stall_probe(
                pid, 7'(dev_addr_v), 4'h0, label))
            `uvm_error("OCP_STALL", {label, ": ordered token/STALL evidence mismatch."})
        mark_check(label);
    endtask

    protected task probe_all_tokens(input string label);
        for (int unsigned i = 0; i < PROBE_REPETITIONS; i++) begin
            probe_stall(svt_usb_packet::IN, $sformatf("%s_IN_%0d", label, i));
            probe_stall(svt_usb_packet::OUT, $sformatf("%s_OUT_%0d", label, i));
            probe_stall(svt_usb_packet::PING, $sformatf("%s_PING_%0d", label, i));
        end
    endtask

    protected task corrupt_setup_preserves_stall(
        input bit require_existing_stall = 1'b1);
        logic [15:0] generation;
        bit [7:0] setup_bytes[$];
        bit [7:0] empty_payload[$];
        bit [15:0] interface_index;

        interface_index = 16'(get_iface_num());
        // OCP Section 8.5.1 read PROT_CAP SETUP; only the token CRC is bad.
        setup_bytes = '{{1'b1, BMRT_TYPE_CLASS, BMRT_RECIPIENT_IFACE},
            OCP_BREQUEST_XFER, OCP_CMD_PROT_CAP, 8'h00,
            interface_index[7:0], interface_index[15:8],
            8'(wMaxRdTransferSize), 8'(wMaxRdTransferSize >> 8)};
        open_observation_window(generation);
        checker.expect_packet_only_window();
        raw_response_callback.enabled = 1'b1;
        transmit_packet(svt_usb_packet::SETUP, empty_payload, 1'b1);
        transmit_packet(svt_usb_packet::DATA0, setup_bytes);
        #(PACKET_RESPONSE_BOUND);
        close_observation_window(generation, 4'h0);
        raw_response_callback.enabled = 1'b0;
        if ((checker.packet_callback.accepted_setup_count() != 0) ||
            (checker.packet_callback.count_pid(svt_usb_packet::ACK,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) != 0))
            `uvm_error("OCP_STALL", "Corrupt SETUP unexpectedly received ACK.")
        if (checker.packet_callback.count_pid(svt_usb_packet::SETUP,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) != 1)
            `uvm_error("OCP_STALL", "Corrupt SETUP was not observed on the bus.")
        if (checker.packet_callback.corruption_count() != 1)
            `uvm_error("OCP_STALL", "Expected one on-wire CRC corruption marker.")
        if (require_existing_stall) begin
            probe_all_tokens("AFTER_CORRUPT_SETUP");
            mark_check("corrupt SETUP unaccepted; existing STALL retained");
        end else begin
            // A clean sticky-code baseline makes a spurious OCP checksum
            // code visible instead of hiding it behind first-code retention.
            read_status_and_check("CORRUPT_SETUP_NO_OCP_CODE");
            read_status_and_check("CORRUPT_SETUP_CODE_CLEAR");
            mark_check("USB CRC corruption creates no OCP checksum code");
        end
    endtask

    protected task clear_feature_recovery();
        logic [15:0] generation;
        caliptra_ss_usb_ocp_xfer_result_e result;
        bit [7:0] response[$];
        open_observation_window(generation);
        fork
            wait_xfer_done(host_agent_h, "CLEAR_FEATURE_EP0");
            do_control_xfer(
                .bm_request_type_dir(svt_usb_types::HOST_TO_DEVICE),
                .bm_request_type_type(svt_usb_types::STANDARD),
                .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
                .brequest_val(CLEAR_FEATURE_REQUEST),
                .wvalue(ENDPOINT_HALT_FEATURE), .windex(0), .wlength(0),
                .device_addr(dev_addr_v), .label("CLEAR_FEATURE_EP0"),
                .usb_cfg(usb_cfg));
        join
        close_observation_window(generation, 4'h1);
        require_accepted_setup("CLEAR_FEATURE_EP0");
        // USB 2.0 Sections 9.4.1/9.4.5 allow Request Error when EP0 has
        // no Halt feature. Its accepted SETUP, not its status, is the
        // protocol-STALL boundary required by Section 8.5.3.4.
        result = get_xfer_result(last_ctrl_seq_item);
        if (xfer_wait_timed_out ||
            ((result != OCP_XFER_SUCCESS) &&
             !checker.packet_callback.validate_control_stall(7'(dev_addr_v), 4'h0)))
            `uvm_error("OCP_STALL", "CLEAR_FEATURE did not complete or return a legal Request Error.")
        legal_read(OCP_CMD_PROT_CAP, response, "AFTER_CLEAR_FEATURE");
        read_status_and_check("CLEAR_FEATURE_RETAINED_CODE");
        read_status_and_check("CLEAR_FEATURE_CODE_CLEAR");
        mark_check("CLEAR_FEATURE ACKed SETUP recovery; legal OCP continuation");
    endtask

    virtual task body();
        bit [7:0] payload[$];
        bit [7:0] response[$];
        bit [7:0] rc_before[$], fc_before[$], fs_before[$];
        bit [7:0] rc_after[$], fc_after[$], fs_after[$];
        initialize_stall_transport();
        p_sequencer.usb_20_pkt_sequencer.reconfigure(usb_cfg);
        raw_response_callback =
            caliptra_ss_usb_ocp_raw_response_callback::type_id::create(
                "raw_response_callback");
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::add(
            host_agent_h.prot, raw_response_callback);
        snapshot_command_state(rc_before, fc_before, fs_before, "PERSIST_BASELINE");
        payload = '{8'h00};
        issue_stall(0, RESERVED_COMMAND, payload.size(), payload,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, "SETUP_DECODE_STALL");
        probe_all_tokens("SETUP_DECODE");
        corrupt_setup_preserves_stall();
        legal_read(OCP_CMD_PROT_CAP, response, "ACCEPTED_LEGAL_SETUP");
        read_status_and_check("DECODE_RETAINED_CODE");
        read_status_and_check("DECODE_CODE_CLEAR");
        snapshot_command_state(rc_after, fc_after, fs_after, "PERSIST_AFTER");
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after))
            `uvm_error("OCP_STALL", "Stalled/corrupt traffic changed command/FIFO state.")

        corrupt_setup_preserves_stall(1'b0);
        snapshot_command_state(rc_after, fc_after, fs_after, "CLEAN_CRC_AFTER");
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after))
            `uvm_error("OCP_STALL", "Corrupt SETUP changed command/FIFO state.")
        snapshot_command_state(rc_before, fc_before, fs_before, "DATA_BASELINE");
        payload = '{8'h00, RESERVED_IMAGE_SELECTION, 8'h00};
        issue_stall(0, OCP_CMD_RECOVERY_CTRL, payload.size(), payload,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_PARAMETER, "DATA_DECODE_STALL", 1);
        probe_all_tokens("DATA_DECODE");
        read_status_and_check("DATA_DECODE_RETAINED_CODE");
        read_status_and_check("DATA_DECODE_CODE_CLEAR");
        snapshot_command_state(rc_after, fc_after, fs_after, "DATA_AFTER");
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after))
            `uvm_error("OCP_STALL", "Rejected DATA-stage command changed command/FIFO state.")

        payload = '{8'h00};
        issue_stall(0, RESERVED_COMMAND, payload.size(), payload,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, "CLEAR_FEATURE_PRECONDITION");
        clear_feature_recovery();

        issue_stall(0, RESERVED_COMMAND, payload.size(), payload,
            OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND, "NEW_INVALID_FIRST");
        issue_stall(0, OCP_CMD_RECOVERY_CTRL, payload.size(), payload,
            OCP_PROTOCOL_ERROR_LENGTH, "NEW_INVALID_SECOND");
        probe_all_tokens("NEW_INVALID_REENTRY");
        read_status_and_check("NEW_INVALID_FIRST_CODE");
        read_status_and_check("NEW_INVALID_CLEAR_NO_DEFERRED_CODE");
        finish_stall_test("PERSISTENT_STALL");
        uvm_callbacks#(svt_usb_protocol, svt_usb_protocol_callbacks)::delete(
            host_agent_h.prot, raw_response_callback);
    endtask
endclass

`endif
