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

`ifndef CALIPTRA_SS_USB_OCP_STALL_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_STALL_BASE_SEQUENCE_SV

class caliptra_ss_usb_ocp_stall_base_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_stall_base_sequence)

    protected caliptra_ss_usb_ocp_stall_model stall_model;
    protected caliptra_ss_usb_ocp_fifo_packet_model fifo_packet_model;
    protected caliptra_ss_usb_ocp_scoreboard fifo_scoreboard;
    protected bit fifo_window_pending;
    protected int unsigned fifo_window_bytes;
    protected bit expecting_rejection;
    protected bit fifo_window_acceptance_allowed;
    protected bit fifo_window_owner_aborted;
    protected bit fifo_model_configured;
    protected bit inject_short_data;
    protected int unsigned checks_completed;
    protected int unsigned normal_nak_retry_limit;
    protected int unsigned normal_endpoint_retry_limit;
    protected bit [15:0] agent_capabilities;
    localparam ocp_cmd_t RESERVED_COMMAND = OCP_CMD_MIN - 1;
    // OCP Recovery v1.1 Section 9.2 RECOVERY_CTRL: 0x03..0xFF reserved.
    localparam bit [7:0] RESERVED_IMAGE_SELECTION = OCP_RC_IMAGE_SEL_LOCAL + 1;
    // USB 2.0 Section 5.5.3: high-speed control endpoints use 64-byte packets.
    localparam int unsigned HS_CONTROL_PACKET_BYTES = 64;
    localparam int unsigned NEGATIVE_NAK_RETRY_LIMIT = 4;

    function new(string name = "caliptra_ss_usb_ocp_stall_base_sequence");
        super.new(name);
    endfunction

    protected task initialize_stall_transport();
        bit [7:0] cms_count;
        bit [7:0] heartbeat_period;
        ocp_arb_do_initialize_and_check_transport();
        checker.packet_callback.enable_diagnostics();
        if (!uvm_config_db#(caliptra_ss_usb_ocp_stall_model)::get(
                null, "", "ocp_stall_model", stall_model)) begin
            `uvm_fatal("OCP_STALL", "Protocol reference model is unavailable.")
        end
        stall_model.reset();
        if (!uvm_config_db#(caliptra_ss_usb_ocp_fifo_packet_model)::get(
                null, "", "ocp_fifo_packet_model", fifo_packet_model))
            `uvm_fatal("OCP_STALL", "FIFO reference model is unavailable.")
        if (!uvm_config_db#(caliptra_ss_usb_ocp_scoreboard)::get(
                null, "", "ocp_fifo_scoreboard", fifo_scoreboard))
            `uvm_fatal("OCP_STALL", "FIFO scoreboard is unavailable.")
        fifo_model_configured = 1'b0;
        checks_completed = 0;
        ocp_do_read_and_check_prot_cap(agent_capabilities, cms_count, heartbeat_period);
        read_status_and_check("INITIAL_STATUS");
        read_status_and_check("INITIAL_CLEAR");
        normal_nak_retry_limit =
            usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak;
        normal_endpoint_retry_limit = usb_cfg.remote_device_cfg[0].
            endpoint_cfg[0].max_retry_due_to_nak_before_moving_to_next_ep;
    endtask

    protected function void mark_check(input string label);
        checks_completed++;
        `uvm_info("OCP_STALL",
            $sformatf("check=%0d %s", checks_completed, label), UVM_NONE)
    endfunction

    protected function void require_accepted_setup(input string label);
        if (checker.packet_callback.accepted_setup_count() != 1) begin
            `uvm_error("OCP_STALL",
                $sformatf("%s requires exactly one ACKed SETUP; observed %0d.",
                    label, checker.packet_callback.accepted_setup_count()))
        end
        stall_model.note_accepted_setup();
    endfunction

    protected virtual function void ocp_configure_xfer( input svt_usb_transfer request);
        svt_usb_transfer_exception exception_item;
        super.ocp_configure_xfer(request);
        if (fifo_model_configured &&
            (request.setup_data_w_value[7:0] == OCP_CMD_INDIRECT_FIFO_DATA) &&
            (request.setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE)) begin
            if (fifo_window_pending)
                `uvm_fatal("OCP_STALL", "FIFO request lacks its own observation boundary.")
            fifo_window_pending = 1'b1;
            fifo_window_bytes = request.setup_data_w_length;
            fifo_window_acceptance_allowed = !expecting_rejection;
            fifo_window_owner_aborted = 1'b0;
            // USB 2.0 9.3.5: control OUT sends exactly wLength bytes.
            // Do not append the VIP's bulk-style aligned-transfer ZLP.
            usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
                allow_aligned_transfer_without_zero_length = 1;
            request.aligned_transfer_ends_with_zero_length = 0;
        end
        if (!inject_short_data ||
            (request.setup_data_bmrequesttype_dir != svt_usb_types::HOST_TO_DEVICE))
            return;
        if ((request.setup_data_w_value[7:0] != OCP_CMD_RECOVERY_CTRL) ||
            (request.setup_data_w_length != 1) ||
            (request.payload_intended_byte_count != 1))
            `uvm_fatal("OCP_STALL", "Unexpected request for short-DATA injection.")
        exception_item = new("short_data_setup_length");
        exception_item.cfg = request.cfg;
        exception_item.xact = request;
        if (!exception_item.randomize() with {
                error_kind == svt_usb_transfer_exception::CONTROL_TRANSFER_FORMAT;
                control_transfer_format_error ==
                    svt_usb_transfer_exception::W_LENGTH_PAYLOAD_MISMATCH;
                control_transfer_stage == svt_usb_transfer_exception::SETUP_STAGE;
                error_val == OCP_SPEC_LEN_RECOVERY_CTRL;
            })
            `uvm_fatal("OCP_STALL", "Short-DATA format injection did not randomize.")
        if (request.exception_list == null)
            request.exception_list = new("short_data_exceptions");
        request.exception_list.add_exception(exception_item);
    endfunction

    protected virtual function void ocp_note_xfer_completed( input svt_usb_transfer request,
                                                            input caliptra_ss_usb_ocp_xfer_result_e result);
                                                            super.ocp_note_xfer_completed(request, result);
        if (fifo_window_pending &&
            (request.setup_data_w_value[7:0] == OCP_CMD_INDIRECT_FIFO_DATA) &&
            (request.setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE) &&
            (result == OCP_XFER_ABORTED))
            fifo_window_owner_aborted = 1'b1;
    endfunction

    protected virtual task ocp_arb_check_and_close_observation_window(
        input logic [15:0] generation,
        input logic [3:0] expected_legacy_dispatch_delta);
        super.ocp_arb_check_and_close_observation_window(generation, expected_legacy_dispatch_delta);
        if (fifo_window_pending) begin
            fifo_scoreboard.observe_fifo_window(checker.packet_callback,
                generation, 7'(dev_addr_v), fifo_window_bytes,
                fifo_window_acceptance_allowed, fifo_window_owner_aborted);
            fifo_window_pending = 1'b0;
        end
    endtask

    protected task read_status_and_check(input string label);
        bit [7:0] status_bytes[$];
        logic [15:0] generation;
        ocp_arb_open_observation_window(generation);
        ocp_do_read_and_check_device_status(status_bytes, label);
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        require_accepted_setup(label);
        if (status_bytes.size() <= OCP_OFF_DS_PROT_ERROR) begin
            `uvm_fatal("OCP_STALL", {label, ": status code not returned."})
        end
        void'(stall_model.check_status_code(
            status_bytes[OCP_OFF_DS_PROT_ERROR], label));
    endtask

    protected task legal_read( input ocp_cmd_t command, ref bit [7:0] response[$],
                               input string label);
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;
        logic [15:0] generation;
        ocp_arb_open_observation_window(generation);
        ocp_do_read(command, response, ignored_result, label);
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        require_accepted_setup(label);
        if (fifo_model_configured && (command == OCP_CMD_INDIRECT_FIFO_STATUS) &&
            (response.size() == OCP_SPEC_LEN_INDIRECT_FIFO_STATUS) &&
            !fifo_packet_model.indices_match(
                ocp_get_le32(response, OCP_OFF_IFS_WRITE_INDEX_B0),
                ocp_get_le32(response, OCP_OFF_IFS_READ_INDEX_B0)))
            `uvm_error("OCP_STALL", {label, ": FIFO indices differ from packet acceptance model."})
        if (checker.packet_callback.count_pid(svt_usb_packet::STALL,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) != 0)
            `uvm_error("OCP_STALL", {label, ": legal read received STALL."})
    endtask

    protected task issue_stall( input bit dir_in, input ocp_cmd_t command,
                                input bit [15:0] requested_length,
                                ref bit [7:0] payload[$],
                                input ocp_protocol_error_e expected_code,
                                input string label,
                                input bit require_out_data = 1'b0);
        caliptra_ss_usb_ocp_xfer_result_e result;
        bit [7:0] response[$];
        logic [15:0] generation;
        bit ack_seen;
        bit stall_seen;
        int unsigned out_data_packets;
        int unsigned out_data_bytes;
        caliptra_ss_usb_ocp_arbiter_packet_callback::packet_record_t record;

        // Only negative OCP requests require immediate rejection. Standard
        // firmware-serviced requests must retain their normal retry budget.
        ocp_configure_ep0_nak_retry_limit(NEGATIVE_NAK_RETRY_LIMIT);
        ocp_arb_open_observation_window(generation);
        if (inject_short_data)
            checker.expect_wire_setup_length(OCP_SPEC_LEN_RECOVERY_CTRL);
        expecting_rejection = 1'b1;
        ocp_do_class_xfer(dir_in, command, requested_length,
            payload, response, result, label);
        expecting_rejection = 1'b0;
        ocp_configure_ep0_nak_retry_limit(
            normal_nak_retry_limit, normal_endpoint_retry_limit);
        ocp_arb_check_and_close_observation_window(generation, 4'h0);
        require_accepted_setup(label);
        ack_seen = 1'b0;
        stall_seen = 1'b0;
        out_data_packets = 0;
        out_data_bytes = 0;
        for (int unsigned i = 0;
             i < checker.packet_callback.packet_count(); i++) begin
            record = checker.packet_callback.get_packet(i);
            if ((record.direction ==
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) &&
                record.accepted_setup)
                ack_seen = 1'b1;
            if (ack_seen &&
                (record.direction ==
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) &&
                (record.pid_type == svt_usb_packet::DATA)) begin
                out_data_packets++;
                out_data_bytes += record.data_length;
            end
            if ((record.direction ==
                    caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) &&
                (record.pid_name == svt_usb_packet::STALL)) begin
                if (!ack_seen)
                    `uvm_error("OCP_STALL", {label, ": STALL preceded SETUP ACK."})
                stall_seen = 1'b1;
                break;
            end
        end
        if (!stall_seen || (result == OCP_XFER_SUCCESS) ||
            !checker.packet_callback.validate_control_stall(7'(dev_addr_v), 4'h0)) begin
            `uvm_error("OCP_STALL",
                $sformatf("%s expected ordered EP0 STALL/non-success; STALL=%0b result=%s.",
                          label, stall_seen, result.name()))
        end
        if (require_out_data && (out_data_packets == 0))
            `uvm_error("OCP_STALL", {label, ": DATA-stage stimulus was not delivered."})
        if (inject_short_data && (out_data_bytes != payload.size()))
            `uvm_error("OCP_STALL", {label, ": short-DATA wire byte count mismatch."})
        stall_model.note_error(expected_code);
        void'(stall_model.require_stalled(label));
    endtask

    protected task snapshot_command_state( ref bit [7:0] recovery_control[$],
                                           ref bit [7:0] fifo_control[$],
                                           ref bit [7:0] fifo_status[$],
                                           input string label);
        legal_read(OCP_CMD_RECOVERY_CTRL, recovery_control, {label, "_RC"});
        if (agent_capabilities[OCP_CAP_INDIRECT_FIFO]) begin
            legal_read(OCP_CMD_INDIRECT_FIFO_CTRL, fifo_control, {label, "_FC"});
            legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, fifo_status, {label, "_FS"});
            if (fifo_model_configured &&
                (fifo_status.size() == OCP_SPEC_LEN_INDIRECT_FIFO_STATUS) &&
                !fifo_packet_model.indices_match(
                    ocp_get_le32(fifo_status, OCP_OFF_IFS_WRITE_INDEX_B0),
                    ocp_get_le32(fifo_status, OCP_OFF_IFS_READ_INDEX_B0)))
                `uvm_error("OCP_STALL", {label, ": FIFO indices differ from independent reference."})
        end
    endtask

    protected task prepare_modeled_fifo( input int unsigned image_dwords, input string label);
        bit [7:0] status_bytes[$];
        ocp_do_fifo_ctrl_write(0, 1'b1, image_dwords, label);
        legal_read(OCP_CMD_INDIRECT_FIFO_STATUS, status_bytes, {label, "_CAPS"});
        if (status_bytes.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
            `uvm_fatal("OCP_STALL", "FIFO capability discovery was truncated.")
        fifo_packet_model.configure(
            ocp_get_le32(status_bytes, OCP_OFF_IFS_FIFO_SIZE_B0),
            ocp_get_le32(status_bytes, OCP_OFF_IFS_MAX_TRANSFER_B0),
            HS_CONTROL_PACKET_BYTES, 1'b1, wMaxWrTransferSize, image_dwords);
        fifo_model_configured = 1'b1;
        fifo_scoreboard.enable_packet_fifo_checking();
        if (!fifo_packet_model.indices_match(
                ocp_get_le32(status_bytes, OCP_OFF_IFS_WRITE_INDEX_B0),
                ocp_get_le32(status_bytes, OCP_OFF_IFS_READ_INDEX_B0)))
            `uvm_error("OCP_STALL", "Protocol FIFO reset did not establish initial indices.")
    endtask

    protected task check_rejected_request( input bit dir_in,
                                           input ocp_cmd_t command,
                                           input bit [15:0] requested_length,
                                           ref bit [7:0] payload[$],
                                           input ocp_protocol_error_e expected_code,
                                           input string label,
                                           input bit require_out_data = 1'b0);
        bit [7:0] rc_before[$], fc_before[$], fs_before[$];
        bit [7:0] rc_after[$], fc_after[$], fs_after[$];
        snapshot_command_state(rc_before, fc_before, fs_before, {label, "_BEFORE"});
        issue_stall(dir_in, command, requested_length, payload,
            expected_code, label, require_out_data);
        read_status_and_check({label, "_CODE"});
        read_status_and_check({label, "_CLEAR"});
        snapshot_command_state(rc_after, fc_after, fs_after, {label, "_AFTER"});
        if ((rc_before != rc_after) || (fc_before != fc_after) ||
            (fs_before != fs_after))
            `uvm_error("OCP_STALL", {label, ": rejected request changed command/FIFO state."})
        mark_check(label);
    endtask

    protected task finish_stall_test(input string label);
        bit [7:0] response[$];
        if (fifo_window_pending)
            `uvm_error("OCP_STALL", {label, ": FIFO request observation was not consumed."})
        legal_read(OCP_CMD_PROT_CAP, response, {label, "_FINAL_PROT_CAP"});
        if (response.size() != OCP_SPEC_LEN_PROT_CAP)
            `uvm_error("OCP_STALL", {label, ": final capability response truncated."})
        ocp_publish_transfer_count();
        `uvm_info("OCP_STALL",
            $sformatf("%s complete: checks=%0d transfers=%0d.",
                      label, checks_completed, transfers_issued), UVM_NONE)
    endtask
endclass

`endif
