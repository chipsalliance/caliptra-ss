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

`ifndef CALIPTRA_SS_USB_OCP_FLOW_RANDOM_IMAGE_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FLOW_RANDOM_IMAGE_SEQUENCE_SV

// OCP_FLOW_006: randomized multi-batch streaming recovery using the
// specification-defined USB NAK/PING flow-control option.
class caliptra_ss_usb_ocp_flow_random_image_sequence
    extends caliptra_ss_usb_ocp_fifo_flow_control_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_flow_random_image_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam int unsigned FLOW_MAX_IMAGE_DWORDS = 192;
    localparam time FLOW_STATUS_TIMEOUT = 20ms;

    protected int unsigned ping_count;

    covergroup complete_flow_cg with function sample(
        int unsigned sampled_image_dwords,
        int unsigned sampled_chunk_dwords,
        bit sampled_chunk_nak,
        int unsigned sampled_naks);
        option.per_instance = 1;
        cp_image_size: coverpoint sampled_image_dwords {
            bins image_two_batches = {[65:128]};
            bins image_three_batches = {[129:192]};
        }
        cp_chunk_size: coverpoint sampled_chunk_dwords {
            bins chunk_small = {[1:4]};
            bins chunk_medium = {[5:15]};
            bins chunk_max_packet = {16};
        }
        cp_chunk_nak: coverpoint sampled_chunk_nak;
        cp_naks: coverpoint sampled_naks {
            bins nak_none = {0};
            bins nak_one = {1};
            bins nak_several = {[2:15]};
            bins nak_many = {[16:$]};
        }
        image_x_chunk: cross cp_image_size, cp_chunk_size;
        chunk_x_nak: cross cp_chunk_size, cp_chunk_nak;
    endgroup

    function new(string name =
        "caliptra_ss_usb_ocp_flow_random_image_sequence");
        super.new(name);
        complete_flow_cg = new();
    endfunction

    protected virtual function void sample_usb_nak_chunk(
        input int unsigned chunk_dwords,
        input bit nak_observed);

        complete_flow_cg.sample(
            image_dwords, chunk_dwords, nak_observed, observed_naks);
    endfunction

    virtual task body();
        fifo_status_s status;
        bit [15:0] agent_caps;
        bit [7:0] cms_count;
        bit [7:0] heartbeat_period;
        int unsigned min_image_dwords;
        int unsigned max_image_dwords;

        if (!get_sem_vif()) return;
        apply_config();
        initialize_ocp_transport();
        nak_callback =
            caliptra_ss_usb_nak_monitor_callback::type_id::create(
                "nak_callback");
        uvm_callbacks#(
            svt_usb_link_monitor,
            svt_usb_link_monitor_callback)::add(
                host_agent_h.link_mon, nak_callback);

        prot_cap_read_and_check(agent_caps, cms_count, heartbeat_period);
        if (!agent_caps[OCP_CAP_PUSH_C_IMAGE] ||
            !agent_caps[OCP_CAP_INDIRECT_FIFO]) begin
            `uvm_fatal("OCP_FLOW_006",
                $sformatf("PROT_CAP lacks Push C-image/FIFO CMS support: 0x%04h.",
                          agent_caps))
        end
        require_recovery_status_pair(
            OCP_DEVICE_STATUS_RECOVERY_MODE,
            OCP_RECOVERY_STATUS_AWAITING_IMAGE,
            4'h0, 8'h00, OCP_PROTOCOL_ERROR_NONE,
            2000, 10us, "INITIAL", "OCP_FLOW_006");

        read_and_check_status(status, "FLOW006_FIFO_DISCOVERY");
        if ((status.region_type != OCP_REGION_RECOVERY_CODE_WO) ||
            (status.fifo_size == 0) ||
            (legal_max_chunk_dwords(status) == 0)) begin
            `uvm_fatal("OCP_FLOW_006",
                $sformatf({"Invalid FIFO discovery: type=0x%02h size=%0d ",
                           "max_transfer=%0d."},
                          status.region_type, status.fifo_size,
                          status.max_transfer_dwords))
        end

        min_image_dwords =
            status.fifo_size + legal_max_chunk_dwords(status) + 1;
        max_image_dwords = status.fifo_size * 3;
        if (max_image_dwords > FLOW_MAX_IMAGE_DWORDS)
            max_image_dwords = FLOW_MAX_IMAGE_DWORDS;
        if (max_image_dwords < min_image_dwords) begin
            `uvm_fatal("OCP_FLOW_006",
                "FIFO size leaves no legal multi-batch randomization range.")
        end

        image_dwords = $urandom_range(
            max_image_dwords, min_image_dwords);
        pattern_base = 32'hC0DE_0000;
        final_valid_bytes = 4;
        randomize_chunks = 1'b1;
        strategy = FIFO_FLOW_BY_USB_NAK;
        generate_default_image();

        `uvm_info("OCP_FLOW_006",
            $sformatf({"Starting randomized multi-batch flow: ",
                       "image_dwords=%0d fifo_size=%0d max_chunk=%0d."},
                      image_dwords, status.fifo_size,
                      legal_max_chunk_dwords(status)),
            UVM_NONE)

        prepare_fifo_image(
            cms, OCP_RC_IMAGE_SEL_CMS, image_dwords,
            "FLOW006_RECOVERY_CTRL_SELECT", "FLOW006_FIFO_CTRL");
        successful_attempts = 0;
        rejected_attempts = 0;
        observed_naks = 0;
        caliptra_ss_usb_nak_monitor_callback::reset_nak_count();
        caliptra_ss_usb_nak_monitor_callback::reset_ping_count();
        push_image();
        ping_count =
            caliptra_ss_usb_nak_monitor_callback::get_ping_count();
        if (observed_naks == 0) begin
            `uvm_fatal("OCP_FLOW_006",
                "Multi-batch flow completed without USB NAK backpressure.")
        end
        if (ping_count == 0) begin
            `uvm_fatal("OCP_FLOW_006",
                "Multi-batch flow observed no USB PING retry tokens.")
        end
        wait_fw_state_generation_bounded(
            OCP_FW_STATE_RECOVERY_PENDING, 16'h0000,
            FLOW_STATUS_TIMEOUT, "FLOW006_PENDING_FW", "OCP_FLOW_006");
        read_and_check_status(status, "FLOW006_FINAL_EMPTY");
        if (!status.empty || status.full ||
            (status.write_index != status.read_index)) begin
            `uvm_fatal("OCP_FLOW_006",
                $sformatf({"FIFO was not empty after firmware verified the ",
                           "complete image: empty=%0b full=%0b write_index=%0d ",
                           "read_index=%0d."},
                          status.empty, status.full, status.write_index,
                          status.read_index))
        end
        require_recovery_status_pair(
            OCP_DEVICE_STATUS_RECOVERY_PENDING,
            OCP_RECOVERY_STATUS_AWAITING_IMAGE,
            4'h0, 8'h00, OCP_PROTOCOL_ERROR_NONE,
            2000, 10us, "PENDING", "OCP_FLOW_006");

        sem_vif.clear_recovery_image_activated_seen();
        recovery_ctrl_write(
            cms, OCP_RC_IMAGE_SEL_CMS, 1'b1,
            "FLOW006_ACTIVATE");
        wait_for_recovery_activation_observed(
            1000us, 1us, "FLOW006_ACTIVATE", "OCP_FLOW_006");

        wait_fw_state_generation_bounded(
            sem_vif.FW_STATE_FLOW_BOOTING_READY, 16'h0000,
            FLOW_STATUS_TIMEOUT, "FLOW006_BOOTING_READY", "OCP_FLOW_006");
        require_recovery_status_pair(
            OCP_DEVICE_STATUS_RUNNING_RECOVERY,
            OCP_RECOVERY_STATUS_BOOTING_IMAGE,
            4'h0, 8'h00, OCP_PROTOCOL_ERROR_NONE,
            2000, 10us, "BOOTING", "OCP_FLOW_006");

        issue_fw_command_and_wait(
            sem_vif.FW_COMMAND_FLOW_ADVANCE,
            16'h0001,
            sem_vif.FW_STATE_FLOW_SUCCESS_READY,
            FLOW_STATUS_TIMEOUT, "FLOW006_SUCCESS_READY", "OCP_FLOW_006");
        require_recovery_status_pair(
            OCP_DEVICE_STATUS_RUNNING_RECOVERY,
            OCP_RECOVERY_STATUS_SUCCESS,
            4'h0, 8'h00, OCP_PROTOCOL_ERROR_NONE,
            2000, 10us, "SUCCESS", "OCP_FLOW_006");

        issue_fw_command_and_wait(
            sem_vif.FW_COMMAND_FLOW_COMPLETE,
            16'h0002,
            sem_vif.FW_STATE_FLOW_COMPLETE,
            FLOW_STATUS_TIMEOUT, "FLOW006_COMPLETE", "OCP_FLOW_006");

        wait_mcu_axi_idle_before_finish("OCP_FLOW_006");
        publish_transfer_count();
        `uvm_info("OCP_FLOW_006",
            $sformatf({"Randomized recovery flow complete: image_dwords=%0d ",
                       "chunks=%0d observed_naks=%0d observed_pings=%0d ",
                       "transfers=%0d."},
                      image_dwords, successful_attempts,
                      observed_naks, ping_count, transfers_issued),
            UVM_NONE)
    endtask

endclass

`endif
