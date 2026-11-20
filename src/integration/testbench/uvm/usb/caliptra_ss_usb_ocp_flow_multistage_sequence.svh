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

`ifndef CALIPTRA_SS_USB_OCP_FLOW_MULTISTAGE_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FLOW_MULTISTAGE_SEQUENCE_SV

class caliptra_ss_usb_ocp_flow_multistage_sequence
    extends caliptra_ss_usb_ocp_fifo_flow_control_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_flow_multistage_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam time STAGE_TIMEOUT = 20ms;
    localparam bit [31:0] ARTIFACT_MAGIC = 32'h344F4C46;

    covergroup multistage_cg with function sample(
        int unsigned stage, bit random_chunks);
        option.per_instance = 1;
        cp_stage: coverpoint stage {
            bins core = {0};
            bins manifest = {1};
            bins mcu = {2};
            bins ordered_stages = (0 => 1 => 2);
        }
        cp_random_chunks: coverpoint random_chunks;
        stage_x_chunk_mode: cross cp_stage, cp_random_chunks;
    endgroup

    function new(string name = "caliptra_ss_usb_ocp_flow_multistage_sequence");
        super.new(name);
        strategy = FIFO_FLOW_BY_USB_NAK;
        require_backpressure = 1'b0;
        final_valid_bytes = 4;
        multistage_cg = new();
    endfunction

    protected task load_artifact(input int unsigned stage);
        string path;
        int fd;
        int scanned;
        int unsigned value;

        path = $sformatf("flow004_stage%0d.hex", stage);
        fd = $fopen(path, "r");
        if (fd == 0)
            `uvm_fatal("OCP_FLOW_004", {"Could not open artifact ", path})
        image_bytes.delete();
        while (!$feof(fd)) begin
            scanned = $fscanf(fd, "%h", value);
            if (scanned == 1) begin
                if (value > 255)
                    `uvm_fatal("OCP_FLOW_004", {"Invalid artifact byte in ", path})
                image_bytes.push_back(8'(value));
            end else if (!$feof(fd)) begin
                `uvm_fatal("OCP_FLOW_004", {"Malformed artifact ", path})
            end
        end
        $fclose(fd);
        if ((image_bytes.size() <= 16) || (image_bytes.size() > 4096) ||
            ((image_bytes.size() % 4) != 0))
            `uvm_fatal("OCP_FLOW_004", {"Invalid artifact size in ", path})
        if ((ocp_get_le32(image_bytes, 0) != ARTIFACT_MAGIC) ||
            (ocp_get_le32(image_bytes, 4) != stage) ||
            (ocp_get_le32(image_bytes, 8) != image_bytes.size() - 16))
            `uvm_fatal("OCP_FLOW_004", {"Invalid artifact header in ", path})
        image_dwords = image_bytes.size() / 4;
    endtask

    virtual task body();
        bit [15:0] caps;
        fifo_status_s status;

        if (!ocp_configure_sem_vif()) return;
        randomize_chunks = $test$plusargs("flow004_random_chunks");
        ocp_do_initialize_and_check_transport();
        ocp_do_read_and_check_recovery_capabilities("FLOW004_CAPS", caps);
        if (!caps[OCP_CAP_PUSH_C_IMAGE] || !caps[OCP_CAP_INDIRECT_FIFO])
            `uvm_fatal("OCP_FLOW_004", "Push/FIFO recovery support is required")

        // Caliptra streaming-boot sequence: 0=core, 1=SoC manifest, 2=MCU.
        for (int unsigned stage = 0; stage < 3; stage++) begin
            ocp_wait_fw_state_generation(
                sem_vif.FW_STATE_PATH_READY, 16'(stage + 1),
                STAGE_TIMEOUT, "AWAITING_STAGE", "OCP_FLOW_004");
            if (sem_vif.recovery_image_activated !== 1'b0)
                `uvm_fatal("OCP_FLOW_004", "Previous activation was not cleared")
            ocp_do_poll_and_check_recovery_status_pair(
                (stage == 0) ? OCP_DEVICE_STATUS_RECOVERY_MODE :
                               OCP_DEVICE_STATUS_RUNNING_RECOVERY,
                OCP_RECOVERY_STATUS_AWAITING_IMAGE, 4'(stage),
                8'h00, OCP_PROTOCOL_ERROR_NONE,
                2000, 10us, "AWAITING_STAGE", "OCP_FLOW_004");
            load_artifact(stage);
            ocp_do_fifo_image_config_xfers(
                cms, OCP_RC_IMAGE_SEL_CMS, image_dwords,
                "FLOW004_SELECT", "FLOW004_FIFO_RESET");
            ocp_fifo_do_read_and_check_status(status, "FLOW004_RESET_CHECK");
            if (!status.empty || status.full ||
                (status.write_index != 0) || (status.read_index != 0))
                `uvm_fatal("OCP_FLOW_004", "FIFO was not reset for the new stage")
            successful_attempts = 0;
            observed_naks = 0;
            ocp_fifo_do_push_and_check_image();
            ocp_wait_fw_state_generation(
                OCP_FW_STATE_RECOVERY_PENDING, 16'(stage + 1),
                STAGE_TIMEOUT, "STAGE_PENDING", "OCP_FLOW_004");
            ocp_fifo_do_poll_and_check_final_empty();
            ocp_do_poll_and_check_recovery_status_pair(
                OCP_DEVICE_STATUS_RECOVERY_PENDING,
                OCP_RECOVERY_STATUS_AWAITING_IMAGE, 4'(stage),
                8'h00, OCP_PROTOCOL_ERROR_NONE,
                2000, 10us, "STAGE_PENDING", "OCP_FLOW_004");
            sem_vif.clear_recovery_image_activated_seen();
            ocp_do_recovery_ctrl_write(cms, OCP_RC_IMAGE_SEL_CMS, 1'b1,
                                       "FLOW004_ACTIVATE");
            ocp_poll_recovery_activation(
                1000us, 1us, "FLOW004_ACTIVATE", "OCP_FLOW_004");
            ocp_wait_fw_state_generation(
                sem_vif.FW_STATE_FLOW_BOOTING_READY, 16'(stage + 1),
                STAGE_TIMEOUT, "STAGE_BOOTING", "OCP_FLOW_004");
            ocp_do_poll_and_check_recovery_status_pair(
                OCP_DEVICE_STATUS_RUNNING_RECOVERY,
                OCP_RECOVERY_STATUS_BOOTING_IMAGE, 4'(stage),
                8'h00, OCP_PROTOCOL_ERROR_NONE,
                2000, 10us, "STAGE_BOOTING", "OCP_FLOW_004");
            sem_vif.issue_fw_command(
                sem_vif.FW_COMMAND_FLOW_ADVANCE, 16'(stage + 1));
            if (stage < 2)
                ocp_wait_fw_state_generation(
                    sem_vif.FW_STATE_PATH_READY, 16'(stage + 2),
                    STAGE_TIMEOUT, "NEXT_STAGE", "OCP_FLOW_004");
            else
                ocp_wait_fw_state_generation(
                    sem_vif.FW_STATE_FLOW_SUCCESS_READY, 16'd3,
                    STAGE_TIMEOUT, "MCU_EXECUTED", "OCP_FLOW_004");
            sem_vif.clear_fw_command();
            multistage_cg.sample(stage, randomize_chunks);
            `uvm_info("OCP_FLOW_004",
                $sformatf("Stage %0d complete: %0d bytes, %0d chunks.",
                          stage, image_bytes.size(), successful_attempts), UVM_NONE)
        end
        ocp_do_poll_and_check_recovery_status_pair(
            OCP_DEVICE_STATUS_RUNNING_RECOVERY, OCP_RECOVERY_STATUS_SUCCESS,
            4'd2, 8'h00, OCP_PROTOCOL_ERROR_NONE,
            2000, 10us, "MULTISTAGE_SUCCESS", "OCP_FLOW_004");
        ocp_issue_fw_command_and_wait(
            sem_vif.FW_COMMAND_FLOW_COMPLETE, 16'd4,
            sem_vif.FW_STATE_FLOW_COMPLETE, STAGE_TIMEOUT,
            "MULTISTAGE_COMPLETE", "OCP_FLOW_004");
        ocp_poll_mcu_axi_idle("OCP_FLOW_004");
        ocp_publish_transfer_count();
        `uvm_info("OCP_FLOW_004",
            "All three stages completed in one session, including MCU executable pass mailbox.",
            UVM_NONE)
    endtask

endclass
`endif
