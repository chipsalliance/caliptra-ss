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

`ifndef CALIPTRA_SS_USB_OCP_FIRMWARE_STATUS_OWNERSHIP_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FIRMWARE_STATUS_OWNERSHIP_SEQUENCE_SV

class caliptra_ss_usb_ocp_firmware_status_ownership_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(
        caliptra_ss_usb_ocp_firmware_status_ownership_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    function new(string name =
        "caliptra_ss_usb_ocp_firmware_status_ownership_sequence");
        super.new(name);
    endfunction

    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("OCP_STATUS_OWNERSHIP",
                "ocp_access_semantics_if not found in config_db")
            return 1'b0;
        end
        return 1'b1;
    endfunction

    protected virtual task wait_fw_generation(
        input logic [7:0] state,
        input logic [15:0] generation,
        input string label);

        bit found;
        sem_vif.wait_for_fw_state_generation_bounded(
            state, generation, 2ms, found);
        if (!found) begin
            `uvm_fatal("OCP_STATUS_OWNERSHIP",
                $sformatf("%s state=0x%02h generation=%0d not observed.",
                          label, state, generation))
        end
    endtask

    protected virtual task expected_milestone(
        input  int unsigned generation,
        output ocp_device_status_e device_status,
        output logic [15:0] reason_code,
        output ocp_recovery_status_e recovery_status,
        output logic [3:0] image_index,
        output logic [7:0] vendor_status,
        output logic [7:0] hw_status);

        case (generation)
            1: begin
                device_status = OCP_DEVICE_STATUS_RECOVERY_MODE;
                reason_code = OCP_REC_REASON_FORCED_RECOVERY;
                recovery_status = OCP_RECOVERY_STATUS_AWAITING_IMAGE;
                image_index = 4'h0;
                vendor_status = 8'h00;
                hw_status = 8'h00;
            end
            2: begin
                device_status = OCP_DEVICE_STATUS_RECOVERY_PENDING;
                reason_code = OCP_REC_REASON_FLASHLESS_BOOT;
                recovery_status = OCP_RECOVERY_STATUS_BOOTING_IMAGE;
                image_index = 4'h2;
                vendor_status = 8'hA5;
                hw_status = 8'h00;
            end
            3: begin
                device_status = OCP_DEVICE_STATUS_RUNNING_RECOVERY;
                reason_code = OCP_REC_REASON_NONE;
                recovery_status = OCP_RECOVERY_STATUS_SUCCESS;
                image_index = 4'h3;
                vendor_status = 8'h5A;
                hw_status = 8'h00;
            end
            4: begin
                device_status = OCP_DEVICE_STATUS_BOOT_FAILURE;
                reason_code = OCP_REC_REASON_AUTH_RECOVERY_FW;
                recovery_status = OCP_RECOVERY_STATUS_AUTH_ERROR;
                image_index = 4'h4;
                vendor_status = 8'h3C;
                hw_status = 8'h00;
            end
            default: begin
                device_status = OCP_DEVICE_STATUS_FATAL_ERROR;
                reason_code = OCP_REC_REASON_NONE;
                recovery_status = OCP_RECOVERY_STATUS_FAILED;
                image_index = 4'h5;
                vendor_status = 8'hC3;
                hw_status = OCP_HW_STATUS_FATAL_ERR;
            end
        endcase
    endtask

    protected virtual task read_and_check_status(
        input int unsigned generation,
        input ocp_protocol_error_e expected_protocol_error,
        input string label);

        bit [7:0] device_status_response[$];
        bit [7:0] recovery_status_response[$];
        bit [7:0] hw_status_response[$];
        ocp_device_status_e expected_device_status;
        ocp_recovery_status_e expected_recovery_status;
        logic [15:0] expected_reason_code;
        logic [15:0] observed_reason_code;
        logic [3:0] expected_image_index;
        logic [7:0] expected_vendor_status;
        logic [7:0] expected_hw_status;

        expected_milestone(
            generation,
            expected_device_status,
            expected_reason_code,
            expected_recovery_status,
            expected_image_index,
            expected_vendor_status,
            expected_hw_status);

        ocp_read(
            OCP_CMD_RECOVERY_STATUS,
            recovery_status_response,
            {label, "_RECOVERY_STATUS"});
        ocp_read(
            OCP_CMD_HW_STATUS,
            hw_status_response,
            {label, "_HW_STATUS"});
        ocp_read(
            OCP_CMD_DEVICE_STATUS,
            device_status_response,
            {label, "_DEVICE_STATUS"});

        if (device_status_response.size() <= OCP_OFF_DS_REC_REASON_HI) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s DEVICE_STATUS response too short: %0d.",
                          label, device_status_response.size()))
        end else begin
            observed_reason_code = {
                device_status_response[OCP_OFF_DS_REC_REASON_HI],
                device_status_response[OCP_OFF_DS_REC_REASON_LO]
            };
            if ((device_status_response[OCP_OFF_DS_STATUS] !==
                    expected_device_status) ||
                (device_status_response[OCP_OFF_DS_PROT_ERROR] !==
                    expected_protocol_error) ||
                (observed_reason_code !== expected_reason_code)) begin
                `uvm_error("OCP_STATUS_OWNERSHIP",
                    $sformatf("%s DEVICE_STATUS got status/error/reason=0x%02h/0x%02h/0x%04h expected 0x%02h/0x%02h/0x%04h.",
                              label,
                              device_status_response[OCP_OFF_DS_STATUS],
                              device_status_response[OCP_OFF_DS_PROT_ERROR],
                              observed_reason_code,
                              expected_device_status,
                              expected_protocol_error,
                              expected_reason_code))
            end
        end

        if (recovery_status_response.size() <
                OCP_SPEC_LEN_RECOVERY_STATUS) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s RECOVERY_STATUS response too short: %0d.",
                          label, recovery_status_response.size()))
        end else if (
            (recovery_status_response[
                OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0] !==
                    expected_recovery_status) ||
            (recovery_status_response[
                OCP_OFF_RS_STATUS_IMAGE_INDEX][7:4] !==
                    expected_image_index) ||
            (recovery_status_response[OCP_OFF_RS_VENDOR_STATUS] !==
                    expected_vendor_status)) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s RECOVERY_STATUS got status/index/vendor=0x%01h/0x%01h/0x%02h expected 0x%01h/0x%01h/0x%02h.",
                          label,
                          recovery_status_response[
                              OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0],
                          recovery_status_response[
                              OCP_OFF_RS_STATUS_IMAGE_INDEX][7:4],
                          recovery_status_response[
                              OCP_OFF_RS_VENDOR_STATUS],
                          expected_recovery_status,
                          expected_image_index,
                          expected_vendor_status))
        end

        if (hw_status_response.size() < OCP_SPEC_MIN_LEN_HW_STATUS) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s HW_STATUS response too short: %0d.",
                          label, hw_status_response.size()))
        end else if ((hw_status_response[OCP_OFF_HW_DEV_STATUS] &
                      ~OCP_HW_STATUS_RESERVED_MASK) !== expected_hw_status) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s HW_STATUS byte0=0x%02h expected 0x%02h.",
                          label,
                          hw_status_response[OCP_OFF_HW_DEV_STATUS],
                          expected_hw_status))
        end
    endtask

    protected virtual task issue_host_ro_write(
        input ocp_cmd_t command,
        input string label);

        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        payload = '{8'hA5};
        ocp_try_write(command, payload, result, label);
        if (result == OCP_XFER_ABORTED) begin
            `uvm_error("OCP_STATUS_OWNERSHIP",
                $sformatf("%s aborted before the current protocol response completed.",
                          label))
        end
    endtask

    virtual task body();
        if (!get_sem_vif()) return;
        initialize_ocp_transport();

        for (int unsigned generation = 1; generation <= 5; generation++) begin
            wait_fw_generation(
                OCP_STATUS_OWNERSHIP_STATE_READY,
                16'(generation),
                $sformatf("OCP_STATUS_READY_%0d", generation));

            read_and_check_status(
                generation,
                OCP_PROTOCOL_ERROR_NONE,
                $sformatf("OCP_STATUS_MILESTONE_%0d_INITIAL", generation));

            case (generation)
                1: issue_host_ro_write(
                    OCP_CMD_DEVICE_STATUS, "OCP_WRITE_DEVICE_STATUS");
                2: issue_host_ro_write(
                    OCP_CMD_RECOVERY_STATUS, "OCP_WRITE_RECOVERY_STATUS");
                3: issue_host_ro_write(
                    OCP_CMD_HW_STATUS, "OCP_WRITE_HW_STATUS");
                4: begin
                    issue_host_ro_write(
                        OCP_CMD_RECOVERY_STATUS,
                        "OCP_FIRST_ERROR_RECOVERY_STATUS");
                    issue_host_ro_write(
                        OCP_CMD_HW_STATUS,
                        "OCP_SECOND_ERROR_HW_STATUS");
                end
                default: issue_host_ro_write(
                    OCP_CMD_DEVICE_STATUS, "OCP_WRITE_DEVICE_STATUS_FATAL");
            endcase

            wait_fw_generation(
                OCP_STATUS_OWNERSHIP_STATE_PROTECTED,
                16'(generation),
                $sformatf("OCP_STATUS_PROTECTED_%0d", generation));
            if (sem_vif.get_fw_data() !==
                    OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND) begin
                `uvm_error("OCP_STATUS_OWNERSHIP",
                    $sformatf("Generation %0d firmware observed PROT_ERROR=0x%02h expected 0x%02h.",
                              generation,
                              sem_vif.get_fw_data(),
                              OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND))
            end

            read_and_check_status(
                generation,
                OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND,
                $sformatf("OCP_STATUS_MILESTONE_%0d_PROTECTED", generation));
        end

        wait_fw_generation(
            OCP_STATUS_OWNERSHIP_STATE_DONE, 16'd5, "OCP_STATUS_DONE");
        wait_mcu_axi_idle_before_finish("OCP_STATUS_OWNERSHIP");
        publish_transfer_count();
        `uvm_info("OCP_STATUS_OWNERSHIP",
            "Firmware-owned status milestone and host-read-only matrix complete.",
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIRMWARE_STATUS_OWNERSHIP_SEQUENCE_SV
