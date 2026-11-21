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

`ifndef CALIPTRA_SS_USB_OCP_CMD_REGISTER_TOGGLE_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_CMD_REGISTER_TOGGLE_SEQUENCE_SVH

class caliptra_ss_usb_ocp_cmd_register_toggle_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_cmd_register_toggle_sequence)

    localparam int unsigned TARGET_COUNT = 6;
    localparam bit [7:0] LOAD_BYTE0 = 8'h60;
    localparam bit [7:0] SELECT_TARGET = 8'h64;
    localparam bit [7:0] WRITE_TARGET = 8'h65;
    localparam bit [7:0] RESTORE_TARGET = 8'h66;
    localparam time FW_TIMEOUT = 20ms;

    protected logic [15:0] generation;

    function new(string name = "caliptra_ss_usb_ocp_cmd_register_toggle_sequence");
        super.new(name);
        generation = 0;
    endfunction

    protected task firmware_command(input bit [7:0] opcode,
                                     input bit [7:0] data = 0);
        generation++;
        sem_vif.issue_fw_command(opcode, generation, data);
        ocp_wait_fw_state_generation(
            (opcode == sem_vif.FW_COMMAND_FLOW_COMPLETE) ?
                sem_vif.FW_STATE_FLOW_COMPLETE : sem_vif.FW_STATE_PATH_READY,
            generation, FW_TIMEOUT, "REGISTER_SWEEP_COMMAND", "OCP_CMD_TOGGLE");
        if (sem_vif.get_fw_data() !== data)
            `uvm_fatal("OCP_CMD_TOGGLE", "Firmware command data acknowledgment mismatch.")
        sem_vif.clear_fw_command();
        if (opcode != sem_vif.FW_COMMAND_FLOW_COMPLETE)
            ocp_wait_fw_state_generation(
                sem_vif.FW_STATE_COMMAND_BUSY, generation, FW_TIMEOUT,
                "REGISTER_SWEEP_RELEASED", "OCP_CMD_TOGGLE");
    endtask

    protected task write_value(input bit [31:0] value);
        for (int unsigned b = 0; b < 4; b++)
            firmware_command(LOAD_BYTE0 + 8'(b), value[b*8 +: 8]);
        firmware_command(WRITE_TARGET);
    endtask

    protected function bit [31:0] legal_pattern(
        input int unsigned target,
        input int unsigned phase_number,
        input bit [31:0] random_value,
        input bit [31:0] mask);
        bit [31:0] value;
        bit [7:0] device_status;
        bit [7:0] reason;
        bit [7:0] temperature;
        case (phase_number)
            0, 4: value = 0;
            1: value = random_value & mask;
            2: value = mask;
            3: value = ~random_value & mask;
            default: `uvm_fatal("OCP_CMD_TOGGLE", "Invalid pattern phase.")
        endcase
        // OCP Recovery v1.1 Section 9.2 enumerates these field encodings.
        case (target)
            2: begin
                if (phase_number == 2) value[15:8] = OCP_RC_IMAGE_SEL_LOCAL;
                else if (phase_number == 3) value[15:8] = OCP_RC_IMAGE_SEL_CMS;
                else if (value[15:8] > OCP_RC_IMAGE_SEL_LOCAL)
                    value[15:8] = OCP_RC_IMAGE_SEL_CMS;
                value[23:16] = (value[19:16] != 0) ? OCP_RC_ACTIVATE_CODE : 0;
            end
            3: value[3:0] = {value[2], value[2], value[1:0]};
            4: begin
                case (value[2:0])
                    6: device_status = OCP_DEVICE_STATUS_BOOT_FAILURE;
                    7: device_status = OCP_DEVICE_STATUS_FATAL_ERROR;
                    default: device_status = {5'b0, value[2:0]};
                endcase
                reason = value[23:16];
                if ((reason > OCP_REC_REASON_STANDARD_MAX) &&
                    (reason < OCP_REC_REASON_VENDOR_MIN))
                    reason[7] = 1'b1;
                if (phase_number == 2) begin
                    device_status = OCP_DEVICE_STATUS_BOOT_FAILURE;
                    reason = 8'hFF;
                end else if (phase_number == 3) begin
                    device_status = OCP_DEVICE_STATUS_FATAL_ERROR;
                    reason = 0;
                end
                if (!((device_status == OCP_DEVICE_STATUS_RECOVERY_MODE) ||
                      (device_status == OCP_DEVICE_STATUS_RECOVERY_PENDING) ||
                      (device_status == OCP_DEVICE_STATUS_BOOT_FAILURE)))
                    reason = 0;
                value = (32'(reason) << 16) | 32'(device_status);
            end
            5: begin
                temperature = value[23:16];
                if ((temperature > 8'h81) && (temperature < 8'hC4))
                    value[23:16] = 8'h80;
            end
        endcase
        return value;
    endfunction

    protected task read_snapshot(input ocp_cmd_t command,
                                  output byte_queue_t response,
                                  input string label);
        caliptra_ss_usb_ocp_xfer_result_e result;
        ocp_do_read(command, response, result, label, 0);
        if (result != OCP_XFER_SUCCESS)
            `uvm_fatal("OCP_CMD_TOGGLE",
                $sformatf("%s returned %s.", label, result.name()))
    endtask

    virtual task body();
        // Section 9.2 byte offsets and mutable field masks; no RTL reset values.
        ocp_cmd_t commands[TARGET_COUNT] = '{
            OCP_CMD_PROT_CAP, OCP_CMD_PROT_CAP, OCP_CMD_RECOVERY_CTRL,
            OCP_CMD_RECOVERY_STATUS, OCP_CMD_DEVICE_STATUS, OCP_CMD_HW_STATUS};
        int unsigned offsets[TARGET_COUNT] = '{8, 12, 0, 0, 0, 0};
        bit [31:0] masks[TARGET_COUNT] = '{
            32'h1FFF0000, 32'h00FFFFFF, 32'h000F03FF, 32'h0000FFFF,
            32'h00FF000F, 32'h00FFFF07};
        int unsigned lengths[TARGET_COUNT] = '{15, 15, 3, 2, 7, 4};
        byte_queue_t baseline;
        byte_queue_t expected;
        byte_queue_t response;
        bit [31:0] random_value;
        bit [31:0] value;
        bit [31:0] observed;
        bit [31:0] previous;
        bit [31:0] rising;
        bit [31:0] falling;
        bit [31:0] original;
        int unsigned checked_bits;

        if (!ocp_configure_sem_vif())
            `uvm_fatal("OCP_CMD_TOGGLE", "Missing firmware synchronization interface.")
        ocp_do_initialize_and_check_transport();
        ocp_wait_fw_state_generation(sem_vif.FW_STATE_PATH_READY, 0,
            FW_TIMEOUT, "REGISTER_SWEEP_READY", "OCP_CMD_TOGGLE");
        read_snapshot(OCP_CMD_PROT_CAP, response, "REGISTER_SWEEP_CAPS");
        if ((response.size() != OCP_SPEC_LEN_PROT_CAP) ||
            !(ocp_get_le16(response, OCP_OFF_PC_AGENT_CAPS_LO) &
              (16'h1 << OCP_CAP_HW_STATUS)))
            `uvm_fatal("OCP_CMD_TOGGLE",
                "The five-register sweep requires advertised HW_STATUS support.")
        checked_bits = 0;
        for (int unsigned target = 0; target < TARGET_COUNT; target++) begin
            read_snapshot(commands[target], baseline, "REGISTER_SWEEP_BASELINE");
            if (baseline.size() != lengths[target])
                `uvm_fatal("OCP_CMD_TOGGLE",
                    $sformatf("Target %0d requires a fixed baseline length %0d; got %0d. Variable vendor payloads are outside this campaign.",
                              target, lengths[target], baseline.size()))
            original = 0;
            for (int unsigned b = 0;
                 (b < 4) && ((offsets[target] + b) < baseline.size()); b++)
                original[b*8 +: 8] = baseline[offsets[target] + b];
            firmware_command(SELECT_TARGET, 8'(target));
            random_value = $urandom();
            previous = original;
            rising = 0;
            falling = 0;
            for (int unsigned pattern_phase = 0; pattern_phase < 5; pattern_phase++) begin
                value = legal_pattern(target, pattern_phase, random_value, masks[target]);
                value = (original & ~masks[target]) | (value & masks[target]);
                write_value(value);
                expected = baseline;
                for (int unsigned b = 0;
                     (b < 4) && ((offsets[target] + b) < expected.size()); b++)
                    expected[offsets[target] + b] = value[b*8 +: 8];
                read_snapshot(commands[target], response,
                    $sformatf("REGISTER_SWEEP_T%0d_P%0d", target, pattern_phase));
                if (response != expected)
                    `uvm_fatal("OCP_CMD_TOGGLE",
                        $sformatf("Target %0d phase %0d host readback mismatch: expected=%p got=%p.",
                                  target, pattern_phase, expected, response))
                observed = 0;
                for (int unsigned b = 0;
                     (b < 4) && ((offsets[target] + b) < response.size()); b++)
                    observed[b*8 +: 8] = response[offsets[target] + b];
                rising |= ~previous & observed & masks[target];
                falling |= previous & ~observed & masks[target];
                previous = observed;
                `uvm_info("OCP_CMD_TOGGLE",
                    $sformatf("REGISTER_SWEEP_READBACK target=%0d phase=%0d value=0x%08h mask=0x%08h.",
                              target, pattern_phase, observed, masks[target]),
                    UVM_NONE)
            end
            if ((rising != masks[target]) || (falling != masks[target]))
                `uvm_fatal("OCP_CMD_TOGGLE",
                    $sformatf("Target %0d missing transitions: rising=0x%08h falling=0x%08h expected=0x%08h.",
                              target, rising, falling, masks[target]))
            firmware_command(RESTORE_TARGET);
            read_snapshot(commands[target], response, "REGISTER_SWEEP_RESTORED");
            if (response != baseline)
                `uvm_fatal("OCP_CMD_TOGGLE", "Restored host snapshot differs from baseline.")
            for (int unsigned b = 0; b < 32; b++)
                if (masks[target][b]) checked_bits++;
            `uvm_info("OCP_CMD_TOGGLE",
                $sformatf("REGISTER_SWEEP_TARGET_PASS target=%0d command=0x%02h offset=%0d rising=0x%08h falling=0x%08h restored.",
                          target, commands[target], offsets[target], rising, falling),
                UVM_NONE)
        end
        firmware_command(sem_vif.FW_COMMAND_FLOW_COMPLETE);
        ocp_poll_mcu_axi_idle("OCP_CMD_TOGGLE");
        ocp_publish_transfer_count();
        `uvm_info("OCP_CMD_TOGGLE",
            $sformatf("REGISTER_SWEEP_PASS registers=5 targets=%0d checked_bits=%0d phases_per_target=5; host-observed transitions, not a measured VDB coverage percentage.",
                      TARGET_COUNT, checked_bits),
            UVM_NONE)
    endtask

endclass

`endif
