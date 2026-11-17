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

`ifndef CALIPTRA_SS_USB_OCP_ACCESS_COLLISION_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_ACCESS_COLLISION_SEQUENCE_SVH

class caliptra_ss_usb_ocp_access_collision_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_access_collision_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_collision_if collision_vif;
    protected virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
    localparam int unsigned MAX_TRANSFERS = 256;
    localparam time SCENARIO_TIMEOUT = 2ms;
    localparam time COMMAND_TIMEOUT = 100us;
    logic [15:0] generation = 1;

    function new(string name = "caliptra_ss_usb_ocp_access_collision_sequence");
        super.new(name);
    endfunction

    protected task ocp_collision_issue_mcu_command_and_check_ack(input logic [3:0] opcode,
                           input int unsigned scenario_id);
        bit acknowledged;
        observer_vif.issue_mcu_command_bounded(
            opcode, generation++, 4'(scenario_id), COMMAND_TIMEOUT, acknowledged);
        if (!acknowledged)
            `uvm_fatal("OCP_COLLISION", "MCU command acknowledgement timed out")
    endtask

    protected task ocp_collision_do_exercise_and_check_scenario(input int unsigned scenario_id,
                                input logic [31:0] capability_word);
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;
        bit [7:0] response[$];
        logic [31:0] ctrl_word;
        bit found;
        int unsigned attempts;

        // OCP v1.1 Sec 9.2: CMS default 0 and no image activation.
        ocp_do_recovery_ctrl_write(0, OCP_RC_IMAGE_SEL_NONE, 0,
                            "COLLISION_CTRL_BASELINE");
        collision_vif.arm(scenario_id, capability_word, 0);
        ocp_collision_issue_mcu_command_and_check_ack(observer_vif.MCU_COMMAND_COLLISION_START,
            scenario_id);
        found = 0;
        attempts = 0;
        fork : bounded_collision_scenario
            begin
                for (attempts = 0; attempts < MAX_TRANSFERS; attempts++) begin
                    if (scenario_id < collision_vif.CTRL_WRITE_EXT_READ) begin
                        ocp_do_read(OCP_CMD_PROT_CAP, response, ignored_result, "COLLISION_PROT_CAP");
                        if (response.size() <= OCP_OFF_PC_AGENT_CAPS_HI ||
                            ocp_get_le32(response, OCP_OFF_PC_VERSION_MAJOR) !==
                            capability_word)
                            `uvm_fatal("OCP_COLLISION", "USB PROT_CAP read changed runtime data")
                    end else begin
                        ctrl_word = ((attempts[0] ^
                            (scenario_id == collision_vif.CTRL_WRITE_EXT_READ)) ?
                            32'(OCP_RC_IMAGE_SEL_CMS) : 32'(OCP_RC_IMAGE_SEL_NONE)) << 8;
                        collision_vif.set_usb_ctrl(ctrl_word);
                        ocp_do_recovery_ctrl_write(0, ctrl_word[15:8], 0,
                                            "COLLISION_RECOVERY_CTRL");
                    end
                    if (collision_vif.blocked_hits > 0 &&
                        (scenario_id != collision_vif.CTRL_WRITE_EXT_READ ||
                         collision_vif.deferred_read_hits > 0) &&
                        (scenario_id != collision_vif.PROT_READ_EXT_WRITE ||
                         collision_vif.tail_hits > 0)) begin
                        found = 1;
                        break;
                    end
                end
            end
            begin
                #(SCENARIO_TIMEOUT);
                `uvm_fatal("OCP_COLLISION",
                    $sformatf("Scenario %0d wall-clock timeout: blocked=%0d tail=%0d",
                              scenario_id, collision_vif.blocked_hits, collision_vif.tail_hits))
            end
        join_any
        disable bounded_collision_scenario;
        ocp_collision_issue_mcu_command_and_check_ack(observer_vif.MCU_COMMAND_COLLISION_STOP,
            scenario_id);
        collision_vif.finish();
        if (!found)
            `uvm_fatal("OCP_COLLISION",
                $sformatf("Scenario %0d exhausted %0d transfers: blocked=%0d tail=%0d",
                          scenario_id, MAX_TRANSFERS, collision_vif.blocked_hits,
                          collision_vif.tail_hits))
        if (scenario_id >= collision_vif.CTRL_WRITE_EXT_READ) begin
            ocp_do_read(OCP_CMD_RECOVERY_CTRL, response, ignored_result, "COLLISION_CTRL_FINAL");
            if (response.size() != OCP_SPEC_LEN_RECOVERY_CTRL ||
                {8'h00, response[2], response[1], response[0]} !==
                collision_vif.expected_ctrl)
                `uvm_fatal("OCP_COLLISION", "Final USB readback did not match committed access order")
        end
        `uvm_info("OCP_COLLISION",
            $sformatf("Scenario %0d PASS: attempts=%0d blocked=%0d tail=%0d deferred_reads=%0d EXT issues/completions=%0d/%0d",
                      scenario_id, attempts + 1, collision_vif.blocked_hits,
                      collision_vif.tail_hits, collision_vif.deferred_read_hits,
                      collision_vif.issues,
                      collision_vif.completions), UVM_NONE)
    endtask

    virtual task body();
        caliptra_ss_usb_ocp_xfer_result_e ignored_result;
        bit [7:0] prot_cap[$];
        logic [31:0] capability_word;
        if (!uvm_config_db#(virtual caliptra_ss_usb_ocp_collision_if)::get(
                null, "uvm_test_top.env", "ocp_collision_if", collision_vif))
            `uvm_fatal("OCP_COLLISION", "Bound collision monitor handle missing")
        if (!uvm_config_db#(virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                null, "uvm_test_top.env", "usb_legacy_ep0_observer_if", observer_vif))
            `uvm_fatal("OCP_COLLISION", "MCU command handle missing")
        ocp_do_initialize_and_check_transport();
        ocp_do_read(OCP_CMD_PROT_CAP, prot_cap, ignored_result, "COLLISION_RUNTIME_CAPABILITIES");
        if (prot_cap.size() <= OCP_OFF_PC_AGENT_CAPS_HI)
            `uvm_fatal("OCP_COLLISION", "Runtime PROT_CAP response too short")
        capability_word = ocp_get_le32(prot_cap, OCP_OFF_PC_VERSION_MAJOR);
        for (int unsigned scenario_id = 0; scenario_id < 4; scenario_id++)
            ocp_collision_do_exercise_and_check_scenario(scenario_id, capability_word);
        ocp_poll_mcu_axi_idle("OCP_COLLISION_FINISH");
        ocp_publish_transfer_count();
    endtask
endclass
`endif
