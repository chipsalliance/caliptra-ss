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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_BASE_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_BASE_SEQUENCE_SVH

// Shared host stimulus and supported MCU mailbox coordination. Firmware
// READY/HELD/RELEASED authorizes stimulus, never substitutes for USB evidence.
class caliptra_ss_usb_ocp_setup_base_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_base_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam time TRANSFER_TIMEOUT = 20us;
    localparam time CHARACTERIZATION_TIMEOUT = 100us;
    localparam logic [3:0] CMD_ARM = 4'hA, CMD_RELEASE = 4'hB;
    localparam logic [3:0] CMD_STALE = 4'hC, CMD_EXPOSE = 4'hD;
    localparam logic [3:0] STATE_READY = 1, STATE_HELD = 2;
    localparam logic [3:0] STATE_RELEASED = 3, STATE_STALE = 4;
    protected caliptra_ss_usb_supersession_checker mixed_checker;
    protected caliptra_ss_usb_supersession_fault_callback fault_callback;
    protected virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
    protected logic [15:0] command_generation, scenario_generation;
    protected logic [3:0] scenario_id;
    protected logic [7:0] ocp_bytes[$];
    // Image-owned identity, not RTL values (usb.c and the dedicated MCU image).
    // USB 2.0 9.6.1 defines the 18-byte descriptor layout.
    protected logic [7:0] new_bytes[$] = '{
        'h12, 'h01, 'h00, 'h02, 'hFF, 'h01, 'h01, 'h40,
        'h34, 'h12, 'h01, 'h00, 'h00, 'h01, 'h01, 'h02, 'h03, 'h01
    };
    protected logic [7:0] old_bytes[$] = '{
        'h12, 'h01, 'h00, 'h02, 'hFF, 'h01, 'h01, 'h40,
        'h5A, 'hC3, 'h5A, 'hA6, 'h78, 'h56, 'h01, 'h02, 'h03, 'h01
    };

    function new(string name = "caliptra_ss_usb_ocp_setup_base_sequence");
        super.new(name);
    endfunction

    protected task prepare();
        bit [7:0] runtime_capabilities[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        if (!uvm_config_db#(caliptra_ss_usb_supersession_checker)::get(
            null, "", "usb_supersession_checker", mixed_checker))
            `uvm_fatal("SETUP_SUPERSESSION", "Boundary scoreboard not configured")
        if (!uvm_config_db#(caliptra_ss_usb_supersession_fault_callback)::get(
            null, "", "usb_supersession_fault_callback", fault_callback))
            `uvm_fatal("SETUP_SUPERSESSION", "Fault callback not configured")
        if (!uvm_config_db#(virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
            null, "uvm_test_top.env", "usb_legacy_ep0_observer_if", observer_vif))
            `uvm_fatal("SETUP_SUPERSESSION", "Firmware coordination interface not configured")
        initialize_ocp_transport();
        ocp_try_read(OCP_CMD_PROT_CAP, runtime_capabilities, result,
                     "SUPERSESSION_CAPABILITIES");
        if (result != OCP_XFER_SUCCESS)
            `uvm_fatal("SETUP_SUPERSESSION", $sformatf(
                "PROT_CAP discovery did not complete (%s); cannot establish a response baseline.",
                result.name()))
        check_prot_cap_response(runtime_capabilities, "SUPERSESSION_CAPABILITIES");
        if (runtime_capabilities.size() < OCP_SPEC_LEN_PROT_CAP)
            `uvm_fatal("SETUP_SUPERSESSION",
                "PROT_CAP response is too short to establish a response baseline.")
        ocp_bytes.delete();
        foreach (runtime_capabilities[i]) ocp_bytes.push_back(runtime_capabilities[i]);
        command_generation = observer_vif.last_mcu_command_generation;
        if ((usb_cfg.remote_device_cfg.size() == 0) ||
            (usb_cfg.remote_device_cfg[0].endpoint_cfg.size() == 0))
            `uvm_fatal("SETUP_SUPERSESSION", "No discovered remote EP0 retry configuration")
        // Bounded NAK budget for the firmware barrier, without changing VIP
        // timing checks, PING pacing, or report fail effects.
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].max_retry_due_to_nak = 512;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
            max_retry_due_to_nak_before_moving_to_next_ep = 1;
        host_agent_h.reconfigure(usb_cfg);
    endtask

    protected task command(input logic [3:0] opcode,
                           input logic [3:0] argument = 0);
        bit acknowledged;
        if (command_generation == 16'hFFFF)
            `uvm_fatal("SETUP_SUPERSESSION", "Firmware command generation exhausted")
        command_generation++;
        observer_vif.issue_mcu_command_bounded(
            opcode, command_generation, argument, TRANSFER_TIMEOUT, acknowledged);
        if (!acknowledged)
            `uvm_fatal("SETUP_SUPERSESSION", $sformatf(
                "MCU command op=%h gen=%0d timed out", opcode, command_generation))
    endtask

    protected task wait_state(input logic [3:0] state);
        bit found;
        logic [31:0] expected;
        expected = {8'hE1, state, scenario_id, scenario_generation};
        found = 0;
        fork : bounded_state
            begin
                wait (observer_vif.fw_snapshot_header === expected);
                found = 1;
            end
            #(TRANSFER_TIMEOUT);
        join_any
        disable bounded_state;
        if (!found)
            `uvm_fatal("SETUP_SUPERSESSION", $sformatf(
                "MCU state=%h scenario=%0d gen=%0d timed out", state,
                scenario_id, scenario_generation))
    endtask

    protected task arm_scenario(input logic [3:0] id);
        scenario_id = id;
        scenario_generation = command_generation + 1;
        command(CMD_ARM, id);
        wait_state(STATE_READY);
        mixed_checker.begin_window(scenario_generation, dev_addr_v);
    endtask

    protected task release_legacy(input int wire_index, input bit expose = 0);
        wait_state(STATE_HELD);
        mixed_checker.wait_evidence(wire_index, 1, TRANSFER_TIMEOUT);
        mixed_checker.note_release(wire_index);
        command(expose ? CMD_EXPOSE : CMD_RELEASE);
        wait_state(STATE_RELEASED);
    endtask

    protected function svt_usb_transfer build_request(input bit ocp,
                                                      input string label);
        svt_usb_transfer req;
        int unsigned length;
        int iface;
        req = svt_usb_transfer::type_id::create(label);
        req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        length = ocp ? wMaxRdTransferSize : 18;
        iface = get_iface_num();
        // USB 2.0 9.4.3; OCP Recovery 1.1 8.5.1 read encapsulation.
        if (!req.randomize() with {
            xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
            device_address == dev_addr_v;
            endpoint_number == 0;
            setup_data_bmrequesttype_dir == svt_usb_types::DEVICE_TO_HOST;
            setup_data_bmrequesttype_type ==
                (ocp ? svt_usb_types::CLASS : svt_usb_types::STANDARD);
            setup_data_bmrequesttype_recipient ==
                (ocp ? svt_usb_types::BMREQ_INTERFACE : svt_usb_types::BMREQ_DEVICE);
            setup_data_brequest == (ocp ? OCP_BREQUEST_XFER : 8'h06);
            setup_data_w_value == (ocp ? {8'h00, OCP_CMD_PROT_CAP} : 16'h0100);
            setup_data_w_index == (ocp ? 16'(iface) : 16'h0000);
            setup_data_w_length == 16'(length);
            payload_start_ix == 0;
            payload_intended_byte_count == length;
        })
            `uvm_fatal("SETUP_SUPERSESSION", $sformatf("%s randomization failed", label))
        return req;
    endfunction

    protected task execute_request(input svt_usb_transfer req,
        input bit interrupt_request,
        input svt_usb_transfer::xfer_stage_enum completed_stage, input string label);
        bit retired, bounded;
        retired = 0;
        bounded = 0;
        fork : bounded_request
            begin
                fork
                    begin
                        // Persistent completion, also safe if retirement
                        // occurs before this fork branch begins waiting.
                        req.end_event.wait_on();
                        retired = 1;
                    end
                    begin
                        start_item(req, -1, p_sequencer.xfer_sequencer);
                        finish_item(req, -1);
                    end
                    begin
                        if (interrupt_request) begin
                            // stage_end=1 is essential: abort bookkeeping
                            // immediately after the completed transaction.
                            req.wait_for_control_transfer_stage(completed_stage, 1'b1);
                            req.abort(1'b1);
                        end
                    end
                join
                bounded = 1;
            end
            #(TRANSFER_TIMEOUT);
        join_any
        disable bounded_request;
        if (!bounded || !retired) begin
            req.abort(1'b1);
            `uvm_fatal("SETUP_SUPERSESSION", $sformatf("%s did not retire", label))
        end
        if (interrupt_request) begin
            if (get_xfer_result(req) != OCP_XFER_ABORTED)
                `uvm_error("SETUP_SUPERSESSION", $sformatf("%s was not interrupted", label))
        end else if (get_xfer_result(req) != OCP_XFER_SUCCESS)
            `uvm_error("SETUP_SUPERSESSION", $sformatf("%s did not complete", label))
    endtask

    protected task check_request(input int index, input svt_usb_transfer req,
        input bit ocp, input bit complete, input bit data_completed,
        input bit stale = 0);
        mixed_checker.check_request(index, req, complete, data_completed,
            ocp ? ocp_bytes : (stale ? old_bytes : new_bytes), TRANSFER_TIMEOUT);
    endtask

    protected function void finish_stimulus();
        uvm_config_db#(int unsigned)::set(
            null, "", "ocp_transfers_issued", transfers_issued);
    endfunction
endclass
`endif
