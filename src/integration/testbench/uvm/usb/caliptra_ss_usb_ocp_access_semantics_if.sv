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

// =============================================================================
// caliptra_ss_usb_ocp_access_semantics_if
//
// TB-owned synchronization interface for OCP Recovery CPUif tests. It exposes
// architectural top-level outputs and a generation-qualified command channel
// to Caliptra firmware; no internal DUT signals are probed.
//
// Signal mapping for SS-level OCP Recovery access-semantics checks:
//
//   fw_exec_ctrl[124:0]
//     Connected to cptra_ss_cptra_generic_fw_exec_ctrl_o.
//     SS top exports register SS_GENERIC_FW_EXEC_CTRL_0[127:3] as this
//     125-bit output, so register bit N maps to fw_exec_ctrl[N-3] for
//     N in [3..127].
//     Firmware convention for these tests:
//       state[7:0] -> register[10:3] -> fw_exec_ctrl[7:0]
//       data[7:0]  -> register[18:11] -> fw_exec_ctrl[15:8]
//       generation[15:0] -> register[34:19] -> fw_exec_ctrl[31:16]
//
//   subsystem_reset_n
//     Connected to cptra_ss_rst_b_o. Used by sequences to verify that
//     CPUif writes to DEVICE_RESET do not trigger the RA reset action.
//
//   recovery_payload_available
//     Connected to cptra_ss_usb_recovery_payload_available_o.
//
//   recovery_image_activated
//     Connected to cptra_ss_usb_recovery_image_activated_o.
//
// Usage: obtain a virtual handle via
//   uvm_config_db#(virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
//       ..., "ocp_access_semantics_if", vif)
// =============================================================================

interface caliptra_ss_usb_ocp_access_semantics_if;

    localparam logic [31:0] FW_COMMAND_MAGIC = 32'h4F43_5041;
    localparam logic [7:0] FW_COMMAND_SET_PATH_DISABLE = 8'h01;
    localparam logic [7:0] FW_COMMAND_CLEAR_PATH_DISABLE = 8'h02;
    localparam logic [7:0] FW_STATE_COMMAND_BUSY = 8'h1F;
    localparam logic [7:0] FW_STATE_PATH_READY = 8'h20;
    localparam logic [7:0] FW_STATE_PATH_DISABLED = 8'h21;
    localparam logic [7:0] FW_STATE_PATH_ENABLED = 8'h22;
    localparam logic [7:0] FW_STATE_COMMAND_ERROR = 8'h2F;

    // Architectural top-level observations, driven by assign in the TB.
    logic [124:0] fw_exec_ctrl;
    logic         subsystem_reset_n;
    logic         recovery_payload_available;
    logic         recovery_image_activated;
    logic [63:0]  fw_command_wires;
    bit           fw_command_active;
    bit           subsystem_reset_seen;
    bit           recovery_image_activated_seen;

    initial fw_command_wires = '0;
    initial fw_command_active = 1'b0;
    initial subsystem_reset_seen = 1'b0;
    initial recovery_image_activated_seen = 1'b0;

    always @(negedge subsystem_reset_n) begin
        subsystem_reset_seen = 1'b1;
    end

    always @(posedge recovery_image_activated) begin
        recovery_image_activated_seen = 1'b1;
    end

    // -------------------------------------------------------------------------
    // get_fw_state
    //   Returns firmware state code written in register[10:3] (-> [7:0]).
    // -------------------------------------------------------------------------
    function automatic logic [7:0] get_fw_state();
        return fw_exec_ctrl[7:0];
    endfunction

    // -------------------------------------------------------------------------
    // get_fw_data
    //   Returns firmware data byte written in register[18:11] (-> [15:8]).
    // -------------------------------------------------------------------------
    function automatic logic [7:0] get_fw_data();
        return fw_exec_ctrl[15:8];
    endfunction

    function automatic logic [15:0] get_fw_generation();
        return fw_exec_ctrl[31:16];
    endfunction

    // -------------------------------------------------------------------------
    // wait_for_fw_state_bounded
    //   Polls fw_exec_ctrl[7:0] for target_state. Returns found=1 if observed
    //   within max_polls * poll_period, otherwise found=0.
    //   All loops are bounded to guarantee termination.
    // -------------------------------------------------------------------------
    task automatic wait_for_fw_state_bounded(
        input  logic [7:0]  target_state,
        input  int unsigned max_polls,
        input  time         poll_period,
        output bit          found);

        found = 1'b0;
        for (int unsigned i = 0; i < max_polls; i++) begin
            if (fw_exec_ctrl[7:0] === target_state) begin
                found = 1'b1;
                return;
            end
            #(poll_period);
        end
    endtask

    task automatic wait_for_fw_state_data_bounded(
        input  logic [7:0]  target_state,
        input  logic [7:0]  target_data,
        input  int unsigned max_polls,
        input  time         poll_period,
        output bit          found);

        found = 1'b0;
        for (int unsigned i = 0; i < max_polls; i++) begin
            if ((fw_exec_ctrl[7:0] === target_state) &&
                (fw_exec_ctrl[15:8] === target_data)) begin
                found = 1'b1;
                return;
            end
            #(poll_period);
        end
    endtask

    task automatic issue_fw_command(
        input logic [7:0] opcode,
        input logic [15:0] generation);

        fw_command_wires = {
            FW_COMMAND_MAGIC,
            generation,
            opcode,
            8'h00
        };
        fw_command_active = 1'b1;
    endtask

    function automatic void clear_fw_command();
        fw_command_active = 1'b0;
        fw_command_wires = '0;
    endfunction

    task automatic wait_for_fw_state_generation_bounded(
        input  logic [7:0]  target_state,
        input  logic [15:0] target_generation,
        input  time         timeout,
        output bit          found);

        found = 1'b0;
        if ((get_fw_state() === target_state) &&
            (get_fw_generation() === target_generation)) begin
            found = 1'b1;
            return;
        end

        fork : fw_state_generation_timeout
            begin
                wait (
                    (((fw_exec_ctrl[7:0] === target_state) ||
                      (fw_exec_ctrl[7:0] === FW_STATE_COMMAND_ERROR)) &&
                     (fw_exec_ctrl[31:16] === target_generation)));
                found = fw_exec_ctrl[7:0] === target_state;
            end
            begin
                #(timeout);
            end
        join_any
        disable fw_state_generation_timeout;
    endtask

    task automatic set_path_disable_bounded(
        input  bit          disabled,
        input  logic [15:0] generation,
        input  time         timeout,
        output bit          complete);

        logic [7:0] opcode;
        logic [7:0] expected_state;
        logic [7:0] observed_data;

        opcode = disabled ?
            FW_COMMAND_SET_PATH_DISABLE :
            FW_COMMAND_CLEAR_PATH_DISABLE;
        expected_state = disabled ?
            FW_STATE_PATH_DISABLED :
            FW_STATE_PATH_ENABLED;

        issue_fw_command(opcode, generation);
        wait_for_fw_state_generation_bounded(
            expected_state,
            generation,
            timeout,
            complete);
        if (complete) begin
            observed_data = get_fw_data();
            if (observed_data[0] !== disabled) begin
                complete = 1'b0;
            end
        end
        clear_fw_command();
    endtask

    function automatic void clear_subsystem_reset_seen();
        subsystem_reset_seen = 1'b0;
    endfunction

    function automatic void clear_recovery_image_activated_seen();
        recovery_image_activated_seen =
            (recovery_image_activated === 1'b1);
    endfunction

endinterface : caliptra_ss_usb_ocp_access_semantics_if
