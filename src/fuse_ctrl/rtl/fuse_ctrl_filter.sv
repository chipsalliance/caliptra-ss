// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
`ifndef FUSE_CTRL_FILTER_SV
`define FUSE_CTRL_FILTER_SV


// Include the generated access control table.
`include "fc_access_control_table.sv"

module fuse_ctrl_filter
    import axi_struct_pkg::*;
    import otp_ctrl_reg_pkg::*;
    import otp_ctrl_pkg::*;
(
    input wire clk_i,
    input wire rst_n_i,
    input wire fc_init_done,

    // Core interface
    input  axi_wr_req_t  core_axi_wr_req,  // AXI write request from the core
    input axi_wr_rsp_t  core_axi_wr_rsp,  // AXI write response to the core

    // Filtered interface (to the fuse controller)
    input wire discarded_fuse_write_i,
    output logic discard_fuse_write_o
);

//---------------------------------------------------------------------
// Internal signal declarations
//---------------------------------------------------------------------
fc_table_state_t table_fsm_current_st, table_fsm_next_st;
logic first_write_addr, second_write_addr, write_event, trigger_table_check, partition_cmd_axi_addr, all_same_id;

logic [FC_TABLE_NUM_RANGES-1:0] wr_allowed_vec;
logic wr_req_allowed;
logic [31:0] latched_fuse_addr;
logic [31:0]  req_axi_user_id, latched_data_id0, latched_data_id1, latched_addr_id, latched_cmd_id;
logic latch_addr, latch_data_id0, latch_data_id1, latch_addr_id, latch_cmd_id, clear_records;
logic discard_fuse_write;

//---------------------------------------------------------------------
// Extract AXI user ID from the core write request
// (Typically comes from the AWUSER channel field)
assign req_axi_user_id = core_axi_wr_req.awuser;
// OR-reduce all the individual allowed bits to obtain the overall write allowed signal.
assign wr_req_allowed = |wr_allowed_vec;

always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        table_fsm_current_st    <= RESET_ST;
        latched_fuse_addr       <= '0;
        latched_data_id0        <= '0;
        latched_data_id1        <= '0;
        latched_addr_id         <= '0;
        latched_cmd_id          <= '0;
        discard_fuse_write_o    <= '0;
    end else begin
        table_fsm_current_st <= table_fsm_next_st;
        discard_fuse_write_o <= discard_fuse_write;
        // If clear_records is asserted, reset all latched registers
        if (clear_records) begin
            latched_fuse_addr <= '0;
            latched_data_id0  <= '0;
            latched_data_id1  <= '0;
            latched_addr_id   <= '0;
            latched_cmd_id    <= '0;
        end else begin
            if (latch_addr)
                latched_fuse_addr <= core_axi_wr_req.wdata;
            if (latch_data_id0) begin
                latched_data_id0 <= req_axi_user_id;
                latched_data_id1 <= req_axi_user_id;
            end else if (latch_data_id1) begin
                latched_data_id1 <= req_axi_user_id;
            end
            if (latch_addr_id)
                latched_addr_id <= req_axi_user_id;
            if (latch_cmd_id)
                latched_cmd_id <= req_axi_user_id;
        end
    end
end

//---------------------------------------------------------------------
// Combinational Block: Generate the allowed vector based on the access control table.
// For each entry in the table, check if the latched fuse address is within the allowed range
// and if the AXI user ID matches the allowed ID. Each bit in wr_allowed_vec corresponds to an entry.
always_comb begin
    wr_allowed_vec = '0;
    for (int i = 0; i < FC_TABLE_NUM_RANGES; i = i + 1) begin : gen_wr_allowed
        wr_allowed_vec[i] = ((latched_fuse_addr >= access_control_table[i].lower_addr) &&
                                    (latched_fuse_addr <= access_control_table[i].upper_addr) &&
                                    (latched_data_id0 == access_control_table[i].axi_user_id));
    end
end

always_comb begin
    case (table_fsm_current_st)
        RESET_ST: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b1;
            discard_fuse_write= 1'b0;
            if (fc_init_done) begin
                table_fsm_next_st = IDLE_ST;
            end else begin
                table_fsm_next_st = RESET_ST;
            end
        end
        //-------------------------------------------------------------------------
        // IDLE_ST: Monitor for a valid write address for either the first or second fuse data.
        // If a valid address is detected, latch the corresponding data ID and transition to WDATA_ADDR_ST.
        // Otherwise, clear records and remain in IDLE.
        IDLE_ST: begin            
            latch_addr        = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            discard_fuse_write= 1'b0;
            if (first_write_addr) begin
                latch_data_id0     = 1'b1;
                latch_data_id1     = 1'b0;
                clear_records      = 1'b0;
                table_fsm_next_st  = WDATA_ADDR_ST;
            end else if (second_write_addr) begin
                latch_data_id0     = 1'b0;
                latch_data_id1     = 1'b1;
                clear_records      = 1'b0;
                table_fsm_next_st  = WDATA_ADDR_ST;
            end else begin
                latch_data_id0     = 1'b0;
                latch_data_id1     = 1'b0;
                clear_records      = 1'b1;
                table_fsm_next_st  = IDLE_ST;
            end
        end     
        //-------------------------------------------------------------------------
        // WDATA_ADDR_ST: Wait for a valid write event that carries the data.
        // Remain in this state until the write event is detected, then move to WDATA_ST.
        WDATA_ADDR_ST: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b0;
            if (write_event) begin
                table_fsm_next_st = WDATA_ST;
            end else begin
                table_fsm_next_st = WDATA_ADDR_ST;
            end
        end  
        //-------------------------------------------------------------------------
        // WDATA_ST: Process the write data.
        // If a table check is triggered, latch the address ID and transition to the fuse address phase.
        // Otherwise, if additional data writes occur due to the granulartiy, latch the corresponding data ID.
        WDATA_ST: begin
            latch_addr        = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b0;
            if (trigger_table_check) begin
                table_fsm_next_st = FUSE_ADDR_AXI_ADDR_ST;
                latch_addr_id     = 1'b1;
                latch_data_id0    = 1'b0;
                latch_data_id1    = 1'b0;
            end else if (first_write_addr) begin
                table_fsm_next_st = WDATA_ADDR_ST;
                latch_addr_id     = 1'b0;
                latch_data_id0    = 1'b1;
                latch_data_id1    = 1'b0;
            end else if (second_write_addr) begin
                table_fsm_next_st = WDATA_ADDR_ST;
                latch_addr_id     = 1'b0;
                latch_data_id0    = 1'b0;
                latch_data_id1    = 1'b1;
            end else begin
                table_fsm_next_st = WDATA_ST;
                latch_addr_id     = 1'b0;
                latch_data_id0    = 1'b0;
                latch_data_id1    = 1'b0;
            end
        end
        //-------------------------------------------------------------------------
        // FUSE_ADDR_AXI_ADDR_ST: Process the fuse address write phase.
        // When a write event is detected, latch the fuse address and transition to FUSE_ADDR_AXI_WR_ST.
        FUSE_ADDR_AXI_ADDR_ST: begin
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b0;
            if (write_event) begin
                table_fsm_next_st = FUSE_ADDR_AXI_WR_ST;
                latch_addr        = 1'b1;
            end else begin
                table_fsm_next_st = FUSE_ADDR_AXI_ADDR_ST;
                latch_addr        = 1'b0;
            end
        end         
        //-------------------------------------------------------------------------
        // FUSE_ADDR_AXI_WR_ST: Wait for the command address phase.
        // If the partition command address is detected, latch the command ID and move to FUSE_CMD_AXI_ADDR_ST.       
        FUSE_ADDR_AXI_WR_ST: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b0;
            if (partition_cmd_axi_addr) begin
                table_fsm_next_st = FUSE_CMD_AXI_ADDR_ST;
                latch_cmd_id      = 1'b1;
            end else begin
                table_fsm_next_st = FUSE_ADDR_AXI_WR_ST;
                latch_cmd_id      = 1'b0;
            end
        end
        //-------------------------------------------------------------------------
        // FUSE_CMD_AXI_ADDR_ST: Process the fuse command.
        // Check if the fuse write is allowed (using both the access control table and a consistency check
        // on all latched AXI IDs). If not allowed, assert discard_fuse_write and move to discard state.   
        FUSE_CMD_AXI_ADDR_ST: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            if (! wr_req_allowed || !all_same_id)begin
                discard_fuse_write= 1'b1;
                table_fsm_next_st = DISCARD_FUSE_CMD_AXI_WR_ST;
            end else if (write_event) begin
                discard_fuse_write= 1'b0;
                table_fsm_next_st = IDLE_ST;
            end else begin
                discard_fuse_write= 1'b0;
                table_fsm_next_st = FUSE_CMD_AXI_ADDR_ST;
            end
        end
        //-------------------------------------------------------------------------
        // DISCARD_FUSE_CMD_AXI_WR_ST: Remain in discard state until the external
        // signal indicates that the fuse write has been discarded.
        DISCARD_FUSE_CMD_AXI_WR_ST: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b1;
            if (discarded_fuse_write_i) begin
                table_fsm_next_st = IDLE_ST;
            end else begin
                table_fsm_next_st = DISCARD_FUSE_CMD_AXI_WR_ST;
            end
        end     
        //-------------------------------------------------------------------------
        // Default case: Ensure safe signal assignments and return to IDLE.
        default: begin
            latch_addr        = 1'b0;
            latch_data_id0    = 1'b0;
            latch_data_id1    = 1'b0;
            latch_addr_id     = 1'b0;
            latch_cmd_id      = 1'b0;
            clear_records     = 1'b0;
            discard_fuse_write= 1'b0;
            table_fsm_next_st = IDLE_ST;
        end
    endcase
end

//---------------------------------------------------------------------
// - first_write_addr and second_write_addr identify which data register is targeted.
// - write_event indicates that a valid write (data channel) is occurring.
// - trigger_table_check indicates that the address phase is active.
// - partition_cmd_axi_addr indicates that the command phase is active.
// - all_same_id verifies that the AXI user ID is consistent across all phases.

always_comb begin
    first_write_addr            = (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready && core_axi_wr_req.awaddr[CoreAw-1:0] == OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET);
    second_write_addr           = (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready && core_axi_wr_req.awaddr[CoreAw-1:0] == OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET);
    write_event                 = (core_axi_wr_req.wvalid && core_axi_wr_rsp.wready);
    trigger_table_check         = (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready && core_axi_wr_req.awaddr[CoreAw-1:0] == OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET);
    partition_cmd_axi_addr      = (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready && core_axi_wr_req.awaddr[CoreAw-1:0] == OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET);
    all_same_id                 = (latched_data_id1 == latched_data_id0) && (latched_data_id0 == latched_addr_id) &&  (latched_addr_id == latched_cmd_id);
end


endmodule

`endif // FUSE_CTRL_FILTER_SV
