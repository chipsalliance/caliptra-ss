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

module mci_boot_seqr
import mci_pkg::*;
#(
    parameter MIN_MCU_RST_COUNTER_WIDTH = 4 // Determines 
)
(
    input logic clk,
    input logic mci_rst_b,

    // DFT
    input scan_mode,

    // Reset controls
    output logic mcu_rst_b,
    output logic cptra_rst_b,

    // Internal signals
    input  logic caliptra_boot_go,
    input  logic mcu_rst_req,
    output logic fw_boot_upd_reset,     // First MCU reset request
    output logic fw_hitless_upd_reset,  // Other MCU reset requests
    output logic mcu_reset_once, // Has MCU been reset before?
    output mci_boot_fsm_state_e boot_fsm,

    // SoC signals
    input  logic mci_boot_seq_brkpoint,
    input  logic mcu_sram_fw_exec_region_lock,
    input  logic mcu_no_rom_config,                // Determines boot sequencer boot flow

    // LCC Signals
    input  logic lc_done,
    output logic lc_init,

    // FC Signals
    input  logic fc_opt_done,
    output logic fc_opt_init

    // Caliptra signals
);

mci_boot_fsm_state_e boot_fsm_nxt;
mci_boot_fsm_state_e boot_fsm_prev;

logic lc_done_sync;
logic lc_init_nxt;

logic fc_opt_done_sync;
logic fc_opt_init_nxt;

logic mci_boot_seq_brkpoint_sync;

logic mcu_no_rom_config_sync;

logic mcu_rst_b_ff  ;
logic cptra_rst_b_ff;
logic mcu_rst_b_nxt;
logic cptra_rst_b_nxt;

logic fw_boot_upd_reset_nxt;     // First MCU reset request
logic fw_hitless_upd_reset_nxt;  // Other MCU reset requests
logic mcu_reset_once_nxt;

logic [MIN_MCU_RST_COUNTER_WIDTH-1:0] min_mcu_rst_count;
logic [MIN_MCU_RST_COUNTER_WIDTH-1:0] min_mcu_rst_count_nxt;
logic min_mcu_rst_count_elapsed;
logic min_mcu_rst_count_elapsed_nxt;
        
/////////////////////////////////////////////////
// DFT                                 
/////////////////////////////////////////////////
assign mcu_rst_b   = scan_mode ? mcu_rst_b   :  mcu_rst_b_ff;
assign cptra_rst_b = scan_mode ? cptra_rst_b :  cptra_rst_b_ff;

/////////////////////////////////////////////////
// Sync signals into local clock domain
/////////////////////////////////////////////////
caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_lc_done (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(lc_done),
  .q_o(lc_done_sync));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_fc_opt_done (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(fc_opt_done),
  .q_o(fc_opt_done_sync));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mci_boot_seq_brkpoint (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(mci_boot_seq_brkpoint),
  .q_o(mci_boot_seq_brkpoint_sync));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_no_rom_config (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(mcu_no_rom_config),
  .q_o(mcu_no_rom_config_sync));

/////////////////////////////////////////////////
// Boot FSM
/////////////////////////////////////////////////
always_ff @(posedge clk or negedge mci_rst_b) begin
    if(!mci_rst_b) begin
        boot_fsm                    <= BOOT_IDLE;
        boot_fsm_prev               <= BOOT_IDLE;
        fc_opt_init                 <= '0;
        lc_init                     <= '0;
        mcu_rst_b_ff                <= '0;
        cptra_rst_b_ff              <= '0;
        mcu_reset_once              <= '0;
        fw_boot_upd_reset           <= '0;     
        fw_hitless_upd_reset        <= '0;  
        min_mcu_rst_count_elapsed   <= '0;
        min_mcu_rst_count           <= '0;
    end
    else begin
        boot_fsm        <= boot_fsm_nxt;
        boot_fsm_prev   <= (boot_fsm != boot_fsm_nxt) ? boot_fsm : boot_fsm_prev; // Capture where FSM came from
        fc_opt_init     <= fc_opt_init_nxt;
        lc_init         <= lc_init_nxt;
        mcu_rst_b_ff    <= mcu_rst_b_nxt;
        cptra_rst_b_ff  <= cptra_rst_b_nxt;
        mcu_reset_once  <= mcu_reset_once_nxt;
        fw_boot_upd_reset <= fw_boot_upd_reset_nxt;     
        fw_hitless_upd_reset <= fw_hitless_upd_reset_nxt;  
        min_mcu_rst_count_elapsed <= min_mcu_rst_count_elapsed_nxt;
        min_mcu_rst_count <= min_mcu_rst_count_nxt;
    end
end


always_comb begin
    boot_fsm_nxt    = boot_fsm;
    fc_opt_init_nxt = fc_opt_init;
    lc_init_nxt     = lc_init;
    mcu_rst_b_nxt   = mcu_rst_b_ff;
    cptra_rst_b_nxt = cptra_rst_b_ff;
    mcu_reset_once_nxt  = mcu_reset_once;
    fw_boot_upd_reset_nxt = fw_boot_upd_reset;     
    fw_hitless_upd_reset_nxt = fw_hitless_upd_reset;  
    unique case(boot_fsm)
        BOOT_IDLE: begin
            // Can only transition into IDLE on MCI reset
            // If this changes we need to add init signal values
            // for FC, LCC, MCU, CPTRA
            boot_fsm_nxt = BOOT_OTP_FC; 
        end
        BOOT_OTP_FC: begin
            fc_opt_init_nxt = 1'b1;
            if (fc_opt_done_sync) begin
                boot_fsm_nxt = BOOT_LCC; 
            end
        end
        BOOT_LCC: begin
            lc_init_nxt = 1'b1;
            if(lc_done_sync) begin
                boot_fsm_nxt = BOOT_BREAKPOINT;
            end
        end
        BOOT_BREAKPOINT: begin
            if(!mci_boot_seq_brkpoint_sync) begin 
                boot_fsm_nxt = BOOT_MCU;
            end
        end
        BOOT_MCU: begin
            if (boot_fsm_prev == BOOT_RST_MCU) begin
                boot_fsm_nxt = BOOT_WAIT_MCU_RST_REQ;
            end
            else begin 
                boot_fsm_nxt = BOOT_WAIT_CLPA_GO;
            end
            mcu_rst_b_nxt = 1'b1;
        end
        BOOT_WAIT_CLPA_GO: begin
            if(caliptra_boot_go) begin
                boot_fsm_nxt = BOOT_CPTRA;
            end
        end
        BOOT_CPTRA: begin
            cptra_rst_b_nxt = 1'b1;
            boot_fsm_nxt = BOOT_WAIT_MCU_RST_REQ;
        end
        BOOT_WAIT_MCU_RST_REQ: begin
            if(mcu_rst_req) begin
                boot_fsm_nxt        = BOOT_RST_MCU;
                fw_boot_upd_reset_nxt   = !mcu_reset_once;
                fw_hitless_upd_reset_nxt = mcu_reset_once;
            end
        end
        BOOT_RST_MCU: begin
            mcu_rst_b_nxt = 1'b0;
            mcu_reset_once_nxt  = 1'b1;
            // Once min time in reset has been reached and 
            // indication FW image has been loaded into MCU SRAM
            // visa the region_lock signal. Bring MCU out of reset
            if(min_mcu_rst_count_elapsed && mcu_sram_fw_exec_region_lock) begin
                boot_fsm_nxt  = BOOT_MCU;
            end
        end
        default: begin
            // Unexpected state so set state to X
            boot_fsm_nxt = BOOT_UNKNOWN;
        end
    endcase
end


// Min MCU reset count
always_comb begin
    min_mcu_rst_count_elapsed_nxt = min_mcu_rst_count_elapsed;
    min_mcu_rst_count_nxt = min_mcu_rst_count;
    // When entering BOOT_RST_MCU state reset count and flag
    if(boot_fsm_nxt == BOOT_RST_MCU && boot_fsm != BOOT_RST_MCU) begin
        min_mcu_rst_count_elapsed_nxt = '0;
        min_mcu_rst_count_nxt = '0;
    end
    // While in BOOT_RST_MCU count until we are about to overflow the counter.
    else if(boot_fsm == BOOT_RST_MCU && min_mcu_rst_count != '1) begin
        min_mcu_rst_count_nxt = min_mcu_rst_count + 1'b1;
    end
    // Once timeout has been reached set the elapsed timer
    else if(boot_fsm == BOOT_RST_MCU && min_mcu_rst_count != '1) begin
        min_mcu_rst_count_elapsed_nxt = 1'b1;
    end
end

endmodule
