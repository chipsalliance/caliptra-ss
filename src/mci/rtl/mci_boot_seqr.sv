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

`include "caliptra_prim_assert.sv"
`include "caliptra_sva.svh"

module mci_boot_seqr
import mci_pkg::*;
#(
    parameter MIN_MCU_RST_COUNTER_WIDTH = 4 // Determines the minimum time MCU is in reset 
)
(
    input logic clk,
    input logic mci_rst_b,
    input logic mci_pwrgood,

    // Clock Controls
    output logic rdc_clk_dis,
    output logic fw_update_rdc_clk_dis,

    // DFT
    input scan_mode,

    // Reset controls
    output logic cptra_ss_rst_b_o,
    output logic mcu_rst_b,
    output logic cptra_rst_b,
    output logic early_warm_reset_warn,

    // MCU Halt Signals
    output logic mcu_cpu_halt_req_o,
    input  logic mcu_cpu_halt_ack_i,
    input  logic mcu_cpu_halt_status_i,

    // Internal signals
    input  logic caliptra_boot_go,
    input  logic mci_bootfsm_go,
    input  logic mcu_rst_req,
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

logic lc_init_nxt;

logic fc_opt_init_nxt;

logic mci_boot_seq_brkpoint_sync;
logic mcu_cpu_halt_ack_i_sync;
logic mcu_cpu_halt_status_i_sync;

logic mcu_no_rom_config_sync;

logic mcu_rst_b_ff  ;
logic cptra_rst_b_ff;
logic cptra_ss_rst_b_o_ff;
logic mcu_rst_b_nxt;
logic cptra_rst_b_nxt;
logic cptra_ss_rst_b_o_nxt;

logic mci_rst_window;
logic mci_rst_window_sync;
logic mci_rst_window_sync_f;
logic mci_rst_window_sync_2f;
logic fw_update_rst_window;
logic warm_reset;

logic mcu_reset_once_nxt;

logic mcu_cpu_halt_req_nxt;
logic [MIN_MCU_RST_COUNTER_WIDTH-1:0] min_mcu_rst_count;
logic [MIN_MCU_RST_COUNTER_WIDTH-1:0] min_mcu_rst_count_nxt;
logic min_mcu_rst_count_elapsed;
logic min_mcu_rst_count_elapsed_nxt;
        
/////////////////////////////////////////////////
// DFT                                 
/////////////////////////////////////////////////
assign cptra_ss_rst_b_o   = scan_mode ? mci_rst_b           :  cptra_ss_rst_b_o_ff;
assign mcu_rst_b          = scan_mode ? mci_rst_b           :  mcu_rst_b_ff;
assign cptra_rst_b        = scan_mode ? mci_rst_b           :  cptra_rst_b_ff;

/////////////////////////////////////////////////
// Reset Window                        
/////////////////////////////////////////////////

//uC reset generation
always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mci_rst_window <= '1;
    end
    else begin
        mci_rst_window <= 0;
    end
end

caliptra_2ff_sync #(.WIDTH(1), .RST_VAL('d1)) i_rst_window_sync (.clk(clk), .rst_b(mci_pwrgood), .din(mci_rst_window), .       dout(mci_rst_window_sync));


always_ff @(posedge clk or negedge mci_pwrgood) begin
    if(~mci_pwrgood) begin
        mci_rst_window_sync_f <= '1;
        mci_rst_window_sync_2f <= '1;
    end 
    else begin

        mci_rst_window_sync_f  <= mci_rst_window_sync;
        mci_rst_window_sync_2f <= mci_rst_window_sync_f;

    end
end

// Used to synchronously change signals to a safe value that feed
// into different reset domains that can't have their 
// clocks gated, such as Caliptra core/noncore domains.
assign early_warm_reset_warn = mci_rst_window_sync;

//clock gate all flops on warm reset to prevent RDC metastability issues
// Delay by 2 clock cycles to allow some signal sync transition to safe value
always_comb rdc_clk_dis = mci_rst_window_sync_2f;

// Delay by 2 clock cycles to allow some signal sync transition to safe value
assign warm_reset = mci_rst_window_sync_2f;




assign fw_update_rst_window = (boot_fsm_nxt == BOOT_RST_MCU) || (boot_fsm == BOOT_RST_MCU); 

//clock gate all flops on MCU FW update
assign fw_update_rdc_clk_dis = fw_update_rst_window; 

/////////////////////////////////////////////////
// Sync signals into local clock domain
/////////////////////////////////////////////////
caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mci_boot_seq_brkpoint (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(mci_boot_seq_brkpoint),
  .q_o(mci_boot_seq_brkpoint_sync));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_no_rom_config (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(mcu_no_rom_config),
  .q_o(mcu_no_rom_config_sync));


caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_cpu_halt_ack_i (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(mcu_cpu_halt_ack_i),
  .q_o(mcu_cpu_halt_ack_i_sync));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_cpu_halt_status_i (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(mcu_cpu_halt_status_i),
  .q_o(mcu_cpu_halt_status_i_sync));


/////////////////////////////////////////////////
// Boot FSM
/////////////////////////////////////////////////
always_ff @(posedge clk or negedge mci_pwrgood) begin
    if(!mci_pwrgood) begin
        boot_fsm                    <= BOOT_IDLE;
        boot_fsm_prev               <= BOOT_IDLE;
        fc_opt_init                 <= '0;
        lc_init                     <= '0;
        cptra_ss_rst_b_o_ff         <= '0;
        mcu_rst_b_ff                <= '0;
        cptra_rst_b_ff              <= '0;
        mcu_reset_once              <= '0;
        min_mcu_rst_count_elapsed   <= '0;
        min_mcu_rst_count           <= '0;
    end
    else begin
        boot_fsm                    <= warm_reset ? BOOT_IDLE : boot_fsm_nxt;
        boot_fsm_prev               <= (boot_fsm != boot_fsm_nxt) ? boot_fsm : boot_fsm_prev; // Capture where FSM came from
        fc_opt_init                 <= fc_opt_init_nxt;
        lc_init                     <= lc_init_nxt;
        cptra_ss_rst_b_o_ff         <= cptra_ss_rst_b_o_nxt;
        mcu_rst_b_ff                <= mcu_rst_b_nxt;
        cptra_rst_b_ff              <= cptra_rst_b_nxt;
        mcu_reset_once              <= mcu_reset_once_nxt;
        min_mcu_rst_count_elapsed   <= min_mcu_rst_count_elapsed_nxt;
        min_mcu_rst_count           <= min_mcu_rst_count_nxt;
    end
end


always_comb begin
    boot_fsm_nxt            = boot_fsm;
    fc_opt_init_nxt         = fc_opt_init;
    lc_init_nxt             = lc_init;
    cptra_ss_rst_b_o_nxt    = cptra_ss_rst_b_o_ff;
    mcu_rst_b_nxt           = mcu_rst_b_ff;
    cptra_rst_b_nxt         = cptra_rst_b_ff;
    mcu_reset_once_nxt      = mcu_reset_once;
    mcu_cpu_halt_req_nxt    = 1'b0;
    unique case(boot_fsm)
        BOOT_IDLE: begin
            // Can only transition into IDLE on MCI reset
            // If this changes we need to add init signal values
            // for FC, LCC, MCU, CPTRA
            boot_fsm_nxt = BOOT_OTP_FC; 
            cptra_ss_rst_b_o_nxt    = 1'b0;
            mcu_rst_b_nxt           = 1'b0;
            cptra_rst_b_nxt         = 1'b0;
        end
        BOOT_OTP_FC: begin
            cptra_ss_rst_b_o_nxt    = 1'b1;
            fc_opt_init_nxt = 1'b1;
            if (fc_opt_done) begin
                boot_fsm_nxt = BOOT_LCC; 
            end
        end
        BOOT_LCC: begin
            lc_init_nxt = 1'b1;
            if(lc_done) begin
                boot_fsm_nxt = BOOT_BREAKPOINT_CHECK;
            end
        end
        BOOT_BREAKPOINT_CHECK: begin
            if(mci_boot_seq_brkpoint_sync) begin 
                boot_fsm_nxt = BOOT_BREAKPOINT;
            end
            else if (mcu_no_rom_config_sync) begin
                boot_fsm_nxt = BOOT_WAIT_CPTRA_GO;
            end
            else begin
                boot_fsm_nxt = BOOT_MCU;
            end
        end
        BOOT_BREAKPOINT: begin
            if (mci_bootfsm_go) begin
                if (mcu_no_rom_config_sync) begin
                    boot_fsm_nxt = BOOT_WAIT_CPTRA_GO;
                end
                else begin
                    boot_fsm_nxt = BOOT_MCU;
                end
            end
        end
        BOOT_MCU: begin
            if (boot_fsm_prev == BOOT_RST_MCU) begin
                boot_fsm_nxt = BOOT_WAIT_MCU_RST_REQ;
            end
            else begin 
                boot_fsm_nxt = BOOT_WAIT_CPTRA_GO;
            end
            mcu_rst_b_nxt = 1'b1;
        end
        BOOT_WAIT_CPTRA_GO: begin
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
                boot_fsm_nxt        = BOOT_HALT_MCU;
            end
        end
        BOOT_HALT_MCU: begin
            if(mcu_cpu_halt_ack_i_sync) begin
                boot_fsm_nxt        = BOOT_WAIT_MCU_HALTED;
            end
            mcu_cpu_halt_req_nxt = 1'b1;
        end
        BOOT_WAIT_MCU_HALTED: begin
            if (mcu_cpu_halt_status_i_sync) begin
                boot_fsm_nxt        = BOOT_RST_MCU;
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

always_ff@(posedge clk or negedge mci_pwrgood) begin
    if (!mci_pwrgood) begin
        mcu_cpu_halt_req_o <= 1'b0;
    end
    else begin
        mcu_cpu_halt_req_o <= mcu_cpu_halt_req_nxt;
    end
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
    else if(boot_fsm == BOOT_RST_MCU && min_mcu_rst_count == '1) begin
        min_mcu_rst_count_elapsed_nxt = 1'b1;
    end
end


//////////////////////////////////////
// ASSERTIONS
//////////////////////////////////////

// Counter must be a valid width. Meaning greater than 0
`CALIPTRA_ASSERT_INIT(ERR_MIN_MCU_RST_COUNTER_WIDTH,  MIN_MCU_RST_COUNTER_WIDTH > 0)

// If falling into default state the boot_fsm will value will be X
`CALIPTRA_ASSERT_KNOWN(ERR_MCI_BOOT_SEQR_VALID_STATE, boot_fsm, clk, !mci_rst_b)

endmodule
