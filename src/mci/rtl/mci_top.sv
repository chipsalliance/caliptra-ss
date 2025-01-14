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

module mci_top 
    import mci_reg_pkg::*;
    import mci_pkg::*;
    #(
    
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_USER_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 8,

    parameter MCU_SRAM_SIZE_KB = 1024, // FIXME - write assertion ensuring this size 
                                      // is compatible with the MCU SRAM IF parameters

    parameter MIN_MCU_RST_COUNTER_WIDTH = 4 // Size of MCU reset counter that overflows before allowing MCU
                                            // to come out of reset during a FW RT Update
    )
    (
    input logic clk,

    // MCI Resets
    input logic mci_rst_b,
    input logic mci_pwrgood,

    // MCI AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,
    
    // Straps
    input logic [s_axi_r_if.UW-1:0] strap_mcu_lsu_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_mcu_ifu_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_clp_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_mcu_reset_access0_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_mcu_rset_access1_user,

    // SRAM ADHOC connections
    input logic mcu_sram_fw_exec_region_lock,

    // SS error signals
    input logic cptra_error_fatal,
    input logic cptra_error_non_fatal,

    // SOC Interrupts
    output logic mci_error_fatal,
    output logic mci_error_non_fatal,
    
    // Generic in/out
    input  logic [63:0] mci_generic_input_wires,
    output logic [63:0] mci_generic_output_wires,
    
    // MCU interrupts
    output logic mcu_timer_int,
    output logic mci_intr,

    // MCU Reset vector
    input  logic [31:0] strap_mcu_reset_vector, // default reset vector
    output logic [31:0] mcu_reset_vector,       // reset vector used by MCU
    input  logic mcu_no_rom_config,                // Determines boot sequencer boot flow

    // NMI Vector 
    output logic nmi_intr,
    output logic [31:0] mcu_nmi_vector,
    
    // Reset controls
    output logic mcu_rst_b,
    output logic cptra_rst_b,

    // SoC signals
    input logic mci_boot_seq_brkpoint,

    // LCC Signals
    input  logic lc_done,
    output logic lc_init,

    // FC Signals
    input  logic fc_opt_done,
    output logic fc_opt_init,


    // MCU SRAM Interface
    mci_mcu_sram_if.request mci_mcu_sram_req_if 

    );

    
    mci_reg__out_t mci_reg_hwif_out;

    // MCU SRAM signals
    logic mcu_sram_single_ecc_error;
    logic mcu_sram_double_ecc_error;
    logic mcu_sram_fw_exec_region_lock_sync;

    // WDT signals
    logic timer1_en;
    logic timer2_en;
    logic timer1_restart;
    logic timer2_restart;
    logic wdt_timer1_timeout_serviced; 
    logic wdt_timer2_timeout_serviced; 
    logic t1_timeout_p;
    logic t2_timeout_p;
    logic t1_timeout;
    logic t2_timeout;
    logic [MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS-1:0][31:0] timer1_timeout_period;
    logic [MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS-1:0][31:0] timer2_timeout_period;

    // AXI SUB Privileged requests
    logic mcu_lsu_req;
    logic mcu_ifu_req;
    logic mcu_req    ;
    logic clp_req    ;
    logic soc_req    ;

    // Boot Sequencer
    logic mcu_reset_once;
    logic fw_boot_upd_reset;     // First MCU reset request
    logic fw_hitless_upd_reset;  // Other MCU reset requests

// Caliptra internal fabric interface for MCU SRAM 
// Address width is set to AXI_ADDR_WIDTH and MCU SRAM
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mcu_sram_req_if(
    .clk, 
    .rst_b(mci_rst_b));

// Caliptra internal fabric interface for MCI REG 
// Address width is set to AXI_ADDR_WIDTH and MCI REG
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mci_reg_req_if(
    .clk, 
    .rst_b(mci_rst_b));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_sram_fw_exec_region_lock (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(mcu_sram_fw_exec_region_lock),
  .q_o(mcu_sram_fw_exec_region_lock_sync));
  

//AXI Interface
//This module contains the logic for interfacing with the SoC over the AXI Interface
//The SoC sends read and write requests using AXI Protocol
//This wrapper decodes that protocol, collapses the full-duplex protocol to
// simplex, and issues requests to the MIC decode block
mci_axi_sub_top #( // FIXME: Should SUB and MAIN be under same AXI_TOP module?
    .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH), 
    .AXI_DATA_WIDTH(AXI_DATA_WIDTH), 
    .AXI_ID_WIDTH(AXI_ID_WIDTH),
    .AXI_USER_WIDTH(AXI_USER_WIDTH),
    .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB),
    .MBOX0_SIZE_KB (4),     // FIXME
    .MBOX1_SIZE_KB  (4)     // FIXME
) i_mci_axi_sub_top (
    // MCI clk
    .clk  (clk     ),

    // MCI Resets
    .rst_b(mci_rst_b), // FIXME: Need to sync reset

    // AXI INF
    .s_axi_w_if(s_axi_w_if),
    .s_axi_r_if(s_axi_r_if),

    // MCI REG Interface
    .mci_reg_req_if( mci_reg_req_if.request ),

    // MCU SRAM Interface
    .mcu_sram_req_if( mcu_sram_req_if.request ),


    // Privileged requests 
    .mcu_lsu_req,
    .mcu_ifu_req,
    .mcu_req    ,
    .clp_req    ,
    .soc_req    ,

    
    // Privileged AXI users
    .strap_mcu_lsu_axi_user,
    .strap_mcu_ifu_axi_user,
    .strap_clp_axi_user
);

mci_boot_seqr #(
    .MIN_MCU_RST_COUNTER_WIDTH(MIN_MCU_RST_COUNTER_WIDTH)
)i_boot_seqr (
    .clk,
    .mci_rst_b,

    // Reset controls
    .mcu_rst_b,
    .cptra_rst_b,

    // Internal signals
    .caliptra_boot_go(mci_reg_hwif_out.CALIPTRA_BOOT_GO.go),
    .mcu_rst_req(mci_reg_hwif_out.RESET_REQUEST.mcu_req),
    .fw_boot_upd_reset,     // First MCU reset request
    .fw_hitless_upd_reset,  // Other MCU reset requests
    .mcu_reset_once,

    // SoC signals
    .mci_boot_seq_brkpoint,
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_sync),
    .mcu_no_rom_config,                // Determines boot sequencer boot flow

    // LCC Signals
    .lc_done,
    .lc_init,

    // FC Signals
    .fc_opt_done,
    .fc_opt_init
);

// MCU SRAM
// Translates requests from the AXI SUB and sends them to the MCU SRAM.
mci_mcu_sram_ctrl #(
    .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB)
) i_mci_mcu_sram_ctrl (
    // MCI clk
    .clk,

    // MCI Resets
    .rst_b (mci_rst_b), // FIXME: Need to sync reset

    
    // MCU Reset
    .mcu_rst_b,

    // Interface
    .fw_sram_exec_region_size(mci_reg_hwif_out.FW_SRAM_EXEC_REGION_SIZE.size.value), 

    // Caliptra internal fabric response interface
    .cif_resp_if (mcu_sram_req_if.response),

    // AXI Privileged requests
    .mcu_lsu_req,
    .mcu_ifu_req,
    .clp_req    ,

    // Access lock interface
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_sync),  

    // ECC Status
    .sram_single_ecc_error(mcu_sram_single_ecc_error),  
    .sram_double_ecc_error(mcu_sram_double_ecc_error),  

    // Interface with SRAM
    .mci_mcu_sram_req_if(mci_mcu_sram_req_if)
);


// MCI WDT

assign timer1_en = mci_reg_hwif_out.WDT_TIMER1_EN.timer1_en.value;
assign timer2_en = mci_reg_hwif_out.WDT_TIMER2_EN.timer2_en.value;
assign timer1_restart = mci_reg_hwif_out.WDT_TIMER1_CTRL.timer1_restart.value;
assign timer2_restart = mci_reg_hwif_out.WDT_TIMER2_CTRL.timer2_restart.value;

for (genvar i = 0; i < MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS; i++) begin
    assign timer1_timeout_period[i] = mci_reg_hwif_out.WDT_TIMER1_TIMEOUT_PERIOD[i].timer1_timeout_period.value;
    assign timer2_timeout_period[i] = mci_reg_hwif_out.WDT_TIMER2_TIMEOUT_PERIOD[i].timer2_timeout_period.value;
end

mci_wdt_top #(
    .WDT_TIMEOUT_PERIOD_NUM_DWORDS(MCI_WDT_TIMEOUT_PERIOD_NUM_DWORDS)
) i_mci_wdt_top (
    .clk,

    // MCI Resets
    .rst_b (mci_rst_b), // FIXME: Need to sync reset

    //Timer inputs
    .timer1_en,
    .timer2_en,
    .timer1_restart,
    .timer2_restart,
    .timer1_timeout_period,
    .timer2_timeout_period,
    //Interrupts
    .wdt_timer1_timeout_serviced, 
    .wdt_timer2_timeout_serviced, 
    //WDT STATUS
    .t1_timeout, 
    .t2_timeout,
    .t1_timeout_p, 
    .t2_timeout_p,
    .fatal_timeout(nmi_intr)
);

// MCI Reg
// MCI CSR bank
mci_reg_top i_mci_reg_top (
    .clk,

    // MCI Resets
    .mci_rst_b      (mci_rst_b),// FIXME: Need to sync reset
    .mcu_rst_b      (mcu_rst_b),// FIXME: Need to sync reset
    .mci_pwrgood    (mci_pwrgood),       // FIXME: Need to sync

    // REG HWIF signals
    .mci_reg_hwif_out,
    
    // AXI Privileged requests
    .clp_req,
    .mcu_req,

    // WDT specific signals
    .wdt_timer1_timeout_serviced, 
    .wdt_timer2_timeout_serviced, 
    .t1_timeout_p,
    .t2_timeout_p,
    .t1_timeout,
    .t2_timeout,
    
    // Generic IN/OUT
    .mci_generic_input_wires,
    .mci_generic_output_wires,
    
    // MCU Reset vector
    .strap_mcu_reset_vector, // default reset vector
    .mcu_reset_vector,       // reset vector used by MCU

    // SS error signals
    .cptra_error_fatal,
    .cptra_error_non_fatal,

    // SOC Interrupts
    .mci_error_fatal,
    .mci_error_non_fatal,
    
    // MCU interrupts
    .mcu_timer_int,
    .mci_intr,

    // NMI
    .nmi_intr,
    .mcu_nmi_vector,
    
    // MISC
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_sync),

    // MCU SRAM specific signals
    .mcu_sram_single_ecc_error,
    .mcu_sram_double_ecc_error,

    // Reset status
    .mcu_reset_once,
    .fw_boot_upd_reset,     // First MCU reset request
    .fw_hitless_upd_reset,  // Other MCU reset requests
    
    // Caliptra internal fabric response interface
    .cif_resp_if (mci_reg_req_if.response)

);



endmodule
