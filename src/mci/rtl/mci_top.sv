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


module mci_top 
    import mci_reg_pkg::*;
    import mci_pkg::*;
    import mci_dmi_pkg::*;
    import mci_mcu_trace_buffer_pkg::*;
    #(    
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_USER_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 8,

    parameter MCU_SRAM_SIZE_KB = 512, 
                                      

    parameter MIN_MCU_RST_COUNTER_WIDTH = 4 // Size of MCU reset counter that overflows before allowing MCU
                                            // to come out of reset during a FW RT Update

    //Mailbox configuration
    ,parameter MCU_MBOX0_SIZE_KB = 128
    ,parameter [4:0] SET_MCU_MBOX0_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCU_MBOX0_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
    ,parameter MCU_MBOX1_SIZE_KB = 4
    ,parameter [4:0] SET_MCU_MBOX1_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCU_MBOX1_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}

    )
    (
    input logic clk,
    output logic mcu_clk_cg, // Gated when MCU reset or warm reset
    output logic cptra_ss_rdc_clk_cg, // Gated during warm reset. 

    // Resets
    input logic mci_rst_b,
    input logic mci_pwrgood,
    output logic cptra_ss_rst_b_o,

    // DFT
    input scan_mode,

    // MCI AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,
    
    
    // Straps
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_lsu_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_ifu_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_sram_config_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mci_soc_config_axi_user,
    input logic ss_debug_intent,

    // SRAM ADHOC connections
    input logic mcu_sram_fw_exec_region_lock,

    // SS error signals
    input logic [31:0] agg_error_fatal,
    input logic [31:0] agg_error_non_fatal,

    // SOC Interrupts
    output logic all_error_fatal,
    output logic all_error_non_fatal,
    
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

    // MCU Halt Signals
    output logic mcu_cpu_halt_req_o,
    input  logic mcu_cpu_halt_ack_i,
    input  logic mcu_cpu_halt_status_i,

    // NMI Vector 
    output logic nmi_intr,
    output logic [31:0] mcu_nmi_vector,

    // MCU DMI
    output logic        mcu_dmi_core_enable,
    output logic        mcu_dmi_uncore_enable,
    input  logic        mcu_dmi_uncore_en,
    input  logic        mcu_dmi_uncore_wr_en,
    input  logic [ 6:0] mcu_dmi_uncore_addr,
    input  logic [31:0] mcu_dmi_uncore_wdata,
    output logic [31:0] mcu_dmi_uncore_rdata,
    input  logic        mcu_dmi_active, // Unused - only use if we start using functional CG

    // MCU Trace
    input logic [31:0] mcu_trace_rv_i_insn_ip,
    input logic [31:0] mcu_trace_rv_i_address_ip,
    input logic        mcu_trace_rv_i_valid_ip,
    input logic        mcu_trace_rv_i_exception_ip,
    input logic [ 4:0] mcu_trace_rv_i_ecause_ip,
    input logic        mcu_trace_rv_i_interrupt_ip,
    input logic [31:0] mcu_trace_rv_i_tval_ip,

    // Caliptra MBOX
    input logic cptra_mbox_data_avail,

    // MBOX
    output logic soc_mcu_mbox0_data_avail,
    output logic soc_mcu_mbox1_data_avail,

    
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

    input  logic  FIPS_ZEROIZATION_PPD_i,
    output logic  FIPS_ZEROIZATION_CMD_o,

    input logic intr_otp_operation_done,


    // MCU SRAM Interface
    mci_mcu_sram_if.request mci_mcu_sram_req_if,

    // Mbox0 SRAM Interface
    mci_mcu_sram_if.request mcu_mbox0_sram_req_if,

    // Mbox1 SRAM Interface
    mci_mcu_sram_if.request mcu_mbox1_sram_req_if,


    //=============== LCC GASKET PORTS ========================

    // Inputs from LCC
    input  otp_ctrl_pkg::lc_otp_program_req_t           from_lcc_to_otp_program_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_dft_en_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_hw_debug_en_i,
    input                                               lc_fatal_state_error_i,
    // Inputs from OTP_Ctrl
    input  otp_ctrl_pkg::otp_lc_data_t                  from_otp_to_lcc_program_i,
    // Inputs from Caliptra_Core
    input logic                                         ss_dbg_manuf_enable_i,    
    input logic [63:0]                                  ss_soc_dbg_unlock_level_i,

    // Converted Signals from LCC 
    output  logic                                       SOC_DFT_EN,
    output 	logic                                       SOC_HW_DEBUG_EN,

    output soc_ifc_pkg::security_state_t                security_state_o

    //============================================================

    );

    
    mci_reg__out_t mci_reg_hwif_out;

    // MCU SRAM signals
    logic        mcu_sram_single_ecc_error;
    logic        mcu_sram_double_ecc_error;
    logic        mcu_sram_fw_exec_region_lock_sync;
    logic        mcu_sram_fw_exec_region_lock_internal;
    logic        mcu_sram_fw_exec_region_lock_dmi_override;
    logic        mcu_sram_dmi_axi_collision_error;
    logic        mcu_sram_dmi_uncore_en;
    logic        mcu_sram_dmi_uncore_wr_en;
    logic [ 6:0] mcu_sram_dmi_uncore_addr;
    logic [31:0] mcu_sram_dmi_uncore_wdata;
    logic [31:0] mcu_sram_dmi_uncore_rdata;

    // MCU Trace Buffer signals
    logic         mcu_trace_buffer_dmi_reg_wen;
    logic [31:0]  mcu_trace_buffer_dmi_reg_wdata;
    logic [6:0]   mcu_trace_buffer_dmi_reg_addr;
    mci_mcu_trace_buffer_dmi_reg_t mcu_trace_buffer_dmi_reg;

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
    logic axi_mci_soc_config_req;
    logic axi_mcu_lsu_req;
    logic axi_mcu_ifu_req;
    logic axi_mcu_req    ;
    logic axi_mcu_sram_config_req    ;
    logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox0_users;
    logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox1_users;

    // Boot Sequencer
    logic mcu_reset_once;
    mci_boot_fsm_state_e boot_fsm;

    // MBOX
    logic mbox0_sram_single_ecc_error;
    logic mbox0_sram_double_ecc_error;
    logic mbox1_sram_single_ecc_error;
    logic mbox1_sram_double_ecc_error;
    logic mcu_mbox0_data_avail;
    logic mcu_mbox1_data_avail;
    logic mcu_mbox0_target_user_done;
    logic mcu_mbox1_target_user_done;
    logic soc_req_mbox0_lock;
    logic soc_req_mbox1_lock;

    // Other
    logic mci_ss_debug_intent;

    // RDC

    logic rdc_clk_dis;
    logic fw_update_rdc_clk_dis;



// Clock gating only using RDC clock gating functionality
clk_gate cg ( 
    .clk(clk),
    .cptra_rst_b(cptra_ss_rst_b_o),
    .psel('0),
    .clk_gate_en('0),
    .cpu_halt_status('0),
    .rdc_clk_dis(rdc_clk_dis),
    .rdc_clk_dis_uc (fw_update_rdc_clk_dis),
    .clk_cg (),
    .soc_ifc_clk_cg (),
    .rdc_clk_cg (cptra_ss_rdc_clk_cg),
    .uc_clk_cg (mcu_clk_cg),
    .generic_input_wires('0),
    .cptra_error_fatal('0),
    .cptra_in_debug_scan_mode('0),
    .cptra_dmi_reg_en_preQ('0)
);

// Caliptra internal fabric interface for MCU SRAM 
// Address width is set to AXI_ADDR_WIDTH and MCU SRAM
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mcu_sram_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));

// Caliptra internal fabric interface for MCI REG 
// Address width is set to AXI_ADDR_WIDTH and MCI REG
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mci_reg_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));

// Caliptra internal fabric interface for TRACE BUFFER
// Address width is set to AXI_ADDR_WIDTH and MCI REG
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mcu_trace_buffer_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));

caliptra_prim_flop_2sync #(
  .Width(1)
) u_prim_flop_2sync_mcu_sram_fw_exec_region_lock (
  .clk_i(clk),
  .rst_ni(cptra_ss_rst_b_o),
  .d_i(mcu_sram_fw_exec_region_lock),
  .q_o(mcu_sram_fw_exec_region_lock_sync));

assign mcu_sram_fw_exec_region_lock_internal = mcu_sram_fw_exec_region_lock_dmi_override | mcu_sram_fw_exec_region_lock_sync;
  
// Caliptra internal fabric interface for MCI Mbox0
// Address width is set to AXI_ADDR_WIDTH and Mbox0
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mcu_mbox0_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));

// Caliptra internal fabric interface for MCI Mbox0
// Address width is set to AXI_ADDR_WIDTH and Mbox0
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mcu_mbox1_req_if(
    .clk(cptra_ss_rdc_clk_cg), 
    .rst_b(cptra_ss_rst_b_o));

//AXI Interface
//This module contains the logic for interfacing with the SoC over the AXI Interface
//The SoC sends read and write requests using AXI Protocol
//This wrapper decodes that protocol, collapses the full-duplex protocol to
// simplex, and issues requests to the MIC decode block
mci_axi_sub_top #( 
    .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH), 
    .AXI_DATA_WIDTH(AXI_DATA_WIDTH), 
    .AXI_ID_WIDTH(AXI_ID_WIDTH),
    .AXI_USER_WIDTH(AXI_USER_WIDTH),
    .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB)
) i_mci_axi_sub_top (
    // MCI clk
    .clk  (cptra_ss_rdc_clk_cg), 

    // MCI Resets
    .rst_b(cptra_ss_rst_b_o), 

    // AXI INF
    .s_axi_w_if(s_axi_w_if),
    .s_axi_r_if(s_axi_r_if),

    // MCI REG Interface
    .mci_reg_req_if( mci_reg_req_if.request ),

    // MCU SRAM Interface
    .mcu_sram_req_if( mcu_sram_req_if.request ),

    // MCU TRACE BUFFER Interface
    .mcu_trace_buffer_req_if( mcu_trace_buffer_req_if.request ),

    // MCI Mbox0 Interface
    .mcu_mbox0_req_if ( mcu_mbox0_req_if.request ),

    // MCI Mbox1 Interface
    .mcu_mbox1_req_if ( mcu_mbox1_req_if.request ),

    // Privileged requests 
    .axi_mci_soc_config_req,
    .axi_mcu_lsu_req,
    .axi_mcu_ifu_req,
    .axi_mcu_req    ,
    .axi_mcu_sram_config_req    ,

    
    // Privileged AXI users
    .strap_mci_soc_config_axi_user,
    .strap_mcu_lsu_axi_user,
    .strap_mcu_ifu_axi_user,
    .strap_mcu_sram_config_axi_user
);

mci_boot_seqr #(
    .MIN_MCU_RST_COUNTER_WIDTH(MIN_MCU_RST_COUNTER_WIDTH)
)i_boot_seqr (
    .clk,
    .mci_rst_b, 
    .mci_pwrgood,

    // Clock Controls
    .rdc_clk_dis,
    .fw_update_rdc_clk_dis,

    // DFT
    .scan_mode,

    // Reset controls
    .cptra_ss_rst_b_o,
    .mcu_rst_b,
    .cptra_rst_b,

    // MCU Halt Signals
    .mcu_cpu_halt_req_o,
    .mcu_cpu_halt_ack_i,
    .mcu_cpu_halt_status_i,

    // Internal signals
    .caliptra_boot_go(mci_reg_hwif_out.CPTRA_BOOT_GO.go),
    .mci_bootfsm_go(mci_reg_hwif_out.MCI_BOOTFSM_GO.go),
    .mcu_rst_req(mci_reg_hwif_out.RESET_REQUEST.mcu_req),
    .mcu_reset_once,
    .boot_fsm,

    // SoC signals
    .mci_boot_seq_brkpoint,
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_internal),
    .mcu_no_rom_config,                // Determines boot sequencer boot flow

    // LCC Signals
    .lc_done,
    .lc_init,

    // FC Signals
    .fc_opt_done,
    .fc_opt_init
);


mci_mcu_trace_buffer #(
    .DMI_REG_TRACE_RD_PTR_ADDR(MCI_DMI_MCU_TRACE_RD_PTR)
) i_mci_mcu_trace_buffer 
    (
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .rst_b(cptra_ss_rst_b_o), 

    .debug_en(!security_state_o.debug_locked),
    
    // DMI Access
    .dmi_reg_wen    (mcu_trace_buffer_dmi_reg_wen  ),
    .dmi_reg_wdata  (mcu_trace_buffer_dmi_reg_wdata),
    .dmi_reg_addr   (mcu_trace_buffer_dmi_reg_addr ),
    .dmi_reg        (mcu_trace_buffer_dmi_reg      ),

    // MCU Trace
    .mcu_trace_rv_i_insn_ip,
    .mcu_trace_rv_i_address_ip,
    .mcu_trace_rv_i_valid_ip,
    .mcu_trace_rv_i_exception_ip,
    .mcu_trace_rv_i_ecause_ip,
    .mcu_trace_rv_i_interrupt_ip,
    .mcu_trace_rv_i_tval_ip,
    
    // Caliptra internal fabric response interface
    .cif_resp_if (mcu_trace_buffer_req_if.response)

);

// MCU SRAM
// Translates requests from the AXI SUB and sends them to the MCU SRAM.
mci_mcu_sram_ctrl #(
    .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB)
) i_mci_mcu_sram_ctrl (
    // MCI clk
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .rst_b (cptra_ss_rst_b_o), 
    .mci_pwrgood (mci_pwrgood), 

    
    // MCU Reset
    .mcu_rst_b,

    // Interface
    .fw_sram_exec_region_size(mci_reg_hwif_out.FW_SRAM_EXEC_REGION_SIZE.size.value), 

    // Caliptra internal fabric response interface
    .cif_resp_if (mcu_sram_req_if.response),
    
    // Debug Mode
    .debug_en(!security_state_o.debug_locked),

    // AXI Privileged requests
    .axi_mcu_lsu_req,
    .axi_mcu_ifu_req,
    .axi_mcu_sram_config_req    ,

    // Access lock interface
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_internal),  
    
    // DMI
    .dmi_uncore_en    (mcu_sram_dmi_uncore_en),
    .dmi_uncore_wr_en (mcu_sram_dmi_uncore_wr_en),
    .dmi_uncore_addr  (mcu_sram_dmi_uncore_addr),
    .dmi_uncore_wdata (mcu_sram_dmi_uncore_wdata),
    .dmi_uncore_rdata (mcu_sram_dmi_uncore_rdata),

    // ECC Status
    .sram_single_ecc_error(mcu_sram_single_ecc_error),  
    .sram_double_ecc_error(mcu_sram_double_ecc_error),  
    .dmi_axi_collision_error(mcu_sram_dmi_axi_collision_error),

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
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .rst_b (cptra_ss_rst_b_o), 

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
mci_reg_top #(
    .AXI_USER_WIDTH(AXI_USER_WIDTH),   
    .SET_MCU_MBOX0_AXI_USER_INTEG(SET_MCU_MBOX0_AXI_USER_INTEG),  
    .MCU_MBOX0_VALID_AXI_USER(MCU_MBOX0_VALID_AXI_USER),   
    .MCU_MBOX0_SIZE_KB(MCU_MBOX0_SIZE_KB),
    .SET_MCU_MBOX1_AXI_USER_INTEG(SET_MCU_MBOX1_AXI_USER_INTEG),  
    .MCU_MBOX1_VALID_AXI_USER(MCU_MBOX1_VALID_AXI_USER),
    .MCU_MBOX1_SIZE_KB(MCU_MBOX1_SIZE_KB)
)i_mci_reg_top (
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .mci_rst_b      (cptra_ss_rst_b_o),    
    .mcu_rst_b      (mcu_rst_b),   
    .cptra_rst_b    (cptra_rst_b), 
    .mci_pwrgood    (mci_pwrgood),

    // REG HWIF signals
    .mci_reg_hwif_out,
    
    // DFT
    .scan_mode,
    
    // AXI Privileged requests
    .axi_mci_soc_config_req,
    .axi_mcu_sram_config_req,
    .axi_mcu_req,

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

    // OTP
    .intr_otp_operation_done,
    
    // Debug intent
    .ss_debug_intent,
    .mci_ss_debug_intent,

    .strap_mcu_lsu_axi_user,
    .strap_mcu_ifu_axi_user,
    .strap_mcu_sram_config_axi_user,
    .strap_mci_soc_config_axi_user,
    
    
    // MCU Reset vector
    .strap_mcu_reset_vector, // default reset vector
    .mcu_reset_vector,       // reset vector used by MCU

    // SS error signals
    .agg_error_fatal,
    .agg_error_non_fatal,
    
    // DMI
    .mcu_dmi_core_enable,
    .mcu_dmi_uncore_enable,
    .mcu_dmi_uncore_en,
    .mcu_dmi_uncore_wr_en,
    .mcu_dmi_uncore_addr,
    .mcu_dmi_uncore_wdata,
    .mcu_dmi_uncore_rdata,

    // MCU Trace
    .mcu_trace_buffer_dmi_reg_wen, 
    .mcu_trace_buffer_dmi_reg_wdata,
    .mcu_trace_buffer_dmi_reg_addr,
    .mcu_trace_buffer_dmi_reg,      
    
    // MBOX
    .valid_mbox0_users,
    .valid_mbox1_users,
    .mcu_mbox0_data_avail,
    .mcu_mbox1_data_avail,
    .mcu_mbox0_target_user_done,
    .mcu_mbox1_target_user_done,
    .cptra_mbox_data_avail,
    .soc_req_mbox0_lock,
    .soc_req_mbox1_lock,
    .mbox0_sram_single_ecc_error,
    .mbox0_sram_double_ecc_error,
    .mbox1_sram_single_ecc_error,
    .mbox1_sram_double_ecc_error,

    // LCC Gasket signals
    .security_state_o,

    // SOC Interrupts
    .all_error_fatal,
    .all_error_non_fatal,
    

    // MCU interrupts
    .mcu_timer_int,
    .mci_intr,

    // NMI
    .nmi_intr,
    .mcu_nmi_vector,
    
    // MISC
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_internal),
    .mcu_sram_fw_exec_region_lock_dmi_override,

    // MCU SRAM specific signals
    .mcu_sram_single_ecc_error,
    .mcu_sram_double_ecc_error,
    .mcu_sram_dmi_axi_collision_error,
    .mcu_sram_dmi_uncore_en,
    .mcu_sram_dmi_uncore_wr_en,
    .mcu_sram_dmi_uncore_addr,
    .mcu_sram_dmi_uncore_wdata,
    .mcu_sram_dmi_uncore_rdata,

    // Boot status
    .mcu_reset_once,
    .boot_fsm,
    
    // Caliptra internal fabric response interface
    .cif_resp_if (mci_reg_req_if.response)

);
generate
if (MCU_MBOX0_SIZE_KB == 0) begin : no_mcu_mbox0
    always_comb begin
        //TIE-OFF zero sized mailbox
        mcu_mbox0_req_if.hold = 0;
        mcu_mbox0_req_if.rdata = 0;
        mcu_mbox0_req_if.error = 1;
        mcu_mbox0_sram_req_if.req = '0;
        mbox0_sram_single_ecc_error = '0;
        mbox0_sram_double_ecc_error = '0;
        soc_req_mbox0_lock = '0;
        soc_mcu_mbox0_data_avail = '0;
        mcu_mbox0_data_avail = '0;
        mcu_mbox0_target_user_done = '0;
    end
end else begin : mcu_mbox0
mcu_mbox
#(
    .MCU_MBOX_SRAM_SIZE_KB(MCU_MBOX0_SIZE_KB)
    ,.DEF_MBOX_VALID_AXI_USER(MCU_DEF_MBOX_VALID_AXI_USER)
)
mcu_mbox0 (
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .rst_b(cptra_ss_rst_b_o), 

    // Caliptra internal fabric response interface
    .cif_resp_if(mcu_mbox0_req_if.response),

    .strap_root_axi_user(strap_mcu_lsu_axi_user),

    // Mailbox valid users. 
    .valid_mbox_users(valid_mbox0_users),

    // Mailbox Status
    .soc_req_mbox_locked(soc_req_mbox0_lock), // SoC user requested lock when root user has lock
    .root_mbox_data_available(soc_mcu_mbox0_data_avail),
    .soc_mbox_data_available(mcu_mbox0_data_avail),
    .target_user_done(mcu_mbox0_target_user_done),

    // Mailbox SRAM ECC error flags
    .sram_single_ecc_error(mbox0_sram_single_ecc_error),
    .sram_double_ecc_error(mbox0_sram_double_ecc_error),

    .mcu_mbox_sram_req_if(mcu_mbox0_sram_req_if)
);
end
endgenerate

generate
if (MCU_MBOX1_SIZE_KB == 0) begin : no_mcu_mbox1
    always_comb begin
        //TIE-OFF zero sized mailbox
        mcu_mbox1_req_if.hold = 0;
        mcu_mbox1_req_if.rdata = 0;
        mcu_mbox1_req_if.error = 1;
        mcu_mbox1_sram_req_if.req = '0;
        mbox1_sram_single_ecc_error = '0;
        mbox1_sram_double_ecc_error = '0;
        soc_req_mbox1_lock = '0;
        soc_mcu_mbox1_data_avail = '0;
        mcu_mbox1_data_avail = '0;
        mcu_mbox1_target_user_done = '0;
    end
end else begin : mcu_mbox1
mcu_mbox
#(
    .MCU_MBOX_SRAM_SIZE_KB(MCU_MBOX1_SIZE_KB)
    ,.DEF_MBOX_VALID_AXI_USER(MCU_DEF_MBOX_VALID_AXI_USER)
)
mcu_mbox1 (
    .clk(cptra_ss_rdc_clk_cg),

    // MCI Resets
    .rst_b(cptra_ss_rst_b_o), 

    // Caliptra internal fabric response interface
    .cif_resp_if(mcu_mbox1_req_if.response),

    .strap_root_axi_user(strap_mcu_lsu_axi_user),

    // Mailbox valid users. 
    .valid_mbox_users(valid_mbox1_users),

    // Mailbox Status
    .soc_req_mbox_locked(soc_req_mbox1_lock), // SoC user requested lock when root user has lock
    .root_mbox_data_available(soc_mcu_mbox1_data_avail),
    .soc_mbox_data_available(mcu_mbox1_data_avail),
    .target_user_done(mcu_mbox1_target_user_done),

    // Mailbox SRAM ECC error flags
    .sram_single_ecc_error(mbox1_sram_single_ecc_error),
    .sram_double_ecc_error(mbox1_sram_double_ecc_error),

    .mcu_mbox_sram_req_if(mcu_mbox1_sram_req_if)
);
end
endgenerate



 // DUT instantiation
mci_lcc_st_trans LCC_state_translator (
    .clk_i(cptra_ss_rdc_clk_cg),
    .rst_ni(cptra_ss_rst_b_o),
    .state_error(lc_fatal_state_error_i),  
    .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
    .lc_dft_en_i(lc_dft_en_i),
    .lc_hw_debug_en_i(lc_hw_debug_en_i),
    .from_otp_to_lcc_program_i(from_otp_to_lcc_program_i),
    .ss_dbg_manuf_enable_i(ss_dbg_manuf_enable_i),
    .ss_soc_dbg_unlock_level_i(ss_soc_dbg_unlock_level_i),
    .ss_soc_dft_en_mask_reg0_1({mci_reg_hwif_out.SOC_DFT_EN[1].MASK.value, mci_reg_hwif_out.SOC_DFT_EN[0].MASK.value}), 
    .ss_soc_dbg_unlock_mask_reg0_1({mci_reg_hwif_out.SOC_PROD_DEBUG_STATE[1].MASK.value, mci_reg_hwif_out.SOC_PROD_DEBUG_STATE[0].MASK.value}), 
    .ss_soc_CLTAP_unlock_mask_reg0_1({mci_reg_hwif_out.SOC_HW_DEBUG_EN[1].MASK.value, mci_reg_hwif_out.SOC_HW_DEBUG_EN[0].MASK.value}), 
    .ss_soc_MCU_ROM_zeroization_mask_reg(mci_reg_hwif_out.FC_FIPS_ZEROZATION.MASK.value), 
    .FIPS_ZEROIZATION_PPD_i,
    .FIPS_ZEROIZATION_CMD_o,
    .SOC_DFT_EN(SOC_DFT_EN),
    .SOC_HW_DEBUG_EN(SOC_HW_DEBUG_EN),
    .security_state_o(security_state_o)
);

///////////////////////////////////////
// Assertions
///////////////////////////////////////

`CALIPTRA_ASSERT_MUTEX(ERR_MCI_AXI_AGENT_GRANT_MUTEX, {mci_reg_req_if.dv, mcu_sram_req_if.dv, mcu_trace_buffer_req_if.dv, mcu_mbox0_req_if.dv, mcu_mbox1_req_if.dv}, clk, !cptra_ss_rst_b_o)

// Today we don't support anything other than 32 bits
`CALIPTRA_ASSERT_INIT(ERR_AXI_DATA_WIDTH, AXI_DATA_WIDTH == 32)

// Verify min size of MCU SRAM
`CALIPTRA_ASSERT_INIT(ERR_MCU_SRAM_MIN_SIZE, MCU_SRAM_SIZE_KB >= 4)
// Verify max size of MCU SRAM
`CALIPTRA_ASSERT_INIT(ERR_MCU_SRAM_MAX_SIZE, MCU_SRAM_SIZE_KB <= 2048)
// Verify min size of MBOX0 
`CALIPTRA_ASSERT_INIT(ERR_MCU_MBOX0_MIN_SIZE, MCU_MBOX0_SIZE_KB >= 0)
// Verify max size of MBOX0
`CALIPTRA_ASSERT_INIT(ERR_MCU_MBOX0_MAX_SIZE, MCU_MBOX0_SIZE_KB <= 2048)
// Verify min size of MBOX1 
`CALIPTRA_ASSERT_INIT(ERR_MCU_MBOX1_MIN_SIZE, MCU_MBOX1_SIZE_KB >= 0)
// Verify max size of MBOX1
`CALIPTRA_ASSERT_INIT(ERR_MCU_MBOX1_MAX_SIZE, MCU_MBOX1_SIZE_KB <= 2048)

// AXI SUB W - Verify AXI addr width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_W_ADDR_SIZE_MATCH,  AXI_ADDR_WIDTH == s_axi_w_if.AW)
// AXI SUB W - Veirfy AXI data width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_W_DATA_SIZE_MATCH,  AXI_DATA_WIDTH == s_axi_w_if.DW)
// AXI SUB W - Verify USER ID width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_W_USER_SIZE_MATCH,  AXI_USER_WIDTH == s_axi_w_if.UW)
// AXI SUB W - Verify ID width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_W_ID_SIZE_MATCH,  AXI_ID_WIDTH == s_axi_w_if.IW)

// AXI SUB R - Verify AXI addr width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_R_ADDR_SIZE_MATCH,  AXI_ADDR_WIDTH == s_axi_r_if.AW)
// AXI SUB R - Veirfy AXI data width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_R_DATA_SIZE_MATCH,  AXI_DATA_WIDTH == s_axi_r_if.DW)
// AXI SUB R - Verify USER ID width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_R_USER_SIZE_MATCH,  AXI_USER_WIDTH == s_axi_r_if.UW)
// AXI SUB R - Verify ID width matches
`CALIPTRA_ASSERT_INIT(ERR_MCI_AXI_SUB_R_ID_SIZE_MATCH,  AXI_ID_WIDTH == s_axi_r_if.IW)

// MCU SRAM ECC SB
`CALIPTRA_ASSERT(MCU_SRAM_ECC_SB, $rose(i_mci_mcu_sram_ctrl.ecc_decode.single_ecc_error) |=> i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif0_internal_intr_r.notif_mcu_sram_ecc_cor_sts.value, cptra_ss_rdc_clk_cg, !cptra_ss_rst_b_o) 
`CALIPTRA_ASSERT(MCU_SRAM_ECC_SB_INTR_OUT, $rose(i_mci_mcu_sram_ctrl.ecc_decode.single_ecc_error) && 
                i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif0_intr_en_r.notif_mcu_sram_ecc_cor_en.value && 
                i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.global_intr_en_r.notif_en.value |=>
                ##2 mci_intr, cptra_ss_rdc_clk_cg, !cptra_ss_rst_b_o) 

`CALIPTRA_ASSERT(MCU_SRAM_ECC_DB, $rose(i_mci_mcu_sram_ctrl.ecc_decode.double_ecc_error) |=> i_mci_reg_top.mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_ecc_unc.value, cptra_ss_rdc_clk_cg, !cptra_ss_rst_b_o) 
`CALIPTRA_ASSERT(MCU_SRAM_ECC_DB_ALL_ERR_OUT, $rose(i_mci_mcu_sram_ctrl.ecc_decode.double_ecc_error) && 
                !i_mci_reg_top.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_ecc_unc.value |=> 
                all_error_fatal, cptra_ss_rdc_clk_cg, !cptra_ss_rst_b_o) 

endmodule
