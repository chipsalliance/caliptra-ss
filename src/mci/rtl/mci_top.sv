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
    import mci_dmi_pkg::*;
    import mbox_pkg::*;
    #(    
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_USER_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 8,

    parameter MCU_SRAM_SIZE_KB = 1024, // FIXME - write assertion ensuring this size 
                                      // is compatible with the MCU SRAM IF parameters

    parameter MIN_MCU_RST_COUNTER_WIDTH = 4 // Size of MCU reset counter that overflows before allowing MCU
                                            // to come out of reset during a FW RT Update

    //Mailbox configuration
    ,parameter MCI_MBOX0_SIZE_KB = 4
    ,parameter [4:0] MCI_SET_MBOX0_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCI_MBOX0_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
    ,parameter MCI_MBOX1_SIZE_KB = 4
    ,parameter [4:0] MCI_SET_MBOX1_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCI_MBOX1_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}

    )
    (
    input logic clk,

    // MCI Resets
    input logic mci_rst_b,
    input logic mci_pwrgood,

    // DFT
    input scan_mode,

    // MCI AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,
    
    // AXI Manager INF
    axi_if.w_mgr m_axi_w_if,
    axi_if.r_mgr m_axi_r_if,
    
    // Straps
    input logic [s_axi_r_if.UW-1:0] strap_mcu_lsu_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_mcu_ifu_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_cptra_axi_user,
    input logic [s_axi_r_if.UW-1:0] strap_debug_axi_user,
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
    input  logic        mcu_dmi_active, // FIXME: This is not used in the design
    
    // Reset controls
    output logic mcu_rst_b,
    output logic cptra_rst_b,

    // SoC signals
    input logic mci_boot_seq_brkpoint,

    // LCC Signals
    input  logic lc_done,
    output logic lc_init,

    // MBOX
    output logic mbox0_data_avail,
    output logic mbox1_data_avail,

    // FC Signals
    input  logic fc_opt_done,
    output logic fc_opt_init,


    // MCU SRAM Interface
    mci_mcu_sram_if.request mci_mcu_sram_req_if,

    // Mbox0 SRAM Interface
    mci_mcu_sram_if.request mci_mbox0_sram_req_if,

    // Mbox1 SRAM Interface
    mci_mcu_sram_if.request mci_mbox1_sram_req_if,


    //=============== LCC GASKET PORTS ========================

    // Inputs from LCC
    input  otp_ctrl_pkg::lc_otp_program_req_t           from_lcc_to_otp_program_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_dft_en_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_hw_debug_en_i,
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
    logic        mcu_sram_dmi_axi_collision_error;
    logic        mcu_sram_dmi_uncore_en;
    logic        mcu_sram_dmi_uncore_wr_en;
    logic [ 6:0] mcu_sram_dmi_uncore_addr;
    logic [31:0] mcu_sram_dmi_uncore_wdata;
    logic [31:0] mcu_sram_dmi_uncore_rdata;


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
    logic axi_debug_req;
    logic axi_mcu_lsu_req;
    logic axi_mcu_ifu_req;
    logic axi_mcu_req    ;
    logic axi_cptra_req    ;
    logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox0_users;
    logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox1_users;

    // Boot Sequencer
    logic mcu_reset_once;
    logic fw_boot_upd_reset;     // First MCU reset request
    logic fw_hitless_upd_reset;  // Other MCU reset requests
    mci_boot_fsm_state_e boot_fsm;

    // MBOX
    logic mbox0_sram_single_ecc_error;
    logic mbox0_sram_double_ecc_error;
    logic mbox1_sram_single_ecc_error;
    logic mbox1_sram_double_ecc_error;
    logic mci_mbox0_data_avail;
    logic mci_mbox1_data_avail;
    logic soc_req_mbox0_lock;
    logic soc_req_mbox1_lock;
    mbox_protocol_error_t mbox0_protocol_error;
    mbox_protocol_error_t mbox1_protocol_error;
    logic mbox0_inv_user_p;
    logic mbox1_inv_user_p;

    // Other
    logic mci_ss_debug_intent;

// AIX MANAGER TIEOFFS - FIXME
assign m_axi_w_if.wlast = '0; // FIXME
assign m_axi_w_if.awaddr = '0; // FIXME
assign m_axi_w_if.awburst = '0; // FIXME
assign m_axi_w_if.awsize = '0; // FIXME
assign m_axi_w_if.awlen = '0; // FIXME
assign m_axi_w_if.awuser = '0; // FIXME
assign m_axi_w_if.awid = '0; // FIXME
assign m_axi_w_if.awlock = '0; // FIXME
assign m_axi_w_if.awvalid = '0; // FIXME
assign m_axi_w_if.wdata = '0; // FIXME
assign m_axi_w_if.wstrb = '0; // FIXME
assign m_axi_w_if.wvalid = '0; // FIXME
assign m_axi_w_if.bready = '0; // FIXME
assign m_axi_r_if.araddr = '0; // FIXME
assign m_axi_r_if.arburst = '0; // FIXME
assign m_axi_r_if.arsize = '0; // FIXME
assign m_axi_r_if.arlen = '0; // FIXME
assign m_axi_r_if.aruser = '0; // FIXME
assign m_axi_r_if.arid = '0; // FIXME
assign m_axi_r_if.arlock = '0; // FIXME
assign m_axi_r_if.arvalid = '0; // FIXME
assign m_axi_r_if.rready = '0; // FIXME
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
  
// Caliptra internal fabric interface for MCI Mbox0
// Address width is set to AXI_ADDR_WIDTH and Mbox0
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mci_mbox0_req_if(
    .clk, 
    .rst_b(mci_rst_b));

// Caliptra internal fabric interface for MCI Mbox0
// Address width is set to AXI_ADDR_WIDTH and Mbox0
// will mask out upper bits that are "don't care"
cif_if #(
    .ADDR_WIDTH(AXI_ADDR_WIDTH)
    ,.DATA_WIDTH(AXI_DATA_WIDTH)
    ,.ID_WIDTH(AXI_ID_WIDTH)
    ,.USER_WIDTH(AXI_USER_WIDTH)
) mci_mbox1_req_if(
    .clk, 
    .rst_b(mci_rst_b));

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

    // MCI Mbox0 Interface
    .mci_mbox0_req_if ( mci_mbox0_req_if.request ),
    .valid_mbox0_users,

    // MCI Mbox1 Interface
    .mci_mbox1_req_if ( mci_mbox1_req_if.request ),
    .valid_mbox1_users,

    // Privileged requests 
    .axi_debug_req,
    .axi_mcu_lsu_req,
    .axi_mcu_ifu_req,
    .axi_mcu_req    ,
    .axi_cptra_req    ,

    
    // Privileged AXI users
    .strap_debug_axi_user,
    .strap_mcu_lsu_axi_user,
    .strap_mcu_ifu_axi_user,
    .strap_cptra_axi_user
);

mci_boot_seqr #(
    .MIN_MCU_RST_COUNTER_WIDTH(MIN_MCU_RST_COUNTER_WIDTH)
)i_boot_seqr (
    .clk,
    .mci_rst_b, // FIXME RDC?

    // DFT
    .scan_mode,

    // Reset controls
    .mcu_rst_b,
    .cptra_rst_b,

    // Internal signals
    .caliptra_boot_go(mci_reg_hwif_out.MCI_BOOTFSM_GO.go),
    .mcu_rst_req(mci_reg_hwif_out.RESET_REQUEST.mcu_req),
    .fw_boot_upd_reset,     // First MCU reset request
    .fw_hitless_upd_reset,  // Other MCU reset requests
    .mcu_reset_once,
    .boot_fsm,

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
    .mci_pwrgood (mci_pwrgood), // FIXME: Need to sync reset

    
    // MCU Reset
    .mcu_rst_b,

    // Interface
    .fw_sram_exec_region_size(mci_reg_hwif_out.FW_SRAM_EXEC_REGION_SIZE.size.value), 

    // Caliptra internal fabric response interface
    .cif_resp_if (mcu_sram_req_if.response),

    // AXI Privileged requests
    .axi_debug_req,
    .axi_mcu_lsu_req,
    .axi_mcu_ifu_req,
    .axi_cptra_req    ,

    // Access lock interface
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_sync),  
    
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
mci_reg_top #(
    .AXI_USER_WIDTH(AXI_USER_WIDTH),   
    .MCI_SET_MBOX0_AXI_USER_INTEG(MCI_SET_MBOX0_AXI_USER_INTEG),  
    .MCI_MBOX0_VALID_AXI_USER(MCI_MBOX0_VALID_AXI_USER),    
    .MCI_SET_MBOX1_AXI_USER_INTEG(MCI_SET_MBOX1_AXI_USER_INTEG),  
    .MCI_MBOX1_VALID_AXI_USER(MCI_MBOX1_VALID_AXI_USER)    
)i_mci_reg_top (
    .clk,

    // MCI Resets
    .mci_rst_b      (mci_rst_b),    // FIXME: Need to sync reset
    .mcu_rst_b      (mcu_rst_b),    // FIXME: Need to sync reset
    .cptra_rst_b    (cptra_rst_b),  // FIXME: Need to sync reset
    .mci_pwrgood    (mci_pwrgood),  // FIXME: Need to sync

    // REG HWIF signals
    .mci_reg_hwif_out,
    
    // AXI Privileged requests
    .axi_debug_req,
    .axi_cptra_req,
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
    
    // Debug intent
    .ss_debug_intent,
    .mci_ss_debug_intent,
    
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
    
    // MBOX
    .valid_mbox0_users,
    .valid_mbox1_users,
    .mci_mbox0_data_avail,
    .mci_mbox1_data_avail,
    .soc_req_mbox0_lock,
    .soc_req_mbox1_lock,
    .mbox0_protocol_error, 
    .mbox1_protocol_error, 
    .mbox0_inv_user_p,
    .mbox1_inv_user_p,
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
    .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock_sync),

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
    .fw_boot_upd_reset,     // First MCU reset request
    .fw_hitless_upd_reset,  // Other MCU reset requests
    .boot_fsm,
    
    // Caliptra internal fabric response interface
    .cif_resp_if (mci_reg_req_if.response)

);
generate
if (MCI_MBOX0_SIZE_KB == 0) begin
    always_comb begin
        //TIE-OFF zero sized mailbox
        mci_mbox0_req_if.hold = 0;
        mci_mbox0_req_if.rdata = 0;
        mci_mbox0_req_if.error = 1;
        mci_mbox0_sram_req_if.req.cs = 0;
        mci_mbox0_sram_req_if.req.we = 0;
        mci_mbox0_sram_req_if.req.addr = 0;
        mci_mbox0_sram_req_if.req.wdata = 0;
        mbox0_sram_single_ecc_error = 0;
        mbox0_sram_double_ecc_error = 0;
    end
end else begin
mbox
#(
    .DMI_REG_MBOX_DLEN_ADDR(MCI_DMI_REG_MBOX0_DLEN),
    .MBOX_SIZE_KB(MCI_MBOX0_SIZE_KB),
    .MBOX_DATA_W(MCI_MBOX_DATA_W),
    .MBOX_ECC_DATA_W(MCI_MBOX_ECC_DATA_W),
    .MBOX_IFC_DATA_W(AXI_DATA_WIDTH),
    .MBOX_IFC_USER_W(AXI_USER_WIDTH),
    .MBOX_IFC_ADDR_W(AXI_ADDR_WIDTH)
)
mci_mbox0_i (
    .clk(clk),
    .rst_b(mci_rst_b),
    //mailbox request interface
    .req_dv(mci_mbox0_req_if.dv), 
    .req_hold(mci_mbox0_req_if.hold),
    .req_data_addr(mci_mbox0_req_if.req_data.addr),
    .req_data_wdata(mci_mbox0_req_if.req_data.wdata),
    .req_data_user(mci_mbox0_req_if.req_data.user),
    .req_data_write(mci_mbox0_req_if.req_data.write),
    .req_data_soc_req(~axi_mcu_req),
    .rdata(mci_mbox0_req_if.rdata),
    .mbox_error(mci_mbox0_req_if.error),
    .mbox_sram_req_cs(mci_mbox0_sram_req_if.req.cs),
    .mbox_sram_req_we(mci_mbox0_sram_req_if.req.we), 
    .mbox_sram_req_addr(mci_mbox0_sram_req_if.req.addr),
    .mbox_sram_req_ecc(mci_mbox0_sram_req_if.req.wdata.ecc),
    .mbox_sram_req_wdata(mci_mbox0_sram_req_if.req.wdata.data),
    .mbox_sram_resp_ecc(mci_mbox0_sram_req_if.resp.rdata.ecc),
    .mbox_sram_resp_data(mci_mbox0_sram_req_if.resp.rdata.data),
    .sram_single_ecc_error(mbox0_sram_single_ecc_error),
    .sram_double_ecc_error(mbox0_sram_double_ecc_error),
    //status
    .uc_mbox_lock(), //FIXME
    //interrupts
    .soc_mbox_data_avail(mbox0_data_avail), 
    .uc_mbox_data_avail(mci_mbox0_data_avail), 
    .soc_req_mbox_lock(soc_req_mbox0_lock),
    .mbox_protocol_error(mbox0_protocol_error),
    .mbox_inv_axi_user_axs(mbox0_inv_user_p), 
    //direct request unsupported
    .dir_req_dv(1'b0),
    .dir_rdata(),
    //sha accelerator unsupported
    .sha_sram_req_dv('0),
    .sha_sram_req_addr('0),
    .sha_sram_resp_ecc(),
    .sha_sram_resp_data(),
    .sha_sram_hold(),
    //FIXME dma
    .dma_sram_req_dv  ('0),
    .dma_sram_req_write('0),
    .dma_sram_req_addr('0),
    .dma_sram_req_wdata('0),
    .dma_sram_rdata   (),
    .dma_sram_hold    (),
    .dma_sram_error   (),
    //dmi port unused
    .dmi_inc_rdptr('0),
    .dmi_inc_wrptr('0),
    .dmi_reg_wen('0),
    .dmi_reg_addr('0),
    .dmi_reg_wdata('0),
    .dmi_reg()
);
end
endgenerate

generate
if (MCI_MBOX1_SIZE_KB == 0) begin
    always_comb begin
        //TIE-OFF zero sized mailbox
        mci_mbox1_req_if.hold = 0;
        mci_mbox1_req_if.rdata = 0;
        mci_mbox1_req_if.error = 1;
        mci_mbox1_sram_req_if.req.cs = 0;
        mci_mbox1_sram_req_if.req.we = 0;
        mci_mbox1_sram_req_if.req.addr = 0;
        mci_mbox1_sram_req_if.req.wdata = 0;
        mbox1_sram_single_ecc_error = 0;
        mbox1_sram_double_ecc_error = 0;
    end
end else begin
mbox
#(
    .DMI_REG_MBOX_DLEN_ADDR(MCI_DMI_REG_MBOX1_DLEN),
    .MBOX_SIZE_KB(MCI_MBOX1_SIZE_KB),
    .MBOX_DATA_W(MCI_MBOX_DATA_W),
    .MBOX_ECC_DATA_W(MCI_MBOX_ECC_DATA_W),
    .MBOX_IFC_DATA_W(AXI_DATA_WIDTH),
    .MBOX_IFC_USER_W(AXI_USER_WIDTH),
    .MBOX_IFC_ADDR_W(AXI_ADDR_WIDTH)
)
mci_mbox1_i (
    .clk(clk),
    .rst_b(mci_rst_b),
    //mailbox request interface
    .req_dv(mci_mbox1_req_if.dv), 
    .req_hold(mci_mbox1_req_if.hold),
    .req_data_addr(mci_mbox1_req_if.req_data.addr),
    .req_data_wdata(mci_mbox1_req_if.req_data.wdata),
    .req_data_user(mci_mbox1_req_if.req_data.user),
    .req_data_write(mci_mbox1_req_if.req_data.write),
    .req_data_soc_req(~axi_mcu_req),
    .rdata(mci_mbox1_req_if.rdata),
    .mbox_error(mci_mbox1_req_if.error),
    .mbox_sram_req_cs(mci_mbox1_sram_req_if.req.cs),
    .mbox_sram_req_we(mci_mbox1_sram_req_if.req.we), 
    .mbox_sram_req_addr(mci_mbox1_sram_req_if.req.addr),
    .mbox_sram_req_ecc(mci_mbox1_sram_req_if.req.wdata.ecc),
    .mbox_sram_req_wdata(mci_mbox1_sram_req_if.req.wdata.data),
    .mbox_sram_resp_ecc(mci_mbox1_sram_req_if.resp.rdata.ecc),
    .mbox_sram_resp_data(mci_mbox1_sram_req_if.resp.rdata.data),
    .sram_single_ecc_error(mbox1_sram_single_ecc_error),
    .sram_double_ecc_error(mbox1_sram_double_ecc_error),
    //status
    .uc_mbox_lock(), //FIXME
    //interrupts
    .soc_mbox_data_avail(mbox1_data_avail), 
    .uc_mbox_data_avail(mci_mbox1_data_avail), 
    .soc_req_mbox_lock(soc_req_mbox1_lock), 
    .mbox_protocol_error(mbox1_protocol_error), 
    .mbox_inv_axi_user_axs(mbox1_inv_user_p), 
    //dma FIXME
    .dma_sram_req_dv  ('0),
    .dma_sram_req_write('0),
    .dma_sram_req_addr('0),
    .dma_sram_req_wdata('0),
    .dma_sram_rdata   (),
    .dma_sram_hold    (),
    .dma_sram_error   (),
    // DMI unused 
    .dmi_inc_rdptr('0),
    .dmi_inc_wrptr('0),
    .dmi_reg_wen('0),
    .dmi_reg_addr('0),
    .dmi_reg_wdata('0),
    .dmi_reg(),
    //direct request unsupported
    .dir_req_dv(1'b0),
    .dir_rdata(),
    //sha accelerator unsupported
    .sha_sram_req_dv('0),
    .sha_sram_req_addr('0),
    .sha_sram_resp_ecc(),
    .sha_sram_resp_data(),
    .sha_sram_hold()
);
end
endgenerate


 // DUT instantiation
mci_lcc_st_trans LCC_state_translator (
    .clk(clk),
    .rst_n(mci_rst_b),
    .state_error(1'b0),  // TODO: This needs to be added to put caliptra into debug locked position
    .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
    .lc_dft_en_i(lc_dft_en_i),
    .lc_hw_debug_en_i(lc_hw_debug_en_i),
    .from_otp_to_lcc_program_i(from_otp_to_lcc_program_i),
    .ss_dbg_manuf_enable_i(ss_dbg_manuf_enable_i),
    .ss_soc_dbg_unlock_level_i(ss_soc_dbg_unlock_level_i),
    .ss_soc_dft_en_mask_reg0_1(64'h0), // TODO: there should be two registers for this connection
    .ss_soc_dbg_unlock_mask_reg0_1(64'h0), // TODO: there should be two registers for this connection
    .ss_soc_CLTAP_unlock_mask_reg0_1(64'h0), // TODO: there should be two registers for this connection
    .SOC_DFT_EN(SOC_DFT_EN),
    .SOC_HW_DEBUG_EN(SOC_HW_DEBUG_EN),
    .security_state_o(security_state_o)
);

endmodule
