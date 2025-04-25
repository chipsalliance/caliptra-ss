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
//
//`define MCU_DRAM(bk) caliptra_ss_top.mcu_top_i.dccm_loop[bk].ram.ram_core
`define MCU_RV_LSU_BUS_TAG_local 1
`define INCLUDE_FUSE_CTRL = 1

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"
`include "i3c_defines.svh"
`include "caliptra_ss_includes.svh"

module caliptra_ss_top
    import axi_pkg::*;
    import soc_ifc_pkg::*;
#(
    `include "css_mcu0_el2_param.vh"
    ,parameter MCU_MBOX0_SIZE_KB = 4
    ,parameter [4:0] SET_MCU_MBOX0_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCU_MBOX0_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
    ,parameter MCU_MBOX1_SIZE_KB = 4
    ,parameter [4:0] SET_MCU_MBOX1_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
    ,parameter [4:0][31:0] MCU_MBOX1_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
    ,parameter MCU_SRAM_SIZE_KB = 512
) (
    input logic cptra_ss_clk_i,
    output logic cptra_ss_rdc_clk_cg_o,
    input logic cptra_ss_pwrgood_i,
    input logic cptra_ss_rst_b_i,
    input  logic cptra_ss_mci_cptra_rst_b_i,
    output logic cptra_ss_mci_cptra_rst_b_o,
    output logic cptra_ss_rst_b_o,

// Caliptra Core AXI Sub Interface
    axi_if.w_sub cptra_ss_cptra_core_s_axi_if_w_sub,
    axi_if.r_sub cptra_ss_cptra_core_s_axi_if_r_sub,

// Caliptra Core AXI Manager Interface
    axi_if.w_mgr cptra_ss_cptra_core_m_axi_if_w_mgr,
    axi_if.r_mgr cptra_ss_cptra_core_m_axi_if_r_mgr,

// Caliptra SS MCI AXI Sub Interface
    axi_if.w_sub cptra_ss_mci_s_axi_if_w_sub,
    axi_if.r_sub cptra_ss_mci_s_axi_if_r_sub,

// Caliptra SS MCU ROM AXI Sub Interface
    axi_if.w_sub cptra_ss_mcu_rom_s_axi_if_w_sub,
    axi_if.r_sub cptra_ss_mcu_rom_s_axi_if_r_sub,
    axi_mem_if.request mcu_rom_mem_export_if,

// Caliptra SS MCU LSU/IFU AXI Manager Interface
    axi_if.w_mgr       cptra_ss_mcu_lsu_m_axi_if_w_mgr,
    axi_if.r_mgr       cptra_ss_mcu_lsu_m_axi_if_r_mgr,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awcache,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arcache,
    output logic [2:0] cptra_ss_mcu_lsu_m_axi_if_awprot,
    output logic [2:0] cptra_ss_mcu_lsu_m_axi_if_arprot,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awregion,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arregion,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awqos,
    output logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arqos,
    axi_if.w_mgr       cptra_ss_mcu_ifu_m_axi_if_w_mgr,
    axi_if.r_mgr       cptra_ss_mcu_ifu_m_axi_if_r_mgr,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awcache,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arcache,
    output logic [2:0] cptra_ss_mcu_ifu_m_axi_if_awprot,
    output logic [2:0] cptra_ss_mcu_ifu_m_axi_if_arprot,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awregion,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arregion,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awqos,
    output logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arqos,
    axi_if.w_mgr       cptra_ss_mcu_sb_m_axi_if_w_mgr,
    axi_if.r_mgr       cptra_ss_mcu_sb_m_axi_if_r_mgr,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_awcache,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_arcache,
    output logic [2:0] cptra_ss_mcu_sb_m_axi_if_awprot,
    output logic [2:0] cptra_ss_mcu_sb_m_axi_if_arprot,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_awregion,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_arregion,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_awqos,
    output logic [3:0] cptra_ss_mcu_sb_m_axi_if_arqos,

// Caliptra SS I3C AXI Sub Interface
    axi_if.w_sub cptra_ss_i3c_s_axi_if_w_sub,
    axi_if.r_sub cptra_ss_i3c_s_axi_if_r_sub,

// Caliptra SS LC Controller AXI Sub Interface
    input  axi_struct_pkg::axi_wr_req_t cptra_ss_lc_axi_wr_req_i,
    output axi_struct_pkg::axi_wr_rsp_t cptra_ss_lc_axi_wr_rsp_o,
    input  axi_struct_pkg::axi_rd_req_t cptra_ss_lc_axi_rd_req_i,
    output axi_struct_pkg::axi_rd_rsp_t cptra_ss_lc_axi_rd_rsp_o,

// Caliptra SS FC / OTP Controller AXI Sub Interface
    input  axi_struct_pkg::axi_wr_req_t cptra_ss_otp_core_axi_wr_req_i,
    output axi_struct_pkg::axi_wr_rsp_t cptra_ss_otp_core_axi_wr_rsp_o,
    input  axi_struct_pkg::axi_rd_req_t cptra_ss_otp_core_axi_rd_req_i,
    output axi_struct_pkg::axi_rd_rsp_t cptra_ss_otp_core_axi_rd_rsp_o,

//--------------------
// caliptra core Obf Key & CSR Signing Key
//--------------------
    input logic [255:0]                              cptra_ss_cptra_obf_key_i,
    input logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0] cptra_ss_cptra_csr_hmac_key_i,

//Caliptra JTAG Interface
    input logic                        cptra_ss_cptra_core_jtag_tck_i,    // JTAG clk
    input logic                        cptra_ss_cptra_core_jtag_tms_i,    // JTAG TMS
    input logic                        cptra_ss_cptra_core_jtag_tdi_i,    // JTAG tdi
    input logic                        cptra_ss_cptra_core_jtag_trst_n_i, // JTAG Reset
    output logic                       cptra_ss_cptra_core_jtag_tdo_o,    // JTAG TDO
    output logic                       cptra_ss_cptra_core_jtag_tdoEn_o,  // JTAG TDO enable
    output logic [124:0]               cptra_ss_cptra_generic_fw_exec_ctrl_o,
    output logic cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o,
    input  logic cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i,

//LC controller JTAG
    input   jtag_pkg::jtag_req_t                       cptra_ss_lc_ctrl_jtag_i,
    output  jtag_pkg::jtag_rsp_t                       cptra_ss_lc_ctrl_jtag_o,

// Caliptra Memory Export Interface
// Caliptra Core, ICCM and DCCM interface
    el2_mem_if.veer_sram_src           cptra_ss_cptra_core_el2_mem_export,
    mldsa_mem_if.req                   mldsa_memory_export_req,

// SRAM interface for mbox
// Caliptra SS mailbox sram interface
    output logic cptra_ss_cptra_core_mbox_sram_cs_o,
    output logic cptra_ss_cptra_core_mbox_sram_we_o,
    output logic [CPTRA_MBOX_ADDR_W-1:0] cptra_sscptra_core_mbox_sram_addr_o,
    output logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_wdata_o,
    input  logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_rdata_i,

// Caliptra Core SRAM interface for imem (/ROM)
    output logic cptra_ss_cptra_core_imem_cs_o,
    output logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] cptra_ss_cptra_core_imem_addr_o,
    input  logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] cptra_ss_cptra_core_imem_rdata_i,

// -- Caliptra Core Boot FSM Breakpoint
    input logic                        cptra_ss_cptra_core_bootfsm_bp_i,

// TRNG Interface
`ifdef CALIPTRA_INTERNAL_TRNG
    // External Request
    output logic             cptra_ss_cptra_core_etrng_req_o,
    // Physical Source for Internal TRNG
    input  logic [3:0]       cptra_ss_cptra_core_itrng_data_i,
    input  logic             cptra_ss_cptra_core_itrng_valid_i,
`endif

// Caliptra SS MCU 
    input  logic [31:0] cptra_ss_strap_mcu_lsu_axi_user_i,
    input  logic [31:0] cptra_ss_strap_mcu_ifu_axi_user_i,
    input  logic [31:0] cptra_ss_strap_mcu_sram_config_axi_user_i,
    input  logic [31:0] cptra_ss_strap_mci_soc_config_axi_user_i,
    output logic        cptra_ss_cpu_halt_status_o,

// Caliptra SS MCI MCU SRAM Interface (SRAM, MBOX0, MBOX1)
    mci_mcu_sram_if.request cptra_ss_mci_mcu_sram_req_if,
    mci_mcu_sram_if.request cptra_ss_mcu_mbox0_sram_req_if,
    mci_mcu_sram_if.request cptra_ss_mcu_mbox1_sram_req_if,
    css_mcu0_el2_mem_if.veer_sram_icache_src cptra_ss_mcu0_el2_mem_export,

//  MCU MBOX signals
    output logic cptra_ss_soc_mcu_mbox0_data_avail,
    output logic cptra_ss_soc_mcu_mbox1_data_avail,

    input logic [63:0] cptra_ss_mci_generic_input_wires_i,

    input logic [31:0] cptra_ss_strap_mcu_reset_vector_i,
    input logic cptra_ss_mcu_no_rom_config_i,
    input logic cptra_ss_mci_boot_seq_brkpoint_i,

    input logic cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i,
    input logic cptra_ss_FIPS_ZEROIZATION_PPD_i,

    output logic [63:0] cptra_ss_mci_generic_output_wires_o,
    output logic cptra_ss_all_error_fatal_o,
    output logic cptra_ss_all_error_non_fatal_o,

    input logic [pt.PIC_TOTAL_INT:`VEER_INTR_EXT_LSB] cptra_ss_mcu_ext_int,
    input logic cptra_ss_mcu_jtag_tck_i,
    input logic cptra_ss_mcu_jtag_tms_i,
    input logic cptra_ss_mcu_jtag_tdi_i,
    input logic cptra_ss_mcu_jtag_trst_n_i,
    output logic cptra_ss_mcu_jtag_tdo_o,
    output logic cptra_ss_mcu_jtag_tdoEn_o,

    input logic [63:0]  cptra_ss_strap_caliptra_base_addr_i,
    input logic [63:0]  cptra_ss_strap_mci_base_addr_i,
    input logic [63:0]  cptra_ss_strap_recovery_ifc_base_addr_i,
    input logic [63:0]  cptra_ss_strap_otp_fc_base_addr_i,
    input logic [63:0]  cptra_ss_strap_uds_seed_base_addr_i,
    input logic [31:0]  cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i,
    input logic [31:0]  cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i,
    input logic [31:0]  cptra_ss_strap_caliptra_dma_axi_user_i,
    input logic [31:0]  cptra_ss_strap_generic_0_i,
    input logic [31:0]  cptra_ss_strap_generic_1_i,
    input logic [31:0]  cptra_ss_strap_generic_2_i,
    input logic [31:0]  cptra_ss_strap_generic_3_i,
    input logic         cptra_ss_debug_intent_i,            // Debug intent signal

    output logic        cptra_ss_dbg_manuf_enable_o,
    output logic [63:0] cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o,

    input  lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_ack_i,
    output lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_req_o,
    input  logic cptra_ss_lc_ctrl_scan_rst_ni_i,

    input logic cptra_ss_lc_esclate_scrap_state0_i,   // NOTE: These two signals are very important. FIXME: Renaming is needed
    input logic cptra_ss_lc_esclate_scrap_state1_i,   // If you assert them, Caliptr-SS will enter SCRAP mode

    output wire cptra_ss_soc_dft_en_o,
    output wire cptra_ss_soc_hw_debug_en_o,

// Caliptra SS Fuse Controller Interface (Fuse Macros)
    input otp_ctrl_pkg::prim_generic_otp_outputs_t      cptra_ss_fuse_macro_outputs_i,
    output otp_ctrl_pkg::prim_generic_otp_inputs_t      cptra_ss_fuse_macro_inputs_o,
   
// Caliptra SS I3C GPIO Interface
`ifdef DIGITAL_IO_I3C
    input  logic cptra_ss_i3c_scl_i,
    input  logic cptra_ss_i3c_sda_i,
    output logic cptra_ss_i3c_scl_o,
    output logic cptra_ss_i3c_sda_o,
    output logic cptra_ss_sel_od_pp_o,
`else
    inout  wire  cptra_ss_i3c_scl_io,
    inout  wire  cptra_ss_i3c_sda_io,
`endif

// -- THESE ARE NOT RTL SIGNALS, DO NOT USE THEM
// -- note: these are output required for TB
// -- this will go away in final release
    input  logic [63:0] cptra_ss_cptra_core_generic_input_wires_i,
    input  logic        cptra_ss_cptra_core_scan_mode_i,
    output logic        cptra_error_fatal,
    output logic        cptra_error_non_fatal,
    output logic        ready_for_fuses,
    output logic        ready_for_mb_processing,
    output logic        mailbox_data_avail

    
);

    logic [pt.PIC_TOTAL_INT:1]  ext_int;
    logic        [31:0]         agg_error_fatal;
    logic        [31:0]         agg_error_non_fatal;
    logic                       timer_int;

    logic                       mcu_dccm_ecc_single_error;
    logic                       mcu_dccm_ecc_double_error;

    logic                       i3c_irq_o;
    logic                       i3c_peripheral_reset;
    logic                       i3c_escalated_reset;

    logic        [31:0]         reset_vector;


    logic                       o_debug_mode_status;

    logic                       jtag_tdo;
    logic                       i_cpu_halt_req;
    logic                       o_cpu_halt_ack;
    logic                       o_cpu_run_ack;

    logic        [63:0]         dma_hrdata       ;
    logic        [63:0]         dma_hwdata       ;
    logic                       dma_hready       ;
    logic                       dma_hresp        ;

    logic                       mpc_debug_halt_req;
    logic                       mpc_debug_run_req;
    logic                       mpc_reset_run_req;
    logic                       mpc_debug_halt_ack;
    logic                       mpc_debug_run_ack;
    logic                       debug_brkpt_status;

    logic                       mailbox_data_val;

    wire                        dma_hready_out;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    logic                       wb_csr_valid;
    logic [11:0]                wb_csr_dest;
    logic [31:0]                wb_csr_data;

    logic mcu_clk_cg;

    logic        mcu_dmi_core_enable;
    logic        mcu_dmi_uncore_enable;
    logic        mcu_dmi_uncore_en;
    logic        mcu_dmi_uncore_wr_en;
    logic [ 6:0] mcu_dmi_uncore_addr;
    logic [31:0] mcu_dmi_uncore_wdata;
    logic [31:0] mcu_dmi_uncore_rdata;
    logic        mcu_dmi_active; 

    // ----------------- MCU Trace within Subsystem -----------------------
    logic [31:0] mcu_trace_rv_i_insn_ip;
    logic [31:0] mcu_trace_rv_i_address_ip;
    logic        mcu_trace_rv_i_valid_ip;
    logic        mcu_trace_rv_i_exception_ip;
    logic [ 4:0] mcu_trace_rv_i_ecause_ip;
    logic        mcu_trace_rv_i_interrupt_ip;
    logic [31:0] mcu_trace_rv_i_tval_ip;
    
    // -- caliptra DUT instance
    // -- Will be removed in final release.
    logic [63:0] cptra_ss_cptra_core_generic_output_wires_o;

    // ----------------- MCI Connections within Subsystem -----------------------
    logic mcu_rst_b;


    // ----------------- MCI Connections LCC Connections -----------------------
    logic lcc_to_mci_lc_done;
    logic mci_to_lcc_init_req;
    pwrmgr_pkg::pwr_lc_req_t lcc_init_req;


    // ----------------- MCI Connections FC Connections -----------------------
    logic [otp_ctrl_reg_pkg::NumAlerts-1:0] fc_alerts;
    logic fc_intr_otp_error;
    logic FIPS_ZEROIZATION_CMD;

    // ----------------- MCI OTP Connections -----------------------------------
    logic mci_to_otp_ctrl_init_req;
    logic otp_ctrl_to_mci_otp_ctrl_done;
    pwrmgr_pkg::pwr_otp_req_t otp_ctrl_init_req;


    //--------------------------MCI&LCC Gasket Signal Def---------------------
    // Inputs from LCC
    otp_ctrl_pkg::lc_otp_program_req_t from_lcc_to_otp_program_i;
    lc_ctrl_pkg::lc_tx_t lc_dft_en_i;
    lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i;
    // Inputs from OTP_Ctrl
    otp_ctrl_pkg::otp_lc_data_t from_otp_to_lcc_data_i;


    soc_ifc_pkg::security_state_t mci_cptra_security_state;

    logic intr_otp_operation_done;
    logic mci_mcu_nmi_int;
    logic [31:0] mci_mcu_nmi_vector;
    logic mci_mcu_timer_int;

    logic [lc_ctrl_reg_pkg::NumAlerts-1:0] lc_alerts_o; 

    // ----------------- FC to Caliptra-Core ports -----------------------
    otp_ctrl_part_pkg::otp_broadcast_t from_otp_to_clpt_core_broadcast;  // This is a struct data type
    // broadcasted by fuse controller
    logic uds_field_entrpy_valid;
    logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed;
    logic [`CLP_OBF_FE_DWORDS-1 : 0][31:0] cptra_obf_field_entropy;
    // --------------------------------------------------------------------

    //---------------------------I3C---------------------------------------
    logic payload_available_o;
    logic image_activated_o;

    mci_mcu_sram_if cptra_ss_mcu_rom_mbox0_sram_req_if (
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_o)
    );
    
    mci_mcu_sram_if cptra_ss_mcu_rom_mbox1_sram_req_if (
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_o)
    );


    



    ///////
    // AXI USER assignments
    ///////
    // ARUSER
    assign cptra_ss_mcu_lsu_m_axi_if_r_mgr.aruser = cptra_ss_strap_mcu_lsu_axi_user_i;
    assign cptra_ss_mcu_ifu_m_axi_if_r_mgr.aruser = cptra_ss_strap_mcu_ifu_axi_user_i;
    assign cptra_ss_mcu_sb_m_axi_if_r_mgr.aruser = cptra_ss_strap_mcu_lsu_axi_user_i;
    
    // AWUSER
    assign cptra_ss_mcu_lsu_m_axi_if_w_mgr.awuser = cptra_ss_strap_mcu_lsu_axi_user_i;
    assign cptra_ss_mcu_ifu_m_axi_if_w_mgr.awuser = cptra_ss_strap_mcu_ifu_axi_user_i;
    assign cptra_ss_mcu_sb_m_axi_if_w_mgr.awuser = cptra_ss_strap_mcu_lsu_axi_user_i;
    
    // BUSER
    assign cptra_ss_i3c_s_axi_if_w_sub.buser = '0; // FIXME - no port on I3C - https://github.com/chipsalliance/i3c-core/issues/25
    
    // RUSER
    assign cptra_ss_i3c_s_axi_if_r_sub.ruser = '0; // FIXME - no port on I3C - https://github.com/chipsalliance/i3c-core/issues/25
    
    // WUSER
    assign cptra_ss_mcu_lsu_m_axi_if_w_mgr.wuser = '0; // WUSER not used in Caliptra SS
    assign cptra_ss_mcu_ifu_m_axi_if_w_mgr.wuser = '0; // WUSER not used in Caliptra SS
    assign cptra_ss_mcu_sb_m_axi_if_w_mgr.wuser = '0; // WUSER not used in Caliptra SS

    ///////
    // AXI ID assignments
    ///////
    generate
        if ($bits(cptra_ss_mcu_lsu_m_axi_if_r_mgr.arid) > pt.LSU_BUS_TAG) begin
            assign cptra_ss_mcu_lsu_m_axi_if_r_mgr.arid[$bits(cptra_ss_mcu_lsu_m_axi_if_r_mgr.arid)-1:pt.LSU_BUS_TAG] = '0;
        end
        if ($bits(cptra_ss_mcu_lsu_m_axi_if_w_mgr.awid) > pt.IFU_BUS_TAG) begin
            assign cptra_ss_mcu_lsu_m_axi_if_w_mgr.awid[$bits(cptra_ss_mcu_lsu_m_axi_if_w_mgr.awid)-1:pt.LSU_BUS_TAG] = '0;
        end
        if ($bits(cptra_ss_mcu_ifu_m_axi_if_r_mgr.arid) > pt.IFU_BUS_TAG) begin
            assign cptra_ss_mcu_ifu_m_axi_if_r_mgr.arid[$bits(cptra_ss_mcu_ifu_m_axi_if_r_mgr.arid)-1:pt.IFU_BUS_TAG] = '0;
        end
        if ($bits(cptra_ss_mcu_ifu_m_axi_if_w_mgr.awid) > pt.IFU_BUS_TAG) begin
            assign cptra_ss_mcu_ifu_m_axi_if_w_mgr.awid[$bits(cptra_ss_mcu_ifu_m_axi_if_w_mgr.awid)-1:pt.IFU_BUS_TAG] = '0;
        end
        if ($bits(cptra_ss_mcu_sb_m_axi_if_r_mgr.arid) > pt.IFU_BUS_TAG) begin
            assign cptra_ss_mcu_sb_m_axi_if_r_mgr.arid[$bits(cptra_ss_mcu_sb_m_axi_if_r_mgr.arid)-1:pt.SB_BUS_TAG] = '0;
        end
        if ($bits(cptra_ss_mcu_sb_m_axi_if_w_mgr.awid) > pt.IFU_BUS_TAG) begin
            assign cptra_ss_mcu_sb_m_axi_if_w_mgr.awid[$bits(cptra_ss_mcu_sb_m_axi_if_w_mgr.awid)-1:pt.SB_BUS_TAG] = '0;
        end
    endgenerate

    // Fuse controller output is re-organized to feed caliptra-core with its fuse values and valid signal.
     assign uds_field_entrpy_valid = (from_otp_to_clpt_core_broadcast.valid == lc_ctrl_pkg::On) ? 1'b1 : 1'b0;
     always_comb begin: uds_fe_fuse_assignment
        for (int i=0; i<`CLP_OBF_UDS_DWORDS; i++ ) begin
            cptra_obf_uds_seed[i] = from_otp_to_clpt_core_broadcast.secret_manuf_partition_data.cptra_core_uds_seed[i*32 +: 32];
        end
        {cptra_obf_field_entropy[1], cptra_obf_field_entropy[0]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_0_data.cptra_core_field_entropy_0;
        {cptra_obf_field_entropy[3], cptra_obf_field_entropy[2]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_1_data.cptra_core_field_entropy_1;
        {cptra_obf_field_entropy[5], cptra_obf_field_entropy[4]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_2_data.cptra_core_field_entropy_2;
        {cptra_obf_field_entropy[7], cptra_obf_field_entropy[6]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_3_data.cptra_core_field_entropy_3;
     end
    //=========================================================================-
    // Caliptra DUT instance
    //=========================================================================-
    
    logic [127:0] cptra_ss_cptra_generic_fw_exec_ctrl_internal;
    assign cptra_ss_cptra_generic_fw_exec_ctrl_o = cptra_ss_cptra_generic_fw_exec_ctrl_internal[127:3];
    assign cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o = cptra_ss_cptra_generic_fw_exec_ctrl_internal[2];

    caliptra_top caliptra_top_dut (
        .clk                        (cptra_ss_clk_i),
        .cptra_pwrgood              (cptra_ss_pwrgood_i),
        .cptra_rst_b                (cptra_ss_mci_cptra_rst_b_i),

        .cptra_obf_key              (cptra_ss_cptra_obf_key_i),
        .cptra_obf_uds_seed_vld     (uds_field_entrpy_valid), //TODO
        .cptra_obf_uds_seed         (cptra_obf_uds_seed), 
        .cptra_obf_field_entropy_vld(uds_field_entrpy_valid), 
        .cptra_obf_field_entropy    (cptra_obf_field_entropy), 
        .cptra_csr_hmac_key         (cptra_ss_cptra_csr_hmac_key_i),

        .jtag_tck   (cptra_ss_cptra_core_jtag_tck_i   ),
        .jtag_tdi   (cptra_ss_cptra_core_jtag_tdi_i   ),
        .jtag_tms   (cptra_ss_cptra_core_jtag_tms_i   ),
        .jtag_trst_n(cptra_ss_cptra_core_jtag_trst_n_i),
        .jtag_tdo   (cptra_ss_cptra_core_jtag_tdo_o   ),
        .jtag_tdoEn (cptra_ss_cptra_core_jtag_tdoEn_o ),
        
        //SoC AXI Interface
        .s_axi_w_if(cptra_ss_cptra_core_s_axi_if_w_sub),
        .s_axi_r_if(cptra_ss_cptra_core_s_axi_if_r_sub),

        //AXI DMA Interface
        .m_axi_w_if(cptra_ss_cptra_core_m_axi_if_w_mgr),
        .m_axi_r_if(cptra_ss_cptra_core_m_axi_if_r_mgr),

        .el2_mem_export(cptra_ss_cptra_core_el2_mem_export),
        .mldsa_memory_export(mldsa_memory_export_req),

        .ready_for_fuses(ready_for_fuses),
        .ready_for_mb_processing(ready_for_mb_processing),
        .ready_for_runtime(),

        .mbox_sram_cs(cptra_ss_cptra_core_mbox_sram_cs_o),
        .mbox_sram_we(cptra_ss_cptra_core_mbox_sram_we_o),
        .mbox_sram_addr(cptra_sscptra_core_mbox_sram_addr_o),
        .mbox_sram_wdata(cptra_ss_cptra_core_mbox_sram_wdata_o),
        .mbox_sram_rdata(cptra_ss_cptra_core_mbox_sram_rdata_i),
            
        .imem_cs(cptra_ss_cptra_core_imem_cs_o),
        .imem_addr(cptra_ss_cptra_core_imem_addr_o),
        .imem_rdata(cptra_ss_cptra_core_imem_rdata_i),

        .mailbox_data_avail(mailbox_data_avail),
        .mailbox_flow_done(),
        .BootFSM_BrkPoint(cptra_ss_cptra_core_bootfsm_bp_i),

        .recovery_data_avail(payload_available_o),
        .recovery_image_activated(image_activated_o),

        //SoC Interrupts
        .cptra_error_fatal    (cptra_error_fatal    ),
        .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
        .etrng_req             (cptra_ss_cptra_core_etrng_req_o),
        .itrng_data            (cptra_ss_cptra_core_itrng_data_i),
        .itrng_valid           (cptra_ss_cptra_core_itrng_valid_i),
`else
        .etrng_req             (    ),
        .itrng_data            (4'b0),
        .itrng_valid           (1'b0),
`endif

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            ( cptra_ss_strap_caliptra_base_addr_i ),
        .strap_ss_mci_base_addr                                 ( cptra_ss_strap_mci_base_addr_i ),
        .strap_ss_recovery_ifc_base_addr                        ( cptra_ss_strap_recovery_ifc_base_addr_i ),
        .strap_ss_otp_fc_base_addr                              ( cptra_ss_strap_otp_fc_base_addr_i ),
        .strap_ss_uds_seed_base_addr                            ( cptra_ss_strap_uds_seed_base_addr_i ),
        .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset( cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i ),
        .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       ( cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i ),
        .strap_ss_caliptra_dma_axi_user                         ( cptra_ss_strap_caliptra_dma_axi_user_i),
        .strap_ss_strap_generic_0                               ( cptra_ss_strap_generic_0_i ),
        .strap_ss_strap_generic_1                               ( cptra_ss_strap_generic_1_i ),
        .strap_ss_strap_generic_2                               ( cptra_ss_strap_generic_2_i ),
        .strap_ss_strap_generic_3                               ( cptra_ss_strap_generic_3_i ),

        .ss_debug_intent                                        ( cptra_ss_debug_intent_i ),

        // Subsystem mode debug outputs
        .ss_dbg_manuf_enable(cptra_ss_dbg_manuf_enable_o),
        .ss_soc_dbg_unlock_level(cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(cptra_ss_cptra_generic_fw_exec_ctrl_internal),

        .generic_input_wires(cptra_ss_cptra_core_generic_input_wires_i),
        .generic_output_wires(cptra_ss_cptra_core_generic_output_wires_o),

        .security_state(mci_cptra_security_state),
        .scan_mode     (cptra_ss_cptra_core_scan_mode_i)
    );




    logic mci_intr;

    //Interrupt connections
    assign ext_int[`VEER_INTR_VEC_MCI]                  = mci_intr;
    assign ext_int[`VEER_INTR_VEC_I3C]                  = i3c_irq_o;
    assign ext_int[pt.PIC_TOTAL_INT:`VEER_INTR_EXT_LSB] = cptra_ss_mcu_ext_int;

    //Aggregate error connections
    assign agg_error_fatal[5:0]   = {5'b0, cptra_error_fatal}; //CPTRA
    assign agg_error_fatal[11:6]  = {5'b0, mcu_dccm_ecc_double_error}; //MCU
    assign agg_error_fatal[17:12] = {{6-lc_ctrl_reg_pkg::NumAlerts{1'b0}}, lc_alerts_o}; //LCC
    assign agg_error_fatal[23:18] = {fc_intr_otp_error, fc_alerts}; //FC
    assign agg_error_fatal[29:24] = {4'b0, i3c_peripheral_reset, i3c_escalated_reset}; //I3C
    assign agg_error_fatal[31:30] = '0; //spare

    assign agg_error_non_fatal[5:0]   = {5'b0, cptra_error_non_fatal}; //CPTRA
    assign agg_error_non_fatal[11:6]  = {5'b0, mcu_dccm_ecc_single_error}; //MCU
    assign agg_error_non_fatal[17:12] = {{6-lc_ctrl_reg_pkg::NumAlerts{1'b0}}, lc_alerts_o}; //LCC
    assign agg_error_non_fatal[23:18] = {fc_intr_otp_error, fc_alerts}; //FC
    assign agg_error_non_fatal[29:24] = {4'b0, i3c_peripheral_reset, i3c_escalated_reset}; //I3C
    assign agg_error_non_fatal[31:30] = '0; //spare

    //=========================================================================-
    // MCU instance
    //=========================================================================-
    mcu_top rvtop_wrapper (
        .rst_l                  ( mcu_rst_b ),
        .dbg_rst_l              ( cptra_ss_pwrgood_i ), //FIXME same as caliptra?
        .clk                    ( mcu_clk_cg ),
        .rst_vec                ( reset_vector[31:1]),
        .nmi_int                ( mci_mcu_nmi_int),
        .nmi_vec                ( mci_mcu_nmi_vector[31:1]),

        //-------------------------- LSU AXI signals--------------------------
        // // AXI Write Channels

        .lsu_axi_awvalid        (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awvalid),
        .lsu_axi_awready        (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awready),
        .lsu_axi_awid           (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awid[pt.LSU_BUS_TAG-1:0]),
        .lsu_axi_awaddr         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awaddr[31:0]),
        .lsu_axi_awregion       (cptra_ss_mcu_lsu_m_axi_if_awregion),
        .lsu_axi_awlen          (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awlen),
        .lsu_axi_awsize         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awsize),
        .lsu_axi_awburst        (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awburst),
        .lsu_axi_awlock         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.awlock),
        .lsu_axi_awcache        (cptra_ss_mcu_lsu_m_axi_if_awcache),
        .lsu_axi_awprot         (cptra_ss_mcu_lsu_m_axi_if_awprot),
        .lsu_axi_awqos          (cptra_ss_mcu_lsu_m_axi_if_awqos),

        .lsu_axi_wvalid         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.wvalid),
        .lsu_axi_wready         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.wready),
        .lsu_axi_wdata          (cptra_ss_mcu_lsu_m_axi_if_w_mgr.wdata),
        .lsu_axi_wstrb          (cptra_ss_mcu_lsu_m_axi_if_w_mgr.wstrb),
        .lsu_axi_wlast          (cptra_ss_mcu_lsu_m_axi_if_w_mgr.wlast),

        .lsu_axi_bvalid         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.bvalid),
        .lsu_axi_bready         (cptra_ss_mcu_lsu_m_axi_if_w_mgr.bready),
        .lsu_axi_bresp          (cptra_ss_mcu_lsu_m_axi_if_w_mgr.bresp),
        .lsu_axi_bid            (cptra_ss_mcu_lsu_m_axi_if_w_mgr.bid[pt.LSU_BUS_TAG-1:0]),

        .lsu_axi_arvalid        (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arvalid),
        .lsu_axi_arready        (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arready),
        .lsu_axi_arid           (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arid[pt.LSU_BUS_TAG-1:0]),
        .lsu_axi_araddr         (cptra_ss_mcu_lsu_m_axi_if_r_mgr.araddr[31:0]),
        .lsu_axi_arregion       (cptra_ss_mcu_lsu_m_axi_if_arregion),
        .lsu_axi_arlen          (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arlen),
        .lsu_axi_arsize         (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arsize),
        .lsu_axi_arburst        (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arburst),
        .lsu_axi_arlock         (cptra_ss_mcu_lsu_m_axi_if_r_mgr.arlock),
        .lsu_axi_arcache        (cptra_ss_mcu_lsu_m_axi_if_arcache),
        .lsu_axi_arprot         (cptra_ss_mcu_lsu_m_axi_if_arprot),
        .lsu_axi_arqos          (cptra_ss_mcu_lsu_m_axi_if_arqos),

        .lsu_axi_rvalid         (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rvalid),
        .lsu_axi_rready         (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rready),
        .lsu_axi_rid            (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rid[pt.LSU_BUS_TAG-1:0]),
        .lsu_axi_rdata          (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rdata),
        .lsu_axi_rresp          (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rresp),
        .lsu_axi_rlast          (cptra_ss_mcu_lsu_m_axi_if_r_mgr.rlast),

        //-------------------------- IFU AXI signals--------------------------
        // AXI Write Channels

        .ifu_axi_awvalid        ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awvalid ),
        .ifu_axi_awready        ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awready ),
        .ifu_axi_awid           ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awid[pt.IFU_BUS_TAG-1:0]),
        .ifu_axi_awaddr         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awaddr[31:0]  ),
        .ifu_axi_awregion       ( cptra_ss_mcu_ifu_m_axi_if_awregion),
        .ifu_axi_awlen          ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awlen   ),
        .ifu_axi_awsize         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awsize  ),
        .ifu_axi_awburst        ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awburst ),
        .ifu_axi_awlock         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.awlock  ),
        .ifu_axi_awcache        ( cptra_ss_mcu_ifu_m_axi_if_awcache ),
        .ifu_axi_awprot         ( cptra_ss_mcu_ifu_m_axi_if_awprot  ),
        .ifu_axi_awqos          ( cptra_ss_mcu_ifu_m_axi_if_awqos   ),

        .ifu_axi_wvalid         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.wvalid  ),
        .ifu_axi_wready         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.wready  ),
        .ifu_axi_wdata          ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.wdata   ),
        .ifu_axi_wstrb          ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.wstrb   ),
        .ifu_axi_wlast          ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.wlast   ),

        .ifu_axi_bvalid         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.bvalid  ),
        .ifu_axi_bready         ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.bready  ),
        .ifu_axi_bresp          ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.bresp   ),
        .ifu_axi_bid            ( cptra_ss_mcu_ifu_m_axi_if_w_mgr.bid[pt.IFU_BUS_TAG-1:0]     ),

        .ifu_axi_arvalid        ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arvalid ),
        .ifu_axi_arready        ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arready ),
        .ifu_axi_arid           ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arid[pt.IFU_BUS_TAG-1:0]    ),
        .ifu_axi_araddr         ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.araddr[31:0] ),
        .ifu_axi_arlen          ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arlen   ),
        .ifu_axi_arsize         ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arsize  ),
        .ifu_axi_arburst        ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arburst ),
        .ifu_axi_arlock         ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.arlock  ),
        .ifu_axi_arcache        ( cptra_ss_mcu_ifu_m_axi_if_arcache ),
        .ifu_axi_arprot         ( cptra_ss_mcu_ifu_m_axi_if_arprot  ),
        .ifu_axi_arqos          ( cptra_ss_mcu_ifu_m_axi_if_arqos   ),
        .ifu_axi_arregion       ( cptra_ss_mcu_ifu_m_axi_if_arregion),

        .ifu_axi_rvalid         ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rvalid  ),
        .ifu_axi_rready         ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rready  ),
        .ifu_axi_rid            ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rid[pt.IFU_BUS_TAG-1:0]     ),
        .ifu_axi_rdata          ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rdata   ),
        .ifu_axi_rresp          ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rresp   ),
        .ifu_axi_rlast          ( cptra_ss_mcu_ifu_m_axi_if_r_mgr.rlast   ),

        //-------------------------- SB AXI signals--------------------------
        // AXI Write Channels -- system bus
        .sb_axi_awvalid         (cptra_ss_mcu_sb_m_axi_if_w_mgr.awvalid),
        .sb_axi_awready         (cptra_ss_mcu_sb_m_axi_if_w_mgr.awready),
        .sb_axi_awid            (cptra_ss_mcu_sb_m_axi_if_w_mgr.awid[pt.SB_BUS_TAG-1:0]),
        .sb_axi_awaddr          (cptra_ss_mcu_sb_m_axi_if_w_mgr.awaddr[31:0]),
        .sb_axi_awregion        (cptra_ss_mcu_sb_m_axi_if_awregion),
        .sb_axi_awlen           (cptra_ss_mcu_sb_m_axi_if_w_mgr.awlen),
        .sb_axi_awsize          (cptra_ss_mcu_sb_m_axi_if_w_mgr.awsize),
        .sb_axi_awburst         (cptra_ss_mcu_sb_m_axi_if_w_mgr.awburst),
        .sb_axi_awlock          (cptra_ss_mcu_sb_m_axi_if_w_mgr.awlock),
        .sb_axi_awcache         (cptra_ss_mcu_sb_m_axi_if_awcache),
        .sb_axi_awprot          (cptra_ss_mcu_sb_m_axi_if_awprot),
        .sb_axi_awqos           (cptra_ss_mcu_sb_m_axi_if_awqos),

        .sb_axi_wvalid          (cptra_ss_mcu_sb_m_axi_if_w_mgr.wvalid),
        .sb_axi_wready          (cptra_ss_mcu_sb_m_axi_if_w_mgr.wready),
        .sb_axi_wdata           (cptra_ss_mcu_sb_m_axi_if_w_mgr.wdata),
        .sb_axi_wstrb           (cptra_ss_mcu_sb_m_axi_if_w_mgr.wstrb),
        .sb_axi_wlast           (cptra_ss_mcu_sb_m_axi_if_w_mgr.wlast),

        .sb_axi_bvalid          (cptra_ss_mcu_sb_m_axi_if_w_mgr.bvalid),
        .sb_axi_bready          (cptra_ss_mcu_sb_m_axi_if_w_mgr.bready),
        .sb_axi_bresp           (cptra_ss_mcu_sb_m_axi_if_w_mgr.bresp),
        .sb_axi_bid             (cptra_ss_mcu_sb_m_axi_if_w_mgr.bid[pt.SB_BUS_TAG-1:0]),

        .sb_axi_arvalid         (cptra_ss_mcu_sb_m_axi_if_r_mgr.arvalid),
        .sb_axi_arready         (cptra_ss_mcu_sb_m_axi_if_r_mgr.arready),
        .sb_axi_arid            (cptra_ss_mcu_sb_m_axi_if_r_mgr.arid[pt.SB_BUS_TAG-1:0]),
        .sb_axi_araddr          (cptra_ss_mcu_sb_m_axi_if_r_mgr.araddr[31:0]),
        .sb_axi_arregion        (cptra_ss_mcu_sb_m_axi_if_arregion),
        .sb_axi_arlen           (cptra_ss_mcu_sb_m_axi_if_r_mgr.arlen),
        .sb_axi_arsize          (cptra_ss_mcu_sb_m_axi_if_r_mgr.arsize),
        .sb_axi_arburst         (cptra_ss_mcu_sb_m_axi_if_r_mgr.arburst),
        .sb_axi_arlock          (cptra_ss_mcu_sb_m_axi_if_r_mgr.arlock),
        .sb_axi_arcache         (cptra_ss_mcu_sb_m_axi_if_arcache),
        .sb_axi_arprot          (cptra_ss_mcu_sb_m_axi_if_arprot),
        .sb_axi_arqos           (cptra_ss_mcu_sb_m_axi_if_arqos),

        .sb_axi_rvalid          (cptra_ss_mcu_sb_m_axi_if_r_mgr.rvalid),
        .sb_axi_rready          (cptra_ss_mcu_sb_m_axi_if_r_mgr.rready),
        .sb_axi_rid             (cptra_ss_mcu_sb_m_axi_if_r_mgr.rid[pt.SB_BUS_TAG-1:0]),
        .sb_axi_rdata           (cptra_ss_mcu_sb_m_axi_if_r_mgr.rdata),
        .sb_axi_rresp           (cptra_ss_mcu_sb_m_axi_if_r_mgr.rresp),
        .sb_axi_rlast           (cptra_ss_mcu_sb_m_axi_if_r_mgr.rlast),

        //-------------------------- DMA AXI signals--------------------------
        // AXI Write Channels
        .dma_axi_awvalid        ('0), // unused
        .dma_axi_awready        (), // unused
        .dma_axi_awid           ('0), // unused
        .dma_axi_awaddr         ('0), // unused
        .dma_axi_awsize         ('0), // unused
        .dma_axi_awprot         ('0),//(), // unused
        .dma_axi_awlen          ('0), // unused
        .dma_axi_awburst        ('0), // unused

        .dma_axi_wvalid         ('0), // unused
        .dma_axi_wready         (), // unused
        .dma_axi_wdata          ('0), // unused
        .dma_axi_wstrb          ('0), // unused
        .dma_axi_wlast          ('0), // unused

        .dma_axi_bvalid         (), // unused
        .dma_axi_bready         ('0), // unused
        .dma_axi_bresp          (), // unused
        .dma_axi_bid            (), // unused

        .dma_axi_arvalid        ('0), // unused
        .dma_axi_arready        (), // unused
        .dma_axi_arid           ('0), // unused
        .dma_axi_araddr         ('0), // unused
        .dma_axi_arsize         ('0), // unused
        .dma_axi_arprot         ('0),//(), // unused
        .dma_axi_arlen          ('0), // unused
        .dma_axi_arburst        ('0), // unused

        .dma_axi_rvalid         (), // unused
        .dma_axi_rready         ('0), // unused
        .dma_axi_rid            (), // unused
        .dma_axi_rdata          (), // unused
        .dma_axi_rresp          (), // unused
        .dma_axi_rlast          (), // unused

        .timer_int              ( mci_mcu_timer_int ),
        .soft_int               ( 1'b0 ), // No multi-processor functionality, not expecting MSI from other HARTs
        .extintsrc_req          ( ext_int ),

        .lsu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .ifu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .dbg_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
        .dma_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

        .trace_rv_i_insn_ip     (mcu_trace_rv_i_insn_ip     ),
        .trace_rv_i_address_ip  (mcu_trace_rv_i_address_ip  ),
        .trace_rv_i_valid_ip    (mcu_trace_rv_i_valid_ip    ),
        .trace_rv_i_exception_ip(mcu_trace_rv_i_exception_ip),
        .trace_rv_i_ecause_ip   (mcu_trace_rv_i_ecause_ip   ),
        .trace_rv_i_interrupt_ip(mcu_trace_rv_i_interrupt_ip),
        .trace_rv_i_tval_ip     (mcu_trace_rv_i_tval_ip     ),

        // JTAG Interface
        .jtag_tck               ( cptra_ss_mcu_jtag_tck_i ),
        .jtag_tms               ( cptra_ss_mcu_jtag_tms_i ),
        .jtag_tdi               ( cptra_ss_mcu_jtag_tdi_i ),
        .jtag_trst_n            ( cptra_ss_mcu_jtag_trst_n_i ),
        .jtag_tdo               ( cptra_ss_mcu_jtag_tdo_o ),
        .jtag_tdoEn             ( cptra_ss_mcu_jtag_tdoEn_o ),

        .mpc_debug_halt_ack     ( mpc_debug_halt_ack),
        .mpc_debug_halt_req     ( 1'b0),
        .mpc_debug_run_ack      ( mpc_debug_run_ack),
        .mpc_debug_run_req      ( 1'b1),
        .mpc_reset_run_req      ( 1'b1),             // Start running after reset
        .debug_brkpt_status     (debug_brkpt_status),
        .o_debug_mode_status    (o_debug_mode_status),

        .i_cpu_halt_req         ( i_cpu_halt_req ),    // Async halt req to CPU
        .o_cpu_halt_ack         ( o_cpu_halt_ack ),    // core response to halt
        .o_cpu_halt_status      ( cptra_ss_cpu_halt_status_o ), // 1'b1 indicates core is halted
        .i_cpu_run_req          ( 1'b0  ),     // Async restart req to CPU
        .o_cpu_run_ack          ( o_cpu_run_ack ),     // Core response to run req

        .dec_tlu_perfcnt0       (),
        .dec_tlu_perfcnt1       (),
        .dec_tlu_perfcnt2       (),
        .dec_tlu_perfcnt3       (),

        .mem_clk                (cptra_ss_mcu0_el2_mem_export.clk),

        // -- Include this as part of integration specification
        // -- These signals are not used in the design
        .iccm_clken             (cptra_ss_mcu0_el2_mem_export.iccm_clken),
        .iccm_wren_bank         (cptra_ss_mcu0_el2_mem_export.iccm_wren_bank),
        .iccm_addr_bank         (cptra_ss_mcu0_el2_mem_export.iccm_addr_bank),
        .iccm_bank_wr_data      (cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_data),
        .iccm_bank_wr_ecc       (cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_ecc),
        .iccm_bank_dout         (cptra_ss_mcu0_el2_mem_export.iccm_bank_dout),
        .iccm_bank_ecc          (cptra_ss_mcu0_el2_mem_export.iccm_bank_ecc),

        .dccm_clken             (cptra_ss_mcu0_el2_mem_export.dccm_clken),
        .dccm_wren_bank         (cptra_ss_mcu0_el2_mem_export.dccm_wren_bank),
        .dccm_addr_bank         (cptra_ss_mcu0_el2_mem_export.dccm_addr_bank),
        .dccm_wr_data_bank      (cptra_ss_mcu0_el2_mem_export.dccm_wr_data_bank),
        .dccm_wr_ecc_bank       (cptra_ss_mcu0_el2_mem_export.dccm_wr_ecc_bank),
        .dccm_bank_dout         (cptra_ss_mcu0_el2_mem_export.dccm_bank_dout),
        .dccm_bank_ecc          (cptra_ss_mcu0_el2_mem_export.dccm_bank_ecc),

        // ICache Export Interface
        // ICache Data
        .ic_b_sb_wren              (cptra_ss_mcu0_el2_mem_export.ic_b_sb_wren              ),
        .ic_b_sb_bit_en_vec        (cptra_ss_mcu0_el2_mem_export.ic_b_sb_bit_en_vec        ),
        .ic_sb_wr_data             (cptra_ss_mcu0_el2_mem_export.ic_sb_wr_data             ),
        .ic_rw_addr_bank_q         (cptra_ss_mcu0_el2_mem_export.ic_rw_addr_bank_q         ),
        .ic_bank_way_clken_final   (cptra_ss_mcu0_el2_mem_export.ic_bank_way_clken_final   ),
        .ic_bank_way_clken_final_up(cptra_ss_mcu0_el2_mem_export.ic_bank_way_clken_final_up),
        .wb_packeddout_pre         (cptra_ss_mcu0_el2_mem_export.wb_packeddout_pre         ),
        .wb_dout_pre_up            (cptra_ss_mcu0_el2_mem_export.wb_dout_pre_up            ),
        // ICache Tag
        .ic_tag_clken_final        (cptra_ss_mcu0_el2_mem_export.ic_tag_clken_final        ),
        .ic_tag_wren_q             (cptra_ss_mcu0_el2_mem_export.ic_tag_wren_q             ),
        .ic_tag_wren_biten_vec     (cptra_ss_mcu0_el2_mem_export.ic_tag_wren_biten_vec     ),
        .ic_tag_wr_data            (cptra_ss_mcu0_el2_mem_export.ic_tag_wr_data            ),
        .ic_rw_addr_q              (cptra_ss_mcu0_el2_mem_export.ic_rw_addr_q              ),
        .ic_tag_data_raw_pre       (cptra_ss_mcu0_el2_mem_export.ic_tag_data_raw_pre       ),
        .ic_tag_data_raw_packed_pre(cptra_ss_mcu0_el2_mem_export.ic_tag_data_raw_packed_pre),

        .iccm_ecc_single_error  (),
        .iccm_ecc_double_error  (),
        .dccm_ecc_single_error  (mcu_dccm_ecc_single_error),
        .dccm_ecc_double_error  (mcu_dccm_ecc_double_error),

        .core_id                ('0),
        .scan_mode              ( 1'b0 ),        // To enable scan mode
        .mbist_mode             ( 1'b0 ),        // to enable mbist

        .dmi_core_enable   (mcu_dmi_core_enable),
        .dmi_uncore_enable   (mcu_dmi_uncore_enable),
        .dmi_uncore_en   (mcu_dmi_uncore_en),
        .dmi_uncore_wr_en   (mcu_dmi_uncore_wr_en),
        .dmi_uncore_addr   (mcu_dmi_uncore_addr),
        .dmi_uncore_wdata   (mcu_dmi_uncore_wdata),
        .dmi_uncore_rdata   (mcu_dmi_uncore_rdata),
        .dmi_active   (mcu_dmi_active)

    );

    //=========================================================================-
    // i3c_core Instance
    //=========================================================================-

    i3c_wrapper #(
        .AxiDataWidth(`AXI_DATA_WIDTH),
        .AxiAddrWidth(`AXI_ADDR_WIDTH),
        .AxiUserWidth(`AXI_USER_WIDTH),
        .AxiIdWidth  (`AXI_ID_WIDTH  )
    ) i3c (
        .clk_i (cptra_ss_clk_i),
        .rst_ni(cptra_ss_rst_b_o),

        .arvalid_i  (cptra_ss_i3c_s_axi_if_r_sub.arvalid),
        .arready_o  (cptra_ss_i3c_s_axi_if_r_sub.arready),
        .arid_i     (cptra_ss_i3c_s_axi_if_r_sub.arid),
        .araddr_i   (cptra_ss_i3c_s_axi_if_r_sub.araddr[`AXI_ADDR_WIDTH-1:0]),
        .arsize_i   (cptra_ss_i3c_s_axi_if_r_sub.arsize),
        .aruser_i   (cptra_ss_i3c_s_axi_if_r_sub.aruser),
        .arlen_i    (cptra_ss_i3c_s_axi_if_r_sub.arlen),
        .arburst_i  (cptra_ss_i3c_s_axi_if_r_sub.arburst),
        .arlock_i   (cptra_ss_i3c_s_axi_if_r_sub.arlock),
        .rvalid_o   (cptra_ss_i3c_s_axi_if_r_sub.rvalid),
        .rready_i   (cptra_ss_i3c_s_axi_if_r_sub.rready),
        .rid_o      (cptra_ss_i3c_s_axi_if_r_sub.rid),
        .rdata_o    (cptra_ss_i3c_s_axi_if_r_sub.rdata),
        .rresp_o    (cptra_ss_i3c_s_axi_if_r_sub.rresp),
        .rlast_o    (cptra_ss_i3c_s_axi_if_r_sub.rlast),
        .awvalid_i  (cptra_ss_i3c_s_axi_if_w_sub.awvalid),
        .awready_o  (cptra_ss_i3c_s_axi_if_w_sub.awready),
        .awid_i     (cptra_ss_i3c_s_axi_if_w_sub.awid),
        .awaddr_i   (cptra_ss_i3c_s_axi_if_w_sub.awaddr[`AXI_ADDR_WIDTH-1:0]),
        .awsize_i   (cptra_ss_i3c_s_axi_if_w_sub.awsize),
        .awuser_i   (cptra_ss_i3c_s_axi_if_w_sub.awuser),
        .awlen_i    (cptra_ss_i3c_s_axi_if_w_sub.awlen),
        .awburst_i  (cptra_ss_i3c_s_axi_if_w_sub.awburst),
        .awlock_i   (cptra_ss_i3c_s_axi_if_w_sub.awlock),
        .wvalid_i   (cptra_ss_i3c_s_axi_if_w_sub.wvalid),
        .wuser_i    (cptra_ss_i3c_s_axi_if_w_sub.wuser),
        .wready_o   (cptra_ss_i3c_s_axi_if_w_sub.wready),
        .wdata_i    (cptra_ss_i3c_s_axi_if_w_sub.wdata),
        .wstrb_i    (cptra_ss_i3c_s_axi_if_w_sub.wstrb),
        .wlast_i    (cptra_ss_i3c_s_axi_if_w_sub.wlast),
        .bvalid_o   (cptra_ss_i3c_s_axi_if_w_sub.bvalid),
        .bready_i   (cptra_ss_i3c_s_axi_if_w_sub.bready),
        .bresp_o    (cptra_ss_i3c_s_axi_if_w_sub.bresp),
        .bid_o      (cptra_ss_i3c_s_axi_if_w_sub.bid),
`ifdef DIGITAL_IO_I3C
        .scl_i(cptra_ss_i3c_scl_i),
        .sda_i(cptra_ss_i3c_sda_i),
        .scl_o(cptra_ss_i3c_scl_o),
        .sda_o(cptra_ss_i3c_sda_o),
        .sel_od_pp_o(cptra_ss_sel_od_pp_o),
`else
        .i3c_scl_io(cptra_ss_i3c_scl_io),
        .i3c_sda_io(cptra_ss_i3c_sda_io),
`endif
        .recovery_payload_available_o(payload_available_o),
        .recovery_image_activated_o(image_activated_o),
        .peripheral_reset_o(i3c_peripheral_reset),
        .peripheral_reset_done_i(1'b1),
        .escalated_reset_o(i3c_escalated_reset),
        .irq_o(i3c_irq_o),

        .disable_id_filtering_i(1'b0),
        .priv_ids_i('{cptra_ss_strap_mcu_lsu_axi_user_i, cptra_ss_strap_caliptra_dma_axi_user_i, 32'b0, 32'b0}) // -- FIXME : ENABLE THIS FEATURE

    );

    //=========================================================================
    // MCU ROM Interface Instance (Reuses MCI)
    //=========================================================================

    axi_mem #(
      .AW(CPTRA_SS_ROM_AXI_ADDR_W),
      .DW(CPTRA_SS_ROM_DATA_W),
      .IW(`CALIPTRA_AXI_ID_WIDTH)
    ) mcu_rom_i (
      .clk(cptra_ss_clk_i),
      .rst_n(cptra_ss_rst_b_o),

      .s_axi_r_if(cptra_ss_mcu_rom_s_axi_if_r_sub),
      .s_axi_w_if(cptra_ss_mcu_rom_s_axi_if_w_sub),

      .s_mem_req_if(mcu_rom_mem_export_if)
    );

    //=========================================================================
    // MCI Instance
    //=========================================================================

    //TODO: we need to open two input ports for the following signals:
            // lc_ctrl_pkg::lc_tx_t lc_escalate_en_internal;
            // lc_ctrl_pkg::lc_tx_t lc_check_byp_en_internal;
    // These signals show that escalation is enabled at LCC and FUSE end and external clock was accepted.
    // The following signal should be also an input coming from LC to MCI
            //lc_hw_rev_t  hw_rev_o;
    mci_top #(
        .AXI_ADDR_WIDTH  ($bits(cptra_ss_mci_s_axi_if_r_sub.araddr)),
        .AXI_DATA_WIDTH  (32                                       ),
        .AXI_USER_WIDTH  ($bits(cptra_ss_mci_s_axi_if_r_sub.aruser)),
        .AXI_ID_WIDTH    ($bits(cptra_ss_mci_s_axi_if_r_sub.arid)  ),
        .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB                         ),

        .MCU_MBOX0_SIZE_KB(MCU_MBOX0_SIZE_KB),
        .SET_MCU_MBOX0_AXI_USER_INTEG(SET_MCU_MBOX0_AXI_USER_INTEG),  
        .MCU_MBOX0_VALID_AXI_USER(MCU_MBOX0_VALID_AXI_USER),    
        .MCU_MBOX1_SIZE_KB(MCU_MBOX1_SIZE_KB),
        .SET_MCU_MBOX1_AXI_USER_INTEG(SET_MCU_MBOX1_AXI_USER_INTEG),  
        .MCU_MBOX1_VALID_AXI_USER(MCU_MBOX1_VALID_AXI_USER)    
    ) mci_top_i (

        .clk(cptra_ss_clk_i),
        .mcu_clk_cg(mcu_clk_cg),
        .cptra_ss_rdc_clk_cg(cptra_ss_rdc_clk_cg_o), 


        .mci_rst_b(cptra_ss_rst_b_i),
        .mci_pwrgood(cptra_ss_pwrgood_i),
        .cptra_ss_rst_b_o(cptra_ss_rst_b_o),
        
        // DFT
        .scan_mode     (cptra_ss_cptra_core_scan_mode_i),

        // MCI AXI Interface
        .s_axi_w_if(cptra_ss_mci_s_axi_if_w_sub),
        .s_axi_r_if(cptra_ss_mci_s_axi_if_r_sub),
        
        .strap_mcu_lsu_axi_user(cptra_ss_strap_mcu_lsu_axi_user_i),
        .strap_mcu_ifu_axi_user(cptra_ss_strap_mcu_ifu_axi_user_i),
        .strap_mcu_sram_config_axi_user    (cptra_ss_strap_mcu_sram_config_axi_user_i),
        .strap_mci_soc_config_axi_user    (cptra_ss_strap_mci_soc_config_axi_user_i),
        .ss_debug_intent         ( cptra_ss_debug_intent_i ),

        // -- connects to ss_generic_fw_exec_ctrl (bit 2)
        .mcu_sram_fw_exec_region_lock(cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i),

        .agg_error_fatal(agg_error_fatal),
        .agg_error_non_fatal(agg_error_non_fatal),

        .all_error_fatal(cptra_ss_all_error_fatal_o),
        .all_error_non_fatal(cptra_ss_all_error_non_fatal_o),

        .mci_generic_input_wires(cptra_ss_mci_generic_input_wires_i),
        .mci_generic_output_wires(cptra_ss_mci_generic_output_wires_o),

        .mcu_timer_int(mci_mcu_timer_int),
        .mci_intr(mci_intr),

        .cptra_mbox_data_avail(mailbox_data_avail),

        .strap_mcu_reset_vector(cptra_ss_strap_mcu_reset_vector_i),
        
        .mcu_reset_vector(reset_vector),
        
        // OTP
        .intr_otp_operation_done,
        
        // MCU Halt Signals
        .mcu_cpu_halt_req_o   (i_cpu_halt_req   ),
        .mcu_cpu_halt_ack_i   (o_cpu_halt_ack   ),
        .mcu_cpu_halt_status_i(cptra_ss_cpu_halt_status_o),

        .mcu_no_rom_config(cptra_ss_mcu_no_rom_config_i),

        .nmi_intr(mci_mcu_nmi_int),
        .mcu_nmi_vector(mci_mcu_nmi_vector),

        .mcu_rst_b(mcu_rst_b),
        .cptra_rst_b(cptra_ss_mci_cptra_rst_b_o),

        // MBOX
        .soc_mcu_mbox0_data_avail(cptra_ss_soc_mcu_mbox0_data_avail),
        .soc_mcu_mbox1_data_avail(cptra_ss_soc_mcu_mbox1_data_avail),

        // MCU DMI
        .mcu_dmi_core_enable,
        .mcu_dmi_uncore_enable,
        .mcu_dmi_uncore_en,
        .mcu_dmi_uncore_wr_en,
        .mcu_dmi_uncore_addr,
        .mcu_dmi_uncore_wdata,
        .mcu_dmi_uncore_rdata,
        .mcu_dmi_active,
        
        // MCU Trace
        .mcu_trace_rv_i_insn_ip     ,
        .mcu_trace_rv_i_address_ip  ,
        .mcu_trace_rv_i_valid_ip    ,
        .mcu_trace_rv_i_exception_ip,
        .mcu_trace_rv_i_ecause_ip   ,
        .mcu_trace_rv_i_interrupt_ip,
        .mcu_trace_rv_i_tval_ip     ,


        .mci_boot_seq_brkpoint(cptra_ss_mci_boot_seq_brkpoint_i),

        .lc_done(lcc_to_mci_lc_done), //output from lcc
        .lc_init(mci_to_lcc_init_req), //input to lcc
        // .lc_bus_integ_error_fatal(1'b0),
        .lc_fatal_state_error_i(lc_alerts_o[1]),
        // .lc_prog_error_fatal(1'b0),

        .fc_opt_done(otp_ctrl_to_mci_otp_ctrl_done), //output from otp
        .fc_opt_init(mci_to_otp_ctrl_init_req), //input to otp
        .FIPS_ZEROIZATION_PPD_i(cptra_ss_FIPS_ZEROIZATION_PPD_i),
        .FIPS_ZEROIZATION_CMD_o(FIPS_ZEROIZATION_CMD),
        // .fc_intr_otp_error(1'b0),

        .mci_mcu_sram_req_if  (cptra_ss_mci_mcu_sram_req_if),
        .mcu_mbox0_sram_req_if(cptra_ss_mcu_mbox0_sram_req_if),
        .mcu_mbox1_sram_req_if(cptra_ss_mcu_mbox1_sram_req_if),
        

        .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
        .lc_dft_en_i(lc_dft_en_i),
        .lc_hw_debug_en_i(lc_hw_debug_en_i),

        // Inputs from OTP_Ctrl
        .from_otp_to_lcc_program_i(from_otp_to_lcc_data_i),

        // Inputs from Caliptra_Core
        .ss_dbg_manuf_enable_i(cptra_ss_dbg_manuf_enable_o),
        .ss_soc_dbg_unlock_level_i(cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o),

        // Converted Signals from LCC to SoC
        .SOC_DFT_EN(cptra_ss_soc_dft_en_o),
        .SOC_HW_DEBUG_EN(cptra_ss_soc_hw_debug_en_o),

        // Converted Signals from LCC to Caliptra-core
        .security_state_o(mci_cptra_security_state)

    );

    //=========================================================================-
    // Life-cycle Controller Instance : 
    // 
    //=========================================================================-

    //--------------------------------------------------------------------------------------------
    // These are shared signals between fuse controller and lc controller

    //------------------------- LCC and FC internal signals -------------------------------------
    // These are shared signals between fuse controller and lc controller
    otp_ctrl_pkg::lc_otp_vendor_test_req_t from_lc_to_otp_vendor_test_internal;
    otp_ctrl_pkg::lc_otp_vendor_test_rsp_t from_otp_to_lc_vendor_test_internal;
    otp_ctrl_pkg::lc_otp_program_rsp_t lc_otp_program_internal;

    lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_internal;
    lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_internal;
    lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en_internal;
    lc_ctrl_pkg::lc_tx_t lc_escalate_en_internal;
    lc_ctrl_pkg::lc_tx_t lc_check_byp_en_internal;
    caliptra_prim_mubi_pkg::mubi4_t lc_ctrl_scanmode_i;
    assign lc_ctrl_scanmode_i = caliptra_prim_mubi_pkg::MuBi4False;


    //--------------------------------------------------------------------------------------------

    //--------------------------------------------------------------------------------------------

    pwrmgr_pkg::pwr_lc_rsp_t                    u_lc_ctrl_pwr_lc_o;
    assign lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(u_lc_ctrl_pwr_lc_o.lc_done);
    assign lcc_init_req.lc_init = mci_to_lcc_init_req; 

    lc_ctrl u_lc_ctrl (
            .clk_i(cptra_ss_clk_i),
            .rst_ni(cptra_ss_rst_b_o),
            .Allow_RMA_or_SCRAP_on_PPD(cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i),
            .axi_wr_req(cptra_ss_lc_axi_wr_req_i),
            .axi_wr_rsp(cptra_ss_lc_axi_wr_rsp_o),
            .axi_rd_req(cptra_ss_lc_axi_rd_req_i),
            .axi_rd_rsp(cptra_ss_lc_axi_rd_rsp_o),

            .jtag_i(cptra_ss_lc_ctrl_jtag_i),
            .jtag_o(cptra_ss_lc_ctrl_jtag_o),
            
            .scan_rst_ni(cptra_ss_lc_ctrl_scan_rst_ni_i),
            
            .scanmode_i(lc_ctrl_scanmode_i),

            .alerts(lc_alerts_o),

            .esc_scrap_state0(cptra_ss_lc_esclate_scrap_state0_i),
            .esc_scrap_state1(cptra_ss_lc_esclate_scrap_state1_i),

            .pwr_lc_i(lcc_init_req),
            .pwr_lc_o(u_lc_ctrl_pwr_lc_o), // Note: It is tied with this assignment: lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(u_lc_ctrl.pwr_lc_o.lc_done);

            .lc_otp_vendor_test_o(from_lc_to_otp_vendor_test_internal),
            .lc_otp_vendor_test_i(from_otp_to_lc_vendor_test_internal),
            .lc_otp_program_o(from_lcc_to_otp_program_i),
            .lc_otp_program_i(lc_otp_program_internal),
            .otp_lc_data_i(from_otp_to_lcc_data_i),
            .lc_dft_en_o(lc_dft_en_i),
            .lc_creator_seed_sw_rw_en_o(lc_creator_seed_sw_rw_en_internal),
            .lc_owner_seed_sw_rw_en_o(lc_owner_seed_sw_rw_en_internal),
            .lc_seed_hw_rd_en_o(lc_seed_hw_rd_en_internal),            
            .lc_escalate_en_o(lc_escalate_en_internal),
            .lc_check_byp_en_o(lc_check_byp_en_internal),

            .lc_hw_debug_en_o(lc_hw_debug_en_i),

            .lc_clk_byp_req_o(cptra_ss_lc_clk_byp_req_o),
            .lc_clk_byp_ack_i(cptra_ss_lc_clk_byp_ack_i),

            .otp_device_id_i(256'd0),   // FIXME: This signal should come from FC
            .otp_manuf_state_i(256'd0), // FIXME: This signal should come from FC
            .hw_rev_o()             // FIXME: This signal should go to MCI 
        );


    //=========================================================================-
    // Fuse Controller Instance : 
    // 
    //=========================================================================-

    pwrmgr_pkg::pwr_otp_rsp_t                   u_otp_ctrl_pwr_otp_o;
    assign otp_ctrl_to_mci_otp_ctrl_done = pwrmgr_pkg::pwr_otp_rsp_t'(u_otp_ctrl_pwr_otp_o.otp_done);
    assign otp_ctrl_init_req.otp_init = mci_to_otp_ctrl_init_req;

    otp_ctrl #(
        .MemInitFile ("otp-img.2048.vmem")
    ) u_otp_ctrl (
        .clk_i                      (cptra_ss_clk_i),
        .rst_ni                     (cptra_ss_rst_b_o),
        .FIPS_ZEROIZATION_CMD_i     (FIPS_ZEROIZATION_CMD),

        .cptra_ss_strap_mcu_lsu_axi_user_i  (cptra_ss_strap_mcu_lsu_axi_user_i),
        .cptra_ss_strap_cptra_axi_user_i    (cptra_ss_strap_caliptra_dma_axi_user_i),


        .core_axi_wr_req            (cptra_ss_otp_core_axi_wr_req_i),
        .core_axi_wr_rsp            (cptra_ss_otp_core_axi_wr_rsp_o),
        .core_axi_rd_req            (cptra_ss_otp_core_axi_rd_req_i),
        .core_axi_rd_rsp            (cptra_ss_otp_core_axi_rd_rsp_o),
        
        .prim_tl_i                  (107'd0),
        .prim_tl_o                  (),
        .prim_generic_otp_outputs_i (cptra_ss_fuse_macro_outputs_i),
        .prim_generic_otp_inputs_o  (cptra_ss_fuse_macro_inputs_o),

        .intr_otp_operation_done_o  (intr_otp_operation_done),
        .intr_otp_error_o           (fc_intr_otp_error), 
        // .alert_rx_i                 (),
        // .alert_tx_o                 (),
        .alerts(fc_alerts),
        .pwr_otp_i                  (otp_ctrl_init_req),
        .pwr_otp_o                  (u_otp_ctrl_pwr_otp_o),

        .lc_otp_vendor_test_i(from_lc_to_otp_vendor_test_internal),
        .lc_otp_vendor_test_o(from_otp_to_lc_vendor_test_internal),
        .lc_otp_program_i(from_lcc_to_otp_program_i),
        .lc_otp_program_o(lc_otp_program_internal),

        .lc_creator_seed_sw_rw_en_i(lc_creator_seed_sw_rw_en_internal),
        .lc_owner_seed_sw_rw_en_i(lc_owner_seed_sw_rw_en_internal),
        .lc_seed_hw_rd_en_i(lc_seed_hw_rd_en_internal),
        .lc_dft_en_i(lc_dft_en_i),
        .lc_escalate_en_i(lc_escalate_en_internal),
        .lc_check_byp_en_i(lc_check_byp_en_internal),

        .otp_lc_data_o(from_otp_to_lcc_data_i),

        .otp_broadcast_o            (from_otp_to_clpt_core_broadcast),
        .scanmode_i                 (caliptra_prim_mubi_pkg::MuBi4False)
    ); 

    `CALIPTRA_ASSERT(i3c_payload_available, ($rose(payload_available_o) |-> ##[1:50] payload_available_o == 0),cptra_ss_clk_i, cptra_ss_rst_b_i)
    `CALIPTRA_ASSERT(i3c_image_activated, ($rose(image_activated_o) |-> ##[1:50] image_activated_o == 0), cptra_ss_clk_i, cptra_ss_rst_b_i)

endmodule
