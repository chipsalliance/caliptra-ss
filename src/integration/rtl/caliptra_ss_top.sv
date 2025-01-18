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

`default_nettype none

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"
`include "i3c_defines.svh"

module caliptra_ss_top
    import axi_pkg::*;
    import soc_ifc_pkg::*;
#(
    `include "css_mcu0_el2_param.vh"
) (
    input logic cptra_ss_clk,
    input logic cptra_ss_pwrgood,
    input logic cptra_ss_rst_b,

    //SoC AXI Interface
    axi_if cptra_core_s_axi_if,

    // AXI Manager INF
    axi_if cptra_core_m_axi_if,

    //SoC AXI Interface
    axi_if mci_s_axi_if,

    // AXI Manager INF
    axi_if mci_m_axi_if,

    axi_if mcu_lsu_m_axi_if,
    axi_if mcu_ifu_m_axi_if,
    axi_if mcu_dma_s_axi_if,
    axi_if i3c_s_axi_if,

    input axi_struct_pkg::axi_wr_req_t lc_axi_wr_req,
    output axi_struct_pkg::axi_wr_rsp_t lc_axi_wr_rsp,
    input axi_struct_pkg::axi_rd_req_t lc_axi_rd_req,
    output axi_struct_pkg::axi_rd_rsp_t lc_axi_rd_rsp,

    input axi_struct_pkg::axi_wr_req_t core_axi_wr_req,
    output axi_struct_pkg::axi_wr_rsp_t core_axi_wr_rsp,
    input axi_struct_pkg::axi_rd_req_t core_axi_rd_req,
    output axi_struct_pkg::axi_rd_rsp_t core_axi_rd_rsp,

    //--------------------
    //caliptra core signals
    //--------------------
    input logic [255:0]                              cptra_obf_key,
    input logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0] cptra_csr_hmac_key,  
    //Caliptra JTAG Interface
    input logic                        cptra_core_jtag_tck,    // JTAG clk
    input logic                        cptra_core_jtag_tms,    // JTAG TMS
    input logic                        cptra_core_jtag_tdi,    // JTAG tdi
    input logic                        cptra_core_jtag_trst_n, // JTAG Reset
    output logic                       cptra_core_jtag_tdo,    // JTAG TDO
    output logic                       cptra_core_jtag_tdoEn,  // JTAG TDO enable

    // Caliptra Memory Export Interface
    el2_mem_if.veer_sram_src           cptra_core_el2_mem_export,

    //SRAM interface for mbox
    output logic cptra_core_mbox_sram_cs,
    output logic cptra_core_mbox_sram_we,
    output logic [CPTRA_MBOX_ADDR_W-1:0] cptra_core_mbox_sram_addr,
    output logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_core_mbox_sram_wdata,
    input  logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_core_mbox_sram_rdata,

    //SRAM interface for imem
    output logic cptra_core_imem_cs,
    output logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] cptra_core_imem_addr,
    input  logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] cptra_core_imem_rdata,
    
    output logic                       ready_for_fuses,
    output logic                       ready_for_mb_processing,

    output logic                       mailbox_data_avail,

    input logic                        BootFSM_BrkPoint,

    //SoC Interrupts
    output logic             cptra_error_fatal,
    output logic             cptra_error_non_fatal,

    // TRNG Interface
    `ifdef CALIPTRA_INTERNAL_TRNG
    // External Request
    output logic             cptra_core_etrng_req,
    // Physical Source for Internal TRNG
    input  logic [3:0]       cptra_core_itrng_data,
    input  logic             cptra_core_itrng_valid,
    `endif

    input logic  [63:0]                cptra_core_generic_input_wires,
    output logic [63:0]                cptra_core_generic_output_wires,

    input logic                        scan_mode,

    //MCU
    mci_mcu_sram_if.request mci_mcu_sram_req_if,

    mci_mcu_sram_if.request mci_mbox0_sram_req_if,
    
    mci_mcu_sram_if.request mci_mbox1_sram_req_if,

    css_mcu0_el2_mem_if.veer_sram_src css_mcu0_el2_mem_export,

    input logic Allow_RMA_on_PPD,
    input logic fake_reset,

    input logic lc_ctrl_scan_rst_ni,
    input logic [$bits(caliptra_prim_mubi_pkg::mubi4_t)-1:0] lc_ctrl_scanmode_i,


    input logic [$bits(otp_ctrl_pkg::otp_lc_data_t)-1:0] otp_lc_data,
    input logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_clk_byp_ack,
    output logic [lc_ctrl_reg_pkg::NumAlerts-1:0] lc_alerts_o,

    input logic esc_scrap_state0,
    input logic esc_scrap_state1,

    output  wire                                 SOC_DFT_EN,
    output  wire                                 SOC_HW_DEBUG_EN,

    `ifdef VERILATOR
    input bit [31:0]            mem_signature_begin,
    input bit [31:0]            mem_signature_end,
    input bit [31:0]            mem_mailbox
    `endif // VERILATOR
    // I3C Interface
`ifdef VERILATOR
    input  logic scl_i,
    input  logic sda_i,
    output logic scl_o,
    output logic sda_o,
    output logic sel_od_pp_o
`else
    inout  wire  i3c_scl_io,
    inout  wire  i3c_sda_io
`endif
);

`ifndef VERILATOR
    bit          [31:0]         mem_signature_begin = 32'd0; // TODO:
    bit          [31:0]         mem_signature_end   = 32'd0;
    bit          [31:0]         mem_mailbox         = 32'h21000410;
`endif

    logic [pt.PIC_TOTAL_INT:1]  ext_int;
    logic                       timer_int;
    logic                       soft_int;

    logic        [31:0]         reset_vector;


    logic                       o_debug_mode_status;

    logic                       jtag_tdo;
    logic                       o_cpu_halt_ack;
    logic                       o_cpu_halt_status;
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

    int                         cycleCnt;
    logic                       mailbox_data_val;

    wire                        dma_hready_out;
    int                         commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    logic                       wb_csr_valid;
    logic [11:0]                wb_csr_dest;
    logic [31:0]                wb_csr_data;

`ifdef MCU_RV_BUILD_AXI4
   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
    wire                        lsu_axi_awvalid;
    wire                        lsu_axi_awready;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lsu_axi_awid;
    wire [31:0]                 lsu_axi_awaddr;
    wire [3:0]                  lsu_axi_awregion;
    wire [7:0]                  lsu_axi_awlen;
    wire [2:0]                  lsu_axi_awsize;
    wire [1:0]                  lsu_axi_awburst;
    wire                        lsu_axi_awlock;
    wire [3:0]                  lsu_axi_awcache;
    wire [2:0]                  lsu_axi_awprot;
    wire [3:0]                  lsu_axi_awqos;

    wire                        lsu_axi_wvalid;
    wire                        lsu_axi_wready;
    wire [63:0]                 lsu_axi_wdata;
    wire [7:0]                  lsu_axi_wstrb;
    wire                        lsu_axi_wlast;

    wire                        lsu_axi_bvalid;
    wire                        lsu_axi_bready;
    wire [1:0]                  lsu_axi_bresp;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lsu_axi_bid;

    // AXI Read Channels
    wire                        lsu_axi_arvalid;
    wire                        lsu_axi_arready;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lsu_axi_arid;
    wire [31:0]                 lsu_axi_araddr;
    wire [3:0]                  lsu_axi_arregion;
    wire [7:0]                  lsu_axi_arlen;
    wire [2:0]                  lsu_axi_arsize;
    wire [1:0]                  lsu_axi_arburst;
    wire                        lsu_axi_arlock;
    wire [3:0]                  lsu_axi_arcache;
    wire [2:0]                  lsu_axi_arprot;
    wire [3:0]                  lsu_axi_arqos;

    wire                        lsu_axi_rvalid;
    wire                        lsu_axi_rready;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lsu_axi_rid;
    wire [63:0]                 lsu_axi_rdata;
    wire [1:0]                  lsu_axi_rresp;
    wire                        lsu_axi_rlast;

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    wire                        ifu_axi_awvalid;
    wire                        ifu_axi_awready;
    wire [`css_mcu0_RV_IFU_BUS_TAG-1:0]  ifu_axi_awid;
    wire [31:0]                 ifu_axi_awaddr;
    wire [3:0]                  ifu_axi_awregion;
    wire [7:0]                  ifu_axi_awlen;
    wire [2:0]                  ifu_axi_awsize;
    wire [1:0]                  ifu_axi_awburst;
    wire                        ifu_axi_awlock;
    wire [3:0]                  ifu_axi_awcache;
    wire [2:0]                  ifu_axi_awprot;
    wire [3:0]                  ifu_axi_awqos;

    wire                        ifu_axi_wvalid;
    wire                        ifu_axi_wready;
    wire [63:0]                 ifu_axi_wdata;
    wire [7:0]                  ifu_axi_wstrb;
    wire                        ifu_axi_wlast;

    wire                        ifu_axi_bvalid;
    wire                        ifu_axi_bready;
    wire [1:0]                  ifu_axi_bresp;
    wire [`css_mcu0_RV_IFU_BUS_TAG-1:0]  ifu_axi_bid;

    // AXI Read Channels
    wire                        ifu_axi_arvalid;
    wire                        ifu_axi_arready;
    wire [`css_mcu0_RV_IFU_BUS_TAG-1:0]  ifu_axi_arid;
    wire [31:0]                 ifu_axi_araddr;
    wire [3:0]                  ifu_axi_arregion;
    wire [7:0]                  ifu_axi_arlen;
    wire [2:0]                  ifu_axi_arsize;
    wire [1:0]                  ifu_axi_arburst;
    wire                        ifu_axi_arlock;
    wire [3:0]                  ifu_axi_arcache;
    wire [2:0]                  ifu_axi_arprot;
    wire [3:0]                  ifu_axi_arqos;

    wire                        ifu_axi_rvalid;
    wire                        ifu_axi_rready;
    wire [`css_mcu0_RV_IFU_BUS_TAG-1:0]  ifu_axi_rid;
    wire [63:0]                 ifu_axi_rdata;
    wire [1:0]                  ifu_axi_rresp;
    wire                        ifu_axi_rlast;

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    wire                        sb_axi_awvalid;
    wire                        sb_axi_awready;
    wire [`css_mcu0_RV_SB_BUS_TAG-1:0]   sb_axi_awid;
    wire [31:0]                 sb_axi_awaddr;
    wire [3:0]                  sb_axi_awregion;
    wire [7:0]                  sb_axi_awlen;
    wire [2:0]                  sb_axi_awsize;
    wire [1:0]                  sb_axi_awburst;
    wire                        sb_axi_awlock;
    wire [3:0]                  sb_axi_awcache;
    wire [2:0]                  sb_axi_awprot;
    wire [3:0]                  sb_axi_awqos;

    wire                        sb_axi_wvalid;
    wire                        sb_axi_wready;
    wire [63:0]                 sb_axi_wdata;
    wire [7:0]                  sb_axi_wstrb;
    wire                        sb_axi_wlast;

    wire                        sb_axi_bvalid;
    wire                        sb_axi_bready;
    wire [1:0]                  sb_axi_bresp;
    wire [`css_mcu0_RV_SB_BUS_TAG-1:0]   sb_axi_bid;

    // AXI Read Channels
    wire                        sb_axi_arvalid;
    wire                        sb_axi_arready;
    wire [`css_mcu0_RV_SB_BUS_TAG-1:0]   sb_axi_arid;
    wire [31:0]                 sb_axi_araddr;
    wire [3:0]                  sb_axi_arregion;
    wire [7:0]                  sb_axi_arlen;
    wire [2:0]                  sb_axi_arsize;
    wire [1:0]                  sb_axi_arburst;
    wire                        sb_axi_arlock;
    wire [3:0]                  sb_axi_arcache;
    wire [2:0]                  sb_axi_arprot;
    wire [3:0]                  sb_axi_arqos;

    wire                        sb_axi_rvalid;
    wire                        sb_axi_rready;
    wire [`css_mcu0_RV_SB_BUS_TAG-1:0]   sb_axi_rid;
    wire [63:0]                 sb_axi_rdata;
    wire [1:0]                  sb_axi_rresp;
    wire                        sb_axi_rlast;

   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
    wire                        dma_axi_awvalid;
    wire                        dma_axi_awready;
    wire [`css_mcu0_RV_DMA_BUS_TAG-1:0]  dma_axi_awid;
    wire [31:0]                 dma_axi_awaddr;
    wire [2:0]                  dma_axi_awsize;
    wire [2:0]                  dma_axi_awprot;
    wire [7:0]                  dma_axi_awlen;
    wire [1:0]                  dma_axi_awburst;


    wire                        dma_axi_wvalid;
    wire                        dma_axi_wready;
    wire [63:0]                 dma_axi_wdata;
    wire [7:0]                  dma_axi_wstrb;
    wire                        dma_axi_wlast;

    wire                        dma_axi_bvalid;
    wire                        dma_axi_bready;
    wire [1:0]                  dma_axi_bresp;
    wire [`css_mcu0_RV_DMA_BUS_TAG-1:0]  dma_axi_bid;

    // AXI Read Channels
    wire                        dma_axi_arvalid;
    wire                        dma_axi_arready;
    wire [`css_mcu0_RV_DMA_BUS_TAG-1:0]  dma_axi_arid;
    wire [31:0]                 dma_axi_araddr;
    wire [2:0]                  dma_axi_arsize;
    wire [2:0]                  dma_axi_arprot;
    wire [7:0]                  dma_axi_arlen;
    wire [1:0]                  dma_axi_arburst;

    wire                        dma_axi_rvalid;
    wire                        dma_axi_rready;
    wire [`css_mcu0_RV_DMA_BUS_TAG-1:0]  dma_axi_rid;
    wire [63:0]                 dma_axi_rdata;
    wire [1:0]                  dma_axi_rresp;
    wire                        dma_axi_rlast;

    wire                        lmem_axi_arvalid;
    wire                        lmem_axi_arready;

    wire                        lmem_axi_rvalid;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lmem_axi_rid;
    wire [1:0]                  lmem_axi_rresp;
    wire [63:0]                 lmem_axi_rdata;
    wire                        lmem_axi_rlast;
    wire                        lmem_axi_rready;

    wire                        lmem_axi_awvalid;
    wire                        lmem_axi_awready;

    wire                        lmem_axi_wvalid;
    wire                        lmem_axi_wready;

    wire [1:0]                  lmem_axi_bresp;
    wire                        lmem_axi_bvalid;
    wire [`css_mcu0_RV_LSU_BUS_TAG-1:0]  lmem_axi_bid;
    wire                        lmem_axi_bready;
`endif

// ----------------- MCI Connections within Subsystem -----------------------
         logic                             mcu_rst_b;
         logic                             mcu_cptra_rst_b;


// ----------------- MCI Connections LCC Connections -----------------------
         logic                             lcc_to_mci_lc_done;
         logic                             mci_to_lcc_init_req;
         pwrmgr_pkg::pwr_lc_req_t          lcc_init_req;

// ----------------- MCI OTP Connections -----------------------------------
         logic                             mci_to_otp_ctrl_init_req;
         logic                             otp_ctrl_to_mci_otp_ctrl_done;
         pwrmgr_pkg::pwr_otp_req_t         otp_ctrl_init_req;


//--------------------------MCI&LCC Gasket Signal Def---------------------
        // Inputs from LCC
         otp_ctrl_pkg::lc_otp_program_req_t           from_lcc_to_otp_program_i;
         lc_ctrl_pkg::lc_tx_t                         lc_dft_en_i;
         lc_ctrl_pkg::lc_tx_t                         lc_hw_debug_en_i;
         // Inputs from OTP_Ctrl
         otp_ctrl_pkg::otp_lc_data_t                  from_otp_to_lcc_program_i;
         // Inputs from Caliptra_Core
         logic                                         ss_dbg_manuf_enable   ; 
         logic [63:0]                                  ss_soc_dbg_unlock_level;
      
      
         soc_ifc_pkg::security_state_t                mci_cptra_security_state;
      
         logic intr_otp_operation_done;
         logic        mci_mcu_nmi_int;
         logic [31:0] mci_mcu_nmi_vector;
         logic mci_mcu_timer_int;

         // ----------------- FC to Caliptra-Core ports -----------------------
         otp_ctrl_part_pkg::otp_broadcast_t from_otp_to_clpt_core_broadcast; // This is a struct data type
         // broadcasted by fuse controller
         logic uds_field_entrpy_valid;
         logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed; 
         logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] cptra_obf_field_entropy;
         // --------------------------------------------------------------------

    // tie offs
     assign reset_vector = `css_mcu0_RV_RESET_VEC;

    // Fuse controller output is re-organized to feed caliptra-core with its fuse values and valid signal.
     assign uds_field_entrpy_valid = (from_otp_to_clpt_core_broadcast.valid == lc_ctrl_pkg::On) ? 1'b1 : 1'b0;
     always_comb begin: uds_fe_fuse_assignment
        for (int i=0; i<`CLP_OBF_UDS_DWORDS; i++ ) begin
            cptra_obf_uds_seed[i] = from_otp_to_clpt_core_broadcast.secret_manuf_partition_data.uds_seed[i*32 +: 32];
        end
        {cptra_obf_field_entropy[1], cptra_obf_field_entropy[0]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_0_data.field_entropy_0;
        {cptra_obf_field_entropy[3], cptra_obf_field_entropy[2]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_1_data.field_entropy_1;
        {cptra_obf_field_entropy[5], cptra_obf_field_entropy[4]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_2_data.field_entropy_2;
        {cptra_obf_field_entropy[7], cptra_obf_field_entropy[6]} = from_otp_to_clpt_core_broadcast.secret_prod_partition_3_data.field_entropy_3;
     end
    //=========================================================================-
    // Caliptra DUT instance
    //=========================================================================-
    caliptra_top caliptra_top_dut (
        .clk                        (cptra_ss_clk),
        .cptra_pwrgood              (cptra_ss_pwrgood),
        .cptra_rst_b                (mcu_cptra_rst_b),

        .cptra_obf_key              (cptra_obf_key     ),
        .cptra_obf_uds_seed_vld     (uds_field_entrpy_valid), //TODO
        .cptra_obf_uds_seed         (cptra_obf_uds_seed), 
        .cptra_obf_field_entropy_vld(uds_field_entrpy_valid), 
        .cptra_obf_field_entropy    (cptra_obf_field_entropy), 
        .cptra_csr_hmac_key         (cptra_csr_hmac_key),

        .jtag_tck   (cptra_core_jtag_tck   ),
        .jtag_tdi   (cptra_core_jtag_tdi   ),
        .jtag_tms   (cptra_core_jtag_tms   ),
        .jtag_trst_n(cptra_core_jtag_trst_n),
        .jtag_tdo   (cptra_core_jtag_tdo   ),
        .jtag_tdoEn (cptra_core_jtag_tdoEn ),
        
        //SoC AXI Interface
        .s_axi_w_if(cptra_core_s_axi_if.w_sub),
        .s_axi_r_if(cptra_core_s_axi_if.r_sub),

        //AXI DMA Interface
        .m_axi_w_if(cptra_core_m_axi_if.w_mgr),
        .m_axi_r_if(cptra_core_m_axi_if.r_mgr),

        .el2_mem_export(cptra_core_el2_mem_export),

        .ready_for_fuses(ready_for_fuses),
        .ready_for_mb_processing(ready_for_mb_processing),
        .ready_for_runtime(),

        .mbox_sram_cs(cptra_core_mbox_sram_cs),
        .mbox_sram_we(cptra_core_mbox_sram_we),
        .mbox_sram_addr(cptra_core_mbox_sram_addr),
        .mbox_sram_wdata(cptra_core_mbox_sram_wdata),
        .mbox_sram_rdata(cptra_core_mbox_sram_rdata),
            
        .imem_cs(cptra_core_imem_cs),
        .imem_addr(cptra_core_imem_addr),
        .imem_rdata(cptra_core_imem_rdata),

        .mailbox_data_avail(mailbox_data_avail),
        .mailbox_flow_done(),
        .BootFSM_BrkPoint(BootFSM_BrkPoint),

        .recovery_data_avail(1'b1/*TODO*/),
        .recovery_image_activated(1'b0/*TODO*/),

        //SoC Interrupts
        .cptra_error_fatal    (cptra_error_fatal    ),
        .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
        .etrng_req             (cptra_core_etrng_req),
        .itrng_data            (cptra_core_itrng_data),
        .itrng_valid           (cptra_core_itrng_valid),
`else
        .etrng_req             (    ),
        .itrng_data            (4'b0),
        .itrng_valid           (1'b0),
`endif

        // Subsystem mode straps
        .strap_ss_caliptra_base_addr                            (64'h0),
        .strap_ss_mci_base_addr                                 (64'h0),
        .strap_ss_recovery_ifc_base_addr                        (64'h0),
        .strap_ss_otp_fc_base_addr                              (64'h0),
        .strap_ss_uds_seed_base_addr                            (64'h0),
        .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(32'h0),
        .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes       (32'h0),
        .strap_ss_strap_generic_0                               (32'h0),
        .strap_ss_strap_generic_1                               (32'h0),
        .strap_ss_strap_generic_2                               (32'h0),
        .strap_ss_strap_generic_3                               (32'h0),
        .ss_debug_intent                                        (1'b0 ),

        // Subsystem mode debug outputs
        .ss_dbg_manuf_enable(ss_dbg_manuf_enable),
        .ss_soc_dbg_unlock_level(ss_soc_dbg_unlock_level),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(),

        .generic_input_wires(cptra_core_generic_input_wires),
        .generic_output_wires(cptra_core_generic_output_wires),

        .security_state(mci_cptra_security_state),
        .scan_mode     (scan_mode)
    );


    logic mci_intr;

    //FIXME define these somewhere for integrators
    // Interrupt Assignments
    // NOTE Vector 0 is reserved by VeeR
    `define VEER_INTR_VEC_MCI                 1
    `define VEER_INTR_VEC_CLP_MBOX_DATA_AVAIL 2
    `define VEER_INTR_VEC_I3C                 3
    `define VEER_INTR_VEC_FC                  4
    
    //Interrupt connections
    always_comb begin
        ext_int = '0;
        ext_int[`VEER_INTR_VEC_MCI -1]                 = mci_intr;
        ext_int[`VEER_INTR_VEC_CLP_MBOX_DATA_AVAIL -1] = mailbox_data_avail;
        ext_int[`VEER_INTR_VEC_I3C -1]                 = 0;
        ext_int[`VEER_INTR_VEC_FC  -1]                 = intr_otp_operation_done;
        //ext_int = ext_int_tb; //drive from tb if needed
    end

    //=========================================================================-
    // MCU instance
    //=========================================================================-
    mcu_top rvtop_wrapper (
        .rst_l                  ( mcu_rst_b ),
        .dbg_rst_l              ( cptra_ss_pwrgood ), //FIXME same as caliptra?
        .clk                    ( cptra_ss_clk ),
        .rst_vec                ( reset_vector[31:1]),
        .nmi_int                ( mci_mcu_nmi_int),
        .nmi_vec                ( mci_mcu_nmi_vector[31:1]),

        //-------------------------- LSU AXI signals--------------------------
        // // AXI Write Channels

        .lsu_axi_awvalid        (mcu_lsu_m_axi_if.awvalid),
        .lsu_axi_awready        (mcu_lsu_m_axi_if.awready),
        .lsu_axi_awid           (mcu_lsu_m_axi_if.awid), 
        .lsu_axi_awaddr         (mcu_lsu_m_axi_if.awaddr[31:0]),
        .lsu_axi_awregion       (),//(mcu_lsu_m_axi_if.awregion),
        .lsu_axi_awlen          (mcu_lsu_m_axi_if.awlen),
        .lsu_axi_awsize         (mcu_lsu_m_axi_if.awsize),
        .lsu_axi_awburst        (mcu_lsu_m_axi_if.awburst),
        .lsu_axi_awlock         (),//(mcu_lsu_m_axi_if.awlock[0]),
        .lsu_axi_awcache        (),//(mcu_lsu_m_axi_if.awcache),
        .lsu_axi_awprot         (),//(mcu_lsu_m_axi_if.awprot),
        .lsu_axi_awqos          (),//(mcu_lsu_m_axi_if.awqos),

        .lsu_axi_wvalid         (mcu_lsu_m_axi_if.wvalid),
        .lsu_axi_wready         (mcu_lsu_m_axi_if.wready),
        .lsu_axi_wdata          (mcu_lsu_m_axi_if.wdata),
        .lsu_axi_wstrb          (mcu_lsu_m_axi_if.wstrb),
        .lsu_axi_wlast          (mcu_lsu_m_axi_if.wlast),

        .lsu_axi_bvalid         (mcu_lsu_m_axi_if.bvalid),
        .lsu_axi_bready         (mcu_lsu_m_axi_if.bready),
        .lsu_axi_bresp          (mcu_lsu_m_axi_if.bresp),
        .lsu_axi_bid            (mcu_lsu_m_axi_if.bid[pt.LSU_BUS_TAG-1:0]),

        .lsu_axi_arvalid        (mcu_lsu_m_axi_if.arvalid),
        .lsu_axi_arready        (mcu_lsu_m_axi_if.arready),
        .lsu_axi_arid           (mcu_lsu_m_axi_if.arid[pt.LSU_BUS_TAG-1:0]),
        .lsu_axi_araddr         (mcu_lsu_m_axi_if.araddr[31:0]),
        .lsu_axi_arregion       (),//(mcu_lsu_m_axi_if.arregion),
        .lsu_axi_arlen          (mcu_lsu_m_axi_if.arlen),
        .lsu_axi_arsize         (mcu_lsu_m_axi_if.arsize),
        .lsu_axi_arburst        (mcu_lsu_m_axi_if.arburst),
        .lsu_axi_arlock         (),//(mcu_lsu_m_axi_if.arlock[0]),
        .lsu_axi_arcache        (),//(mcu_lsu_m_axi_if.arcache),
        .lsu_axi_arprot         (),//(mcu_lsu_m_axi_if.arprot),
        .lsu_axi_arqos          (),//(mcu_lsu_m_axi_if.arqos),

        .lsu_axi_rvalid         (mcu_lsu_m_axi_if.rvalid),
        .lsu_axi_rready         (mcu_lsu_m_axi_if.rready),
        .lsu_axi_rid            (mcu_lsu_m_axi_if.rid[pt.LSU_BUS_TAG-1:0]),
        .lsu_axi_rdata          (mcu_lsu_m_axi_if.rdata),
        .lsu_axi_rresp          (mcu_lsu_m_axi_if.rresp),
        .lsu_axi_rlast          (mcu_lsu_m_axi_if.rlast),

        //-------------------------- IFU AXI signals--------------------------
        // AXI Write Channels

        .ifu_axi_awvalid        ( mcu_ifu_m_axi_if.awvalid ),
        .ifu_axi_awready        ( mcu_ifu_m_axi_if.awready ),
        .ifu_axi_awid           ( mcu_ifu_m_axi_if.awid[pt.IFU_BUS_TAG-1:0]    ),
        .ifu_axi_awaddr         ( mcu_ifu_m_axi_if.awaddr[31:0]  ),
        .ifu_axi_awregion       (),//( mcu_ifu_m_axi_if.awregion),
        .ifu_axi_awlen          ( mcu_ifu_m_axi_if.awlen   ),
        .ifu_axi_awsize         ( mcu_ifu_m_axi_if.awsize  ),
        .ifu_axi_awburst        ( mcu_ifu_m_axi_if.awburst ),
        .ifu_axi_awlock         ( mcu_ifu_m_axi_if.awlock[0]  ),
        .ifu_axi_awcache        (),//( mcu_ifu_m_axi_if.awcache ),
        .ifu_axi_awprot         (),//( mcu_ifu_m_axi_if.awprot  ),
        .ifu_axi_awqos          (),//( mcu_ifu_m_axi_if.awqos   ),

        .ifu_axi_wvalid         ( mcu_ifu_m_axi_if.wvalid  ),
        .ifu_axi_wready         ( mcu_ifu_m_axi_if.wready  ),
        .ifu_axi_wdata          ( mcu_ifu_m_axi_if.wdata   ),
        .ifu_axi_wstrb          ( mcu_ifu_m_axi_if.wstrb   ),
        .ifu_axi_wlast          ( mcu_ifu_m_axi_if.wlast   ),

        .ifu_axi_bvalid         ( mcu_ifu_m_axi_if.bvalid  ),
        .ifu_axi_bready         ( mcu_ifu_m_axi_if.bready  ),
        .ifu_axi_bresp          ( mcu_ifu_m_axi_if.bresp   ),
        .ifu_axi_bid            ( mcu_ifu_m_axi_if.bid[pt.IFU_BUS_TAG-1:0]     ),

        .ifu_axi_arvalid        ( mcu_ifu_m_axi_if.arvalid ),
        .ifu_axi_arready        ( mcu_ifu_m_axi_if.arready ),
        .ifu_axi_arid           ( mcu_ifu_m_axi_if.arid[pt.IFU_BUS_TAG-1:0]    ),
        .ifu_axi_araddr         ( mcu_ifu_m_axi_if.araddr[31:0]  ),
        .ifu_axi_arlen          ( mcu_ifu_m_axi_if.arlen   ),
        .ifu_axi_arsize         ( mcu_ifu_m_axi_if.arsize  ),
        .ifu_axi_arburst        ( mcu_ifu_m_axi_if.arburst ),
        .ifu_axi_arlock         (),//( mcu_ifu_m_axi_if.arlock[0]  ),
        .ifu_axi_arcache        (),//( mcu_ifu_m_axi_if.arcache ),
        .ifu_axi_arprot         (),//( mcu_ifu_m_axi_if.arprot  ),
        .ifu_axi_arqos          (),//( mcu_ifu_m_axi_if.arqos   ),
        .ifu_axi_arregion       (),//( mcu_ifu_m_axi_if.arregion),

        .ifu_axi_rvalid         ( mcu_ifu_m_axi_if.rvalid  ),
        .ifu_axi_rready         ( mcu_ifu_m_axi_if.rready  ),
        .ifu_axi_rid            ( mcu_ifu_m_axi_if.rid[pt.IFU_BUS_TAG-1:0]     ),
        .ifu_axi_rdata          ( mcu_ifu_m_axi_if.rdata   ),
        .ifu_axi_rresp          ( mcu_ifu_m_axi_if.rresp   ),
        .ifu_axi_rlast          ( mcu_ifu_m_axi_if.rlast   ),

        //-------------------------- SB AXI signals--------------------------
        // AXI Write Channels
        .sb_axi_awvalid         (sb_axi_awvalid),
        .sb_axi_awready         (sb_axi_awready),
        .sb_axi_awid            (sb_axi_awid),
        .sb_axi_awaddr          (sb_axi_awaddr),
        .sb_axi_awregion        (sb_axi_awregion),
        .sb_axi_awlen           (sb_axi_awlen),
        .sb_axi_awsize          (sb_axi_awsize),
        .sb_axi_awburst         (sb_axi_awburst),
        .sb_axi_awlock          (sb_axi_awlock),
        .sb_axi_awcache         (sb_axi_awcache),
        .sb_axi_awprot          (sb_axi_awprot),
        .sb_axi_awqos           (sb_axi_awqos),

        .sb_axi_wvalid          (sb_axi_wvalid),
        .sb_axi_wready          (sb_axi_wready),
        .sb_axi_wdata           (sb_axi_wdata),
        .sb_axi_wstrb           (sb_axi_wstrb),
        .sb_axi_wlast           (sb_axi_wlast),

        .sb_axi_bvalid          (sb_axi_bvalid),
        .sb_axi_bready          (sb_axi_bready),
        .sb_axi_bresp           (sb_axi_bresp),
        .sb_axi_bid             (sb_axi_bid),

        .sb_axi_arvalid         (sb_axi_arvalid),
        .sb_axi_arready         (sb_axi_arready),
        .sb_axi_arid            (sb_axi_arid),
        .sb_axi_araddr          (sb_axi_araddr),
        .sb_axi_arregion        (sb_axi_arregion),
        .sb_axi_arlen           (sb_axi_arlen),
        .sb_axi_arsize          (sb_axi_arsize),
        .sb_axi_arburst         (sb_axi_arburst),
        .sb_axi_arlock          (sb_axi_arlock),
        .sb_axi_arcache         (sb_axi_arcache),
        .sb_axi_arprot          (sb_axi_arprot),
        .sb_axi_arqos           (sb_axi_arqos),

        .sb_axi_rvalid          (sb_axi_rvalid),
        .sb_axi_rready          (sb_axi_rready),
        .sb_axi_rid             (sb_axi_rid),
        .sb_axi_rdata           (sb_axi_rdata),
        .sb_axi_rresp           (sb_axi_rresp),
        .sb_axi_rlast           (sb_axi_rlast),

        //-------------------------- DMA AXI signals--------------------------
        // AXI Write Channels
        .dma_axi_awvalid        (mcu_dma_s_axi_if.awvalid),
        .dma_axi_awready        (mcu_dma_s_axi_if.awready),
        .dma_axi_awid           (mcu_dma_s_axi_if.awid[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_awaddr         (mcu_dma_s_axi_if.awaddr[31:0]),
        .dma_axi_awsize         (mcu_dma_s_axi_if.awsize),
        .dma_axi_awprot         ('0),//(mcu_dma_s_axi_if.awprot),
        .dma_axi_awlen          (mcu_dma_s_axi_if.awlen),
        .dma_axi_awburst        (mcu_dma_s_axi_if.awburst),

        .dma_axi_wvalid         (mcu_dma_s_axi_if.wvalid),
        .dma_axi_wready         (mcu_dma_s_axi_if.wready),
        .dma_axi_wdata          (mcu_dma_s_axi_if.wdata),
        .dma_axi_wstrb          (mcu_dma_s_axi_if.wstrb),
        .dma_axi_wlast          (mcu_dma_s_axi_if.wlast),

        .dma_axi_bvalid         (mcu_dma_s_axi_if.bvalid),
        .dma_axi_bready         (mcu_dma_s_axi_if.bready),
        .dma_axi_bresp          (mcu_dma_s_axi_if.bresp),
        .dma_axi_bid            (mcu_dma_s_axi_if.bid[pt.DMA_BUS_TAG-1:0]),

        .dma_axi_arvalid        (mcu_dma_s_axi_if.arvalid),
        .dma_axi_arready        (mcu_dma_s_axi_if.arready),
        .dma_axi_arid           (mcu_dma_s_axi_if.arid[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_araddr         (mcu_dma_s_axi_if.araddr[31:0]),
        .dma_axi_arsize         (mcu_dma_s_axi_if.arsize),
        .dma_axi_arprot         ('0),//(mcu_dma_s_axi_if.arprot),
        .dma_axi_arlen          (mcu_dma_s_axi_if.arlen),
        .dma_axi_arburst        (mcu_dma_s_axi_if.arburst),

        .dma_axi_rvalid         (mcu_dma_s_axi_if.rvalid),
        .dma_axi_rready         (mcu_dma_s_axi_if.rready),
        .dma_axi_rid            (mcu_dma_s_axi_if.rid[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_rdata          (mcu_dma_s_axi_if.rdata),
        .dma_axi_rresp          (mcu_dma_s_axi_if.rresp),
        .dma_axi_rlast          (mcu_dma_s_axi_if.rlast),

        .timer_int              ( mci_mcu_timer_int ),
        .soft_int               ( soft_int ),
        .extintsrc_req          ( ext_int ),

        .lsu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .ifu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .dbg_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
        .dma_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

        .trace_rv_i_insn_ip     (),//FIXME future (trace_rv_i_insn_ip),
        .trace_rv_i_address_ip  (),//FIXME future (trace_rv_i_address_ip),
        .trace_rv_i_valid_ip    (),//FIXME future (trace_rv_i_valid_ip),
        .trace_rv_i_exception_ip(),//FIXME future (trace_rv_i_exception_ip),
        .trace_rv_i_ecause_ip   (),//FIXME future (trace_rv_i_ecause_ip),
        .trace_rv_i_interrupt_ip(),//FIXME future (trace_rv_i_interrupt_ip),
        .trace_rv_i_tval_ip     (),//FIXME future (trace_rv_i_tval_ip),

        .jtag_tck               ( 1'b0  ),
        .jtag_tms               ( 1'b0  ),
        .jtag_tdi               ( 1'b0  ),
        .jtag_trst_n            ( 1'b0  ),
        .jtag_tdo               ( jtag_tdo ),
        .jtag_tdoEn             (),

        .mpc_debug_halt_ack     ( mpc_debug_halt_ack),
        .mpc_debug_halt_req     ( 1'b0),
        .mpc_debug_run_ack      ( mpc_debug_run_ack),
        .mpc_debug_run_req      ( 1'b1),
        .mpc_reset_run_req      ( 1'b1),             // Start running after reset
         .debug_brkpt_status    (debug_brkpt_status),

        .i_cpu_halt_req         ( 1'b0  ),    // Async halt req to CPU
        .o_cpu_halt_ack         ( o_cpu_halt_ack ),    // core response to halt
        .o_cpu_halt_status      ( o_cpu_halt_status ), // 1'b1 indicates core is halted
        .i_cpu_run_req          ( 1'b0  ),     // Async restart req to CPU
        .o_debug_mode_status    (o_debug_mode_status),
        .o_cpu_run_ack          ( o_cpu_run_ack ),     // Core response to run req

        .dec_tlu_perfcnt0       (),
        .dec_tlu_perfcnt1       (),
        .dec_tlu_perfcnt2       (),
        .dec_tlu_perfcnt3       (),

        .mem_clk                (css_mcu0_el2_mem_export.clk),

        .iccm_clken             (css_mcu0_el2_mem_export.iccm_clken),
        .iccm_wren_bank         (css_mcu0_el2_mem_export.iccm_wren_bank),
        .iccm_addr_bank         (css_mcu0_el2_mem_export.iccm_addr_bank),
        .iccm_bank_wr_data      (css_mcu0_el2_mem_export.iccm_bank_wr_data),
        .iccm_bank_wr_ecc       (css_mcu0_el2_mem_export.iccm_bank_wr_ecc),
        .iccm_bank_dout         (css_mcu0_el2_mem_export.iccm_bank_dout),
        .iccm_bank_ecc          (css_mcu0_el2_mem_export.iccm_bank_ecc),

        .dccm_clken             (css_mcu0_el2_mem_export.dccm_clken),
        .dccm_wren_bank         (css_mcu0_el2_mem_export.dccm_wren_bank),
        .dccm_addr_bank         (css_mcu0_el2_mem_export.dccm_addr_bank),
        .dccm_wr_data_bank      (css_mcu0_el2_mem_export.dccm_wr_data_bank),
        .dccm_wr_ecc_bank       (css_mcu0_el2_mem_export.dccm_wr_ecc_bank),
        .dccm_bank_dout         (css_mcu0_el2_mem_export.dccm_bank_dout),
        .dccm_bank_ecc          (css_mcu0_el2_mem_export.dccm_bank_ecc),

        // ICache Export Interface
        // ICache Data
        .ic_b_sb_wren              (css_mcu0_el2_mem_export.ic_b_sb_wren              ),
        .ic_b_sb_bit_en_vec        (css_mcu0_el2_mem_export.ic_b_sb_bit_en_vec        ),
        .ic_sb_wr_data             (css_mcu0_el2_mem_export.ic_sb_wr_data             ),
        .ic_rw_addr_bank_q         (css_mcu0_el2_mem_export.ic_rw_addr_bank_q         ),
        .ic_bank_way_clken_final   (css_mcu0_el2_mem_export.ic_bank_way_clken_final   ),
        .ic_bank_way_clken_final_up(css_mcu0_el2_mem_export.ic_bank_way_clken_final_up),
        .wb_packeddout_pre         (css_mcu0_el2_mem_export.wb_packeddout_pre         ),
        .wb_dout_pre_up            (css_mcu0_el2_mem_export.wb_dout_pre_up            ),
        // ICache Tag
        .ic_tag_clken_final        (css_mcu0_el2_mem_export.ic_tag_clken_final        ),
        .ic_tag_wren_q             (css_mcu0_el2_mem_export.ic_tag_wren_q             ),
        .ic_tag_wren_biten_vec     (css_mcu0_el2_mem_export.ic_tag_wren_biten_vec     ),
        .ic_tag_wr_data            (css_mcu0_el2_mem_export.ic_tag_wr_data            ),
        .ic_rw_addr_q              (css_mcu0_el2_mem_export.ic_rw_addr_q              ),
        .ic_tag_data_raw_pre       (css_mcu0_el2_mem_export.ic_tag_data_raw_pre       ),
        .ic_tag_data_raw_packed_pre(css_mcu0_el2_mem_export.ic_tag_data_raw_packed_pre),

        .iccm_ecc_single_error  (),
        .iccm_ecc_double_error  (),
        .dccm_ecc_single_error  (),
        .dccm_ecc_double_error  (),

        .core_id                ('0),
        .scan_mode              ( 1'b0 ),         // To enable scan mode
        .mbist_mode             ( 1'b0 ),        // to enable mbist

        .dmi_core_enable        (),
        .dmi_uncore_enable      (),
        .dmi_uncore_en          (),
        .dmi_uncore_wr_en       (),
        .dmi_uncore_addr        (),
        .dmi_uncore_wdata       (),
        .dmi_uncore_rdata       (),
        .dmi_active             ()

    );

    //=========================================================================-
    // I3C-Core Instance
    //=========================================================================-

    i3c_wrapper #(
`ifdef I3C_USE_AHB
        .AhbDataWidth(`AHB_DATA_WIDTH),
        .AhbAddrWidth(`AHB_ADDR_WIDTH)
`elsif I3C_USE_AXI
        .AxiDataWidth(`AXI_DATA_WIDTH),
        .AxiAddrWidth(`AXI_ADDR_WIDTH),
        .AxiUserWidth(`AXI_USER_WIDTH),
        .AxiIdWidth  (`AXI_ID_WIDTH  )
`endif
    ) i3c (
        .clk_i (cptra_ss_clk),
        .rst_ni(cptra_ss_rst_b),

`ifdef I3C_USE_AHB
        .haddr_i    (i3c_haddr    ),
        .hburst_i   (i3c_hburst   ),
        .hprot_i    (i3c_hprot    ),
        .hwdata_i   (i3c_hwdata   ),
        .hsel_i     (i3c_hsel     ),
        .hwstrb_i   (i3c_hwstrb   ),
        .hwrite_i   (i3c_hwrite   ),
        .hready_i   (i3c_hready   ),
        .htrans_i   (i3c_htrans   ),
        .hsize_i    (i3c_hsize    ),
        .hresp_o    (i3c_hresp    ),
        .hreadyout_o(i3c_hreadyout),
        .hrdata_o   (i3c_hrdata   ),
`elsif I3C_USE_AXI
        .arvalid_i  (i3c_s_axi_if.arvalid),
        .arready_o  (i3c_s_axi_if.arready),
        .arid_i     (i3c_s_axi_if.arid),
        .araddr_i   (i3c_s_axi_if.araddr[`AXI_ADDR_WIDTH:0]),
        .arsize_i   (i3c_s_axi_if.arsize),
        .aruser_i   (i3c_s_axi_if.aruser),
        .arlen_i    (i3c_s_axi_if.arlen),
        .arburst_i  (i3c_s_axi_if.arburst),
        .arlock_i   (i3c_s_axi_if.arlock[0]),
        .rvalid_o   (i3c_s_axi_if.rvalid),
        .rready_i   (i3c_s_axi_if.rready),
        .rid_o      (i3c_s_axi_if.rid),
        .rdata_o    (i3c_s_axi_if.rdata),
        .rresp_o    (i3c_s_axi_if.rresp),
        .rlast_o    (i3c_s_axi_if.rlast),
        .awvalid_i  (i3c_s_axi_if.awvalid),
        .awready_o  (i3c_s_axi_if.awready),
        .awid_i     (i3c_s_axi_if.awid),
        .awaddr_i   (i3c_s_axi_if.awaddr[`AXI_ADDR_WIDTH:0]),
        .awsize_i   (i3c_s_axi_if.awsize),
        .awuser_i   (i3c_s_axi_if.awuser),
        .awlen_i    (i3c_s_axi_if.awlen),
        .awburst_i  (i3c_s_axi_if.awburst),
        .awlock_i   (i3c_s_axi_if.awlock[0]),
        .wvalid_i   (i3c_s_axi_if.wvalid),
        .wready_o   (i3c_s_axi_if.wready),
        .wdata_i    (i3c_s_axi_if.wdata),
        .wstrb_i    (i3c_s_axi_if.wstrb),
        .wlast_i    (i3c_s_axi_if.wlast),
        .bvalid_o   (i3c_s_axi_if.bvalid),
        .bready_i   (i3c_s_axi_if.bready),
        .bresp_o    (i3c_s_axi_if.bresp),
        .bid_o      (i3c_s_axi_if.bid),
`endif
`ifdef VERILATOR
        .scl_i(scl_i),
        .sda_i(sda_i),
        .scl_o(scl_o),
        .sda_o(sda_o),
        .sel_od_pp_o(sel_od_pp_o)
`else
        .i3c_scl_io(i3c_scl_io),
        .i3c_sda_io(i3c_sda_io),

    // Recovery interface signals
    .recovery_payload_available_o(),
    .recovery_image_activated_o(),

    .peripheral_reset_o(),
    .peripheral_reset_done_i(),
    .escalated_reset_o()

    // TODO: Add interrupts
`endif
    );

    //=========================================================================
    // MCI Instance
    //=========================================================================

    logic mci_pwrgood;

    assign mci_pwrgood = 1'b1;

    mci_top #(
        // .MCI_BASE_ADDR(`SOC_MCI_REG_BASE_ADDR), //-- FIXME : Assign common paramter
        .AXI_DATA_WIDTH(32),
        .MCU_SRAM_SIZE_KB(256)
    ) mci_top_i (

        .clk(cptra_ss_clk),
        .mci_rst_b(cptra_ss_rst_b),
        .mci_pwrgood(mci_pwrgood),

        // MCI AXI Interface
        .s_axi_w_if(mci_s_axi_if.w_sub),
        .s_axi_r_if(mci_s_axi_if.r_sub),

        // MCI Master interface
        .m_axi_w_if(mci_m_axi_if.w_mgr),
        .m_axi_r_if(mci_m_axi_if.r_mgr),
        
        .strap_mcu_lsu_axi_user(32'hFFFF_FFFF),
        .strap_mcu_ifu_axi_user(32'hFFFF_FFFF),
        .strap_clp_axi_user(32'hFFFF_FFFF),
        .strap_prod_debug_unlock_pk_hash('1),
        // .strap_mcu_sram_access0_axi_user(32'hFFFF_FFFF),
        // .strap_mcu_sram_access1_axi_user(32'hFFFF_FFFF),

        .mcu_sram_fw_exec_region_lock(1'b1),

        .agg_error_fatal(1'b0),
        .agg_error_non_fatal(1'b0),

        // .cptra_error_fatal(1'b0),
        // .cptra_error_non_fatal(1'b0),

        .mci_error_fatal(),
        .mci_error_non_fatal(),

        .mci_generic_input_wires(64'h0),
        .mci_generic_output_wires(),

        .mcu_timer_int(mci_mcu_timer_int),
        .mci_intr(mci_intr),

        .strap_mcu_reset_vector(32'h0),
        .mcu_reset_vector(),
        .mcu_no_rom_config(1'b1),

        .nmi_intr(mci_mcu_nmi_int),
        .mcu_nmi_vector(mci_mcu_nmi_vector),

        .mcu_rst_b(mcu_rst_b),
        .cptra_rst_b(mcu_cptra_rst_b),

        .mci_boot_seq_brkpoint(1'b0),

        .lc_done(lcc_to_mci_lc_done), //output from lcc
        .lc_init(mci_to_lcc_init_req), //input to lcc
        // .lc_bus_integ_error_fatal(1'b0),
        // .lc_state_error_fatal(1'b0),
        // .lc_prog_error_fatal(1'b0),

        .fc_opt_done(otp_ctrl_to_mci_otp_ctrl_done), //output from otp
        .fc_opt_init(mci_to_otp_ctrl_init_req), //input to otp
        // .fc_intr_otp_error(1'b0),

        .mci_mcu_sram_req_if(mci_mcu_sram_req_if),
        .mci_mbox0_sram_req_if(mci_mbox0_sram_req_if),
        .mci_mbox1_sram_req_if(mci_mbox1_sram_req_if),


        .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
        .lc_dft_en_i(lc_dft_en_i),
        .lc_hw_debug_en_i(lc_hw_debug_en_i),
   // Inputs from OTP_Ctrl
        .from_otp_to_lcc_program_i(from_otp_to_lcc_program_i),
   // Inputs from Caliptra_Core
        .ss_dbg_manuf_enable_i(ss_dbg_manuf_enable), 
        .ss_soc_dbg_unlock_level_i(ss_soc_dbg_unlock_level),

   // Converted Signals from LCC to SoC
        .SOC_DFT_EN(SOC_DFT_EN),
        .SOC_HW_DEBUG_EN(SOC_HW_DEBUG_EN),

   // Converted Signals from LCC to Caliptra-core
        .security_state_o(mci_cptra_security_state)
    
    );

    //=========================================================================-
    // Life-cycle Controller Instance : 
    // 
    //=========================================================================-

    //--------------------------------------------------------------------------------------------
    // These are shared signals between fuse controller and lc controller
    logic [$bits(otp_ctrl_pkg::lc_otp_vendor_test_req_t)-1:0] lc_otp_vendor_test_o_tb;
    logic [$bits(otp_ctrl_pkg::lc_otp_vendor_test_rsp_t)-1:0] lc_otp_vendor_test_i_tb;
    logic [$bits(otp_ctrl_pkg::lc_otp_program_rsp_t)-1:0] lc_otp_program_i_tb;

    logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_creator_seed_sw_rw_en_tb;
    logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_owner_seed_sw_rw_en_tb;
    logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_seed_hw_rd_en_tb;
    logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_escalate_en_tb;
    logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_check_byp_en_tb;

    assign lc_otp_vendor_test_o_tb = otp_ctrl_pkg::lc_otp_vendor_test_req_t'(u_lc_ctrl.lc_otp_vendor_test_o);
    assign lc_otp_vendor_test_i_tb = otp_ctrl_pkg::lc_otp_vendor_test_rsp_t'(u_otp_ctrl.lc_otp_vendor_test_o);
    assign lc_otp_program_i_tb = otp_ctrl_pkg::lc_otp_program_rsp_t'(u_otp_ctrl.lc_otp_program_o);

    assign lc_creator_seed_sw_rw_en_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl.lc_creator_seed_sw_rw_en_o);
    assign lc_owner_seed_sw_rw_en_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl.lc_owner_seed_sw_rw_en_o);
    assign lc_seed_hw_rd_en_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl.lc_seed_hw_rd_en_o);
    assign lc_escalate_en_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl.lc_escalate_en_o);
    assign lc_check_byp_en_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl.lc_check_byp_en_o);

    //--------------------------------------------------------------------------------------------

    //--------------------------------------------------------------------------------------------

    assign lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(u_lc_ctrl.pwr_lc_o.lc_done);
    assign lcc_init_req.lc_init = mci_to_lcc_init_req; 

    lc_ctrl u_lc_ctrl (
            .clk_i(cptra_ss_clk),
            .rst_ni(cptra_ss_rst_b & fake_reset),
            .Allow_RMA_on_PPD(Allow_RMA_on_PPD),
            .axi_wr_req(lc_axi_wr_req),
            .axi_wr_rsp(lc_axi_wr_rsp),
            .axi_rd_req(lc_axi_rd_req),
            .axi_rd_rsp(lc_axi_rd_rsp),

            .jtag_i('0),
            .jtag_o(),
            
            .scan_rst_ni(lc_ctrl_scan_rst_ni),
            .scanmode_i(caliptra_prim_mubi_pkg::mubi4_t'(lc_ctrl_scanmode_i)),
            
            .alerts(lc_alerts_o),
            .esc_scrap_state0(esc_scrap_state0),
            .esc_scrap_state1(esc_scrap_state1),


            .pwr_lc_i(lcc_init_req),
            .pwr_lc_o(),

            .strap_en_override_o(),



        

            .lc_otp_vendor_test_o(),
            .lc_otp_vendor_test_i(otp_ctrl_pkg::lc_otp_vendor_test_rsp_t'(lc_otp_vendor_test_i_tb)),
            .lc_otp_program_o(from_lcc_to_otp_program_i),
            .lc_otp_program_i(otp_ctrl_pkg::lc_otp_program_rsp_t'(lc_otp_program_i_tb)),
            .otp_lc_data_i(otp_ctrl_pkg::otp_lc_data_t'(otp_lc_data)),
            .lc_dft_en_o(lc_dft_en_i),
            .lc_creator_seed_sw_rw_en_o(),
            .lc_owner_seed_sw_rw_en_o(),
            .lc_seed_hw_rd_en_o(),            
            .lc_escalate_en_o(),
            .lc_check_byp_en_o(),

            .lc_hw_debug_en_o(lc_hw_debug_en_i),
            .lc_cpu_en_o(),

            .lc_clk_byp_req_o(),
            .lc_clk_byp_ack_i(lc_ctrl_pkg::lc_tx_t'(lc_clk_byp_ack)),

            .otp_device_id_i('0),
            .otp_manuf_state_i('0),
            .hw_rev_o()
        );


    //=========================================================================-
    // Fuse Controller Instance : 
    // 
    //=========================================================================-
    
    // logic otp_lc_data_o_valid;

    logic    [otp_ctrl_reg_pkg::NumAlerts-1:0] fc_alerts;  

    caliptra_prim_mubi_pkg::mubi4_t scanmode_mubi;
    
    assign otp_ctrl_to_mci_otp_ctrl_done = pwrmgr_pkg::pwr_otp_rsp_t'(u_otp_ctrl.pwr_otp_o.otp_done);
    assign otp_ctrl_init_req.otp_init = mci_to_otp_ctrl_init_req; 

    otp_ctrl #(
        .MemInitFile ("otp-img.2048.vmem")
    ) u_otp_ctrl (
        .clk_i                      (cptra_ss_clk),
        .rst_ni                     (cptra_ss_rst_b & fake_reset),
        .clk_edn_i                  (),
        .rst_edn_ni                 (),
        .edn_o                      (),
        .edn_i                      (),

        .core_axi_wr_req            (core_axi_wr_req),
        .core_axi_wr_rsp            (core_axi_wr_rsp),
        .core_axi_rd_req            (core_axi_rd_req),
        .core_axi_rd_rsp            (core_axi_rd_rsp),
        
        // .prim_axi_wr_req            (prim_axi_wr_req),
        // .prim_axi_wr_rsp            (prim_axi_wr_rsp),
        // .prim_axi_rd_req            (prim_axi_rd_req),
        // .prim_axi_rd_rsp            (prim_axi_rd_rsp),

        .intr_otp_operation_done_o  (intr_otp_operation_done),
        .intr_otp_error_o           (),
        // .alert_rx_i                 (),
        // .alert_tx_o                 (),
        .alerts(fc_alerts),
        .obs_ctrl_i                 (),
        .otp_obs_o                  (),
        .otp_ast_pwr_seq_o          (),
        .otp_ast_pwr_seq_h_i        (),
        .pwr_otp_i                  (otp_ctrl_init_req),
        .pwr_otp_o                  (),

        .lc_otp_vendor_test_i(otp_ctrl_pkg::lc_otp_vendor_test_req_t'(lc_otp_vendor_test_o_tb)),
        .lc_otp_vendor_test_o(),
        .lc_otp_program_i(from_lcc_to_otp_program_i),
        .lc_otp_program_o(),

    .lc_creator_seed_sw_rw_en_i(lc_creator_seed_sw_rw_en_tb),
    .lc_owner_seed_sw_rw_en_i(lc_owner_seed_sw_rw_en_tb),
    .lc_seed_hw_rd_en_i(lc_seed_hw_rd_en_tb),
    .lc_dft_en_i(lc_dft_en_i),
    .lc_escalate_en_i(lc_escalate_en_tb),
    .lc_check_byp_en_i(lc_check_byp_en_tb),
    .otp_lc_data_o(from_otp_to_lcc_program_i),


        .otp_keymgr_key_o           (),
        .flash_otp_key_i            (),
        .flash_otp_key_o            (),
        .sram_otp_key_i             (),
        .sram_otp_key_o             (),
        .otbn_otp_key_i             (),
        .otbn_otp_key_o             (),
        .otp_broadcast_o            (from_otp_to_clpt_core_broadcast),
        .otp_ext_voltage_h_io       (),
        .scan_en_i                  (),
        .scan_rst_ni                (),
        .scanmode_i                 (scanmode_mubi),
        .cio_test_o                 (),
        .cio_test_en_o                   ()
	); 


    assign scanmode_mubi = scan_mode ? caliptra_prim_mubi_pkg::MuBi4True : caliptra_prim_mubi_pkg::MuBi4False;

    // assign otp_lc_data_o_valid = otp_lc_data_o.valid;

    // assign fuse_ctrl_rdy = 1;
    // De-assert cptra_rst_b only after fuse_ctrl has initialized
    logic cptra_rst_b; //fixme resets
    assign cptra_rst_b = cptra_ss_rst_b;//fuse_ctrl_rdy ? cptra_soc_bfm_rst_b : 1'b0;

endmodule
