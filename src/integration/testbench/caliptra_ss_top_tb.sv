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

`include "css_mcu0_common_defines.vh"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"
`include "i3c_defines.svh"
`include "soc_address_map_defines.svh"
`include "caliptra_ss_includes.svh"



module caliptra_ss_top_tb
#(
    `include "css_mcu0_el2_param.vh"
);

    import tb_top_pkg::*;
    import aaxi_pkg::*;
    import axi_pkg::*;
    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;
    import ai2c_pkg::*;
    import ai3c_pkg::*;
    import avery_pkg_test::*;
    import jtag_pkg::*;

    `include "caliptra_ss_assertion_overrides.svh"

`ifndef VERILATOR
    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width
`endif


    bit                         core_clk;    
    logic                       cptra_ss_pwrgood_i;
    logic                       cptra_ss_rst_b_i;
    logic                       cptra_rst_b;
    logic                       cptra_ss_mci_cptra_rst_b_o;

    logic        [31:0]         trace_rv_i_insn_ip;
    logic        [31:0]         trace_rv_i_address_ip;
    logic                       trace_rv_i_valid_ip;
    logic                       trace_rv_i_exception_ip;
    logic        [4:0]          trace_rv_i_ecause_ip;
    logic                       trace_rv_i_interrupt_ip;
    logic        [31:0]         trace_rv_i_tval_ip;

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


    mldsa_mem_if mldsa_memory_export();


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
         logic                                         ss_dbg_manuf_enable_i   ; 
         logic [63:0]                                  ss_soc_dbg_unlock_level_i;
      
      
         soc_ifc_pkg::security_state_t                security_state_o;

//---------------------------I3C---------------------------------------
         logic payload_available_o;
         logic image_activated_o;
      
//------------------------------------------------------------------------

    logic         cptra_ss_debug_intent_i;
    logic cptra_ss_soc_mcu_mbox0_data_avail;
    logic cptra_ss_soc_mcu_mbox1_data_avail;

    logic pwr_otp_init_i;
    logic cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i;
    logic cptra_ss_FIPS_ZEROIZATION_PPD_i;
    logic lcc_bfm_reset;

    //-- 
    logic                                 cptra_ss_soc_dft_en_o;
    logic                                 cptra_ss_soc_hw_debug_en_o;

    css_mcu0_el2_mem_if         cptra_ss_mcu0_el2_mem_export ();
    el2_mem_if                  cptra_ss_cptra_core_el2_mem_export ();        

    caliptra_ss_bfm_services_if i_caliptra_ss_bfm_services_if();

    logic fuse_ctrl_rdy;
    
    // -- Read clock frequency from file and set the clock accordingly using a case statement
    initial begin
        
        integer file;
        integer status;
        int frequency;
    
        // Open the file to read the clock frequency
        file = $fopen("caliptra_ss_clk_freq.cfg", "r");
        if (file == 0) begin
            $display("Error: Unable to open file caliptra_ss_clk_freq.cfg");
            $finish;
        end
    
        // Read the frequency from the file
        status = $fscanf(file, "%d", frequency);
        $fclose(file);
    
        if (status != 1) begin
            $display("Error: Failed to read clock frequency from file");
            $finish;
        end

        core_clk = 0;
        // Use a case statement to set the clock period based on the frequency
        case (frequency)
            160: forever core_clk = #(3.125) ~core_clk; // 160MHz -> 6.25ns period, 3.125ns half-period
            400: forever core_clk = #(1.25) ~core_clk;  // 400MHz -> 2.5ns period, 1.25ns half-period
            500: forever core_clk = #(1.0) ~core_clk;   // 500MHz -> 2.0ns period, 1.0ns half-period
            1000: forever core_clk = #(0.5) ~core_clk;   // 1000MHz -> 1.0ns period, 0.5ns half-period
            default: begin
                $display("Error: Unsupported frequency value %d in file", frequency);
                $finish;
            end
        endcase
    end


   //=========================================================================
   // AXI Interconnect
   //=========================================================================

    aaxi4_interconnect axi_interconnect(
        .core_clk (core_clk),
        .rst_l    (cptra_ss_rst_b_i)
    );

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH - 3),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) m_axi_bfm_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH - 3),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) m_axi_bfm_if_FIXME (.clk(core_clk), .rst_n(rst_l));
    // Cptra Mgr Axi Interface
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) cptra_ss_cptra_core_m_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // Cptra Sub AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_cptra_core_s_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // MCI Sub AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mci_s_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // MCU ROM Sub AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(64), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_rom_s_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // MCU LSU AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(64), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_lsu_m_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // MCU LSU AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(64), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_sb_m_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // MCU IFU AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(64), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_ifu_m_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // // MCU DMA AXI Interface
    // axi_if #(
    //     .AW(32), //-- FIXME : Assign a common paramter
    //     .DW(64), //-- FIXME : Assign a common paramter,
    //     .IW(`CALIPTRA_AXI_ID_WIDTH),
    //     .UW(`CALIPTRA_AXI_USER_WIDTH)
    // ) mcu_dma_s_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    // I3C AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_i3c_s_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

    axi_struct_pkg::axi_wr_req_t cptra_ss_lc_axi_wr_req_i;
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_lc_axi_wr_rsp_o;
    axi_struct_pkg::axi_rd_req_t cptra_ss_lc_axi_rd_req_i;
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_lc_axi_rd_rsp_o;

    axi_struct_pkg::axi_wr_req_t cptra_ss_otp_core_axi_wr_req_i;
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_otp_core_axi_wr_rsp_o;
    axi_struct_pkg::axi_rd_req_t cptra_ss_otp_core_axi_rd_req_i;
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_otp_core_axi_rd_rsp_o;

    logic fuse_core_axi_rd_is_upper_dw_latched;
    logic fuse_core_axi_wr_is_upper_dw_latched;
    logic lc_axi_rd_is_upper_dw_latched;
    logic lc_axi_wr_is_upper_dw_latched;

    `define SS_DATA_WIDTH_HACK_LOGIC_DEFINE(inf_name)\
        logic ``inf_name``_rd_is_upper_dw_latched;\
        logic ``inf_name``_wr_is_upper_dw_latched;

    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(cptra_ss_cptra_core_m_axi_if)
    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(cptra_ss_cptra_core_s_axi_if)
    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(m_axi_bfm_if)
    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(cptra_ss_mci_s_axi_if)
    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(cptra_ss_mcu_rom_s_axi_if)
    `SS_DATA_WIDTH_HACK_LOGIC_DEFINE(cptra_ss_i3c_s_axi_if)

    `define SS_DATA_WIDTH_HACK(inf_name, core_clk = core_clk, cptra_ss_rst_b_i = cptra_ss_rst_b_i)\
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)\
        if (!cptra_ss_rst_b_i)\
            ``inf_name``_wr_is_upper_dw_latched <= 0;\
        else if (``inf_name``.awvalid && ``inf_name``.awready)\
            ``inf_name``_wr_is_upper_dw_latched <= ``inf_name``.awaddr[2] && (``inf_name``.awsize < 3);\
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT``inf_name``, (``inf_name``.awvalid && ``inf_name``.awready) -> (``inf_name``.awsize < 3), core_clk, !cptra_ss_rst_b_i)\
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)\
        if (!cptra_ss_rst_b_i)\
            ``inf_name``_rd_is_upper_dw_latched <= 0;\
        else if (``inf_name``.arvalid && ``inf_name``.arready)\
            ``inf_name``_rd_is_upper_dw_latched <= ``inf_name``.araddr[2] && (``inf_name``.arsize < 3);\
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT``inf_name``, (``inf_name``.arvalid && ``inf_name``.arready) -> (``inf_name``.arsize < 3), core_clk, !cptra_ss_rst_b_i)
    

    `SS_DATA_WIDTH_HACK(cptra_ss_cptra_core_m_axi_if)
    `SS_DATA_WIDTH_HACK(cptra_ss_cptra_core_s_axi_if)
    `SS_DATA_WIDTH_HACK(m_axi_bfm_if)
    `SS_DATA_WIDTH_HACK(cptra_ss_mci_s_axi_if)
    `SS_DATA_WIDTH_HACK(cptra_ss_mcu_rom_s_axi_if)
    `SS_DATA_WIDTH_HACK(cptra_ss_i3c_s_axi_if)
        
    //These don't fit the macro FIXME LATER
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)
    if (!cptra_ss_rst_b_i)
        lc_axi_wr_is_upper_dw_latched <= 0;
    else if (cptra_ss_lc_axi_wr_req_i.awvalid && cptra_ss_lc_axi_wr_rsp_o.awready)
        lc_axi_wr_is_upper_dw_latched <= cptra_ss_lc_axi_wr_req_i.awaddr[2] && (cptra_ss_lc_axi_wr_req_i.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT_LC, (cptra_ss_lc_axi_wr_req_i.awvalid && cptra_ss_lc_axi_wr_rsp_o.awready) -> (cptra_ss_lc_axi_wr_req_i.awsize < 3), core_clk, !cptra_ss_rst_b_i)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)
        if (!cptra_ss_rst_b_i)
            lc_axi_rd_is_upper_dw_latched <= 0;
        else if (cptra_ss_lc_axi_rd_req_i.arvalid && cptra_ss_lc_axi_rd_rsp_o.arready)
            lc_axi_rd_is_upper_dw_latched <= cptra_ss_lc_axi_rd_req_i.araddr[2] && (cptra_ss_lc_axi_rd_req_i.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT_LC, (cptra_ss_lc_axi_rd_req_i.arvalid && cptra_ss_lc_axi_rd_rsp_o.arready) -> (cptra_ss_lc_axi_rd_req_i.arsize < 3), core_clk, !cptra_ss_rst_b_i)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)
        if (!cptra_ss_rst_b_i)
            fuse_core_axi_wr_is_upper_dw_latched <= 0;
        else if (cptra_ss_otp_core_axi_wr_req_i.awvalid && cptra_ss_otp_core_axi_wr_rsp_o.awready)
            fuse_core_axi_wr_is_upper_dw_latched <= cptra_ss_otp_core_axi_wr_req_i.awaddr[2] && (cptra_ss_otp_core_axi_wr_req_i.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT_OTP, (cptra_ss_otp_core_axi_wr_req_i.awvalid && cptra_ss_otp_core_axi_wr_rsp_o.awready) -> (cptra_ss_otp_core_axi_wr_req_i.awsize < 3), core_clk, !cptra_ss_rst_b_i)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge cptra_ss_rst_b_i)
        if (!cptra_ss_rst_b_i)
            fuse_core_axi_rd_is_upper_dw_latched <= 0;
        else if (cptra_ss_otp_core_axi_rd_req_i.arvalid && cptra_ss_otp_core_axi_rd_rsp_o.arready)
            fuse_core_axi_rd_is_upper_dw_latched <= cptra_ss_otp_core_axi_rd_req_i.araddr[2] && (cptra_ss_otp_core_axi_rd_req_i.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT_OTP, (cptra_ss_otp_core_axi_rd_req_i.arvalid && cptra_ss_otp_core_axi_rd_rsp_o.arready) -> (cptra_ss_otp_core_axi_rd_req_i.arsize < 3), core_clk, !cptra_ss_rst_b_i)

    // AXI Interconnect upper address tie to 0
    assign axi_interconnect.mintf_arr[0].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[0].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[1].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[1].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[2].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[2].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[3].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[3].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[4].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[4].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[2].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[2].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;

    // Slave port 0 disconnection.
    assign axi_interconnect.sintf_arr[0].ARREADY = 1'b0;
    assign axi_interconnect.sintf_arr[0].RVALID = 1'b0;
    assign axi_interconnect.sintf_arr[0].RDATA = 64'h0;
    assign axi_interconnect.sintf_arr[0].RRESP = 2'b0;
    assign axi_interconnect.sintf_arr[0].RID = 8'h0;
    assign axi_interconnect.sintf_arr[0].RLAST = 1'b0;
    assign axi_interconnect.sintf_arr[0].RUSER = '0;

    assign axi_interconnect.sintf_arr[0].AWREADY = 1'b0;
    assign axi_interconnect.sintf_arr[0].WREADY = 1'b0;
    assign axi_interconnect.sintf_arr[0].BVALID = 1'b0;
    assign axi_interconnect.sintf_arr[0].BRESP = 2'b0;
    assign axi_interconnect.sintf_arr[0].BUSER = '0;

    assign axi_interconnect.sintf_arr[0].BID = 8'h0;

    genvar ii;
    generate
        // Undriven ports on all Managers
        for(ii = 0; ii < AAXI_INTC_MASTER_CNT; ii++) begin
            assign axi_interconnect.mintf_arr[ii].ARCACHE  = '0;
            assign axi_interconnect.mintf_arr[ii].ARPROT   = '0;
            assign axi_interconnect.mintf_arr[ii].ARQOS    = '0;
            assign axi_interconnect.mintf_arr[ii].ARREGION = '0;
            assign axi_interconnect.mintf_arr[ii].AWCACHE  = '0;
            assign axi_interconnect.mintf_arr[ii].AWPROT   = '0;
            assign axi_interconnect.mintf_arr[ii].AWQOS    = '0;
            assign axi_interconnect.mintf_arr[ii].AWREGION = '0;
        end
    endgenerate

    
    //Interconnect 0 - MCU LSU
    assign axi_interconnect.mintf_arr[0].AWVALID = cptra_ss_mcu_lsu_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[0].AWADDR[31:0]  = cptra_ss_mcu_lsu_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[0].AWID    = cptra_ss_mcu_lsu_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[0].AWLEN   = cptra_ss_mcu_lsu_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[0].AWSIZE  = cptra_ss_mcu_lsu_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[0].AWBURST = cptra_ss_mcu_lsu_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[0].AWLOCK  = cptra_ss_mcu_lsu_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[0].AWUSER  = cptra_ss_mcu_lsu_m_axi_if.awuser;
    assign cptra_ss_mcu_lsu_m_axi_if.awready              = axi_interconnect.mintf_arr[0].AWREADY;
    assign axi_interconnect.mintf_arr[0].WVALID  = cptra_ss_mcu_lsu_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[0].WDATA   = cptra_ss_mcu_lsu_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[0].WSTRB   = cptra_ss_mcu_lsu_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[0].WLAST   = cptra_ss_mcu_lsu_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[0].WUSER  = cptra_ss_mcu_lsu_m_axi_if.wuser;
    assign cptra_ss_mcu_lsu_m_axi_if.wready               = axi_interconnect.mintf_arr[0].WREADY;
    assign cptra_ss_mcu_lsu_m_axi_if.bvalid               = axi_interconnect.mintf_arr[0].BVALID;
    assign cptra_ss_mcu_lsu_m_axi_if.bresp                = axi_interconnect.mintf_arr[0].BRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.buser                = axi_interconnect.mintf_arr[0].BUSER;
    assign cptra_ss_mcu_lsu_m_axi_if.bid                  = axi_interconnect.mintf_arr[0].BID;
    assign axi_interconnect.mintf_arr[0].BREADY  = cptra_ss_mcu_lsu_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[0].ARVALID = cptra_ss_mcu_lsu_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[0].ARADDR[31:0]  = cptra_ss_mcu_lsu_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[0].ARID    = cptra_ss_mcu_lsu_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[0].ARLEN   = cptra_ss_mcu_lsu_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[0].ARSIZE  = cptra_ss_mcu_lsu_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[0].ARBURST = cptra_ss_mcu_lsu_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[0].ARLOCK  = cptra_ss_mcu_lsu_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[0].ARUSER  = cptra_ss_mcu_lsu_m_axi_if.aruser;
    assign cptra_ss_mcu_lsu_m_axi_if.arready              = axi_interconnect.mintf_arr[0].ARREADY;
    assign cptra_ss_mcu_lsu_m_axi_if.rvalid               = axi_interconnect.mintf_arr[0].RVALID;
    assign cptra_ss_mcu_lsu_m_axi_if.rdata                = axi_interconnect.mintf_arr[0].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_lsu_m_axi_if.rresp                = axi_interconnect.mintf_arr[0].RRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.ruser                = axi_interconnect.mintf_arr[0].RUSER;
    assign cptra_ss_mcu_lsu_m_axi_if.rid                  = axi_interconnect.mintf_arr[0].RID;
    assign cptra_ss_mcu_lsu_m_axi_if.rlast                = axi_interconnect.mintf_arr[0].RLAST;
    assign axi_interconnect.mintf_arr[0].RREADY  = cptra_ss_mcu_lsu_m_axi_if.rready;

    //Interconnect 1 - MCU IFU
    assign axi_interconnect.mintf_arr[1].AWVALID = cptra_ss_mcu_ifu_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[1].AWADDR[31:0]  = cptra_ss_mcu_ifu_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[1].AWID    = cptra_ss_mcu_ifu_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[1].AWLEN   = cptra_ss_mcu_ifu_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[1].AWSIZE  = cptra_ss_mcu_ifu_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[1].AWBURST = cptra_ss_mcu_ifu_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[1].AWLOCK  = cptra_ss_mcu_ifu_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[1].AWUSER  = cptra_ss_mcu_ifu_m_axi_if.awuser;
    assign cptra_ss_mcu_ifu_m_axi_if.awready                = axi_interconnect.mintf_arr[1].AWREADY;
    assign axi_interconnect.mintf_arr[1].WVALID  = cptra_ss_mcu_ifu_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[1].WDATA   = cptra_ss_mcu_ifu_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[1].WSTRB   = cptra_ss_mcu_ifu_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[1].WLAST   = cptra_ss_mcu_ifu_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[1].WUSER  = cptra_ss_mcu_ifu_m_axi_if.wuser;
    assign cptra_ss_mcu_ifu_m_axi_if.wready                 = axi_interconnect.mintf_arr[1].WREADY;
    assign cptra_ss_mcu_ifu_m_axi_if.bvalid                 = axi_interconnect.mintf_arr[1].BVALID;
    assign cptra_ss_mcu_ifu_m_axi_if.bresp                  = axi_interconnect.mintf_arr[1].BRESP;
    assign cptra_ss_mcu_ifu_m_axi_if.buser                  = axi_interconnect.mintf_arr[1].BUSER;
    assign cptra_ss_mcu_ifu_m_axi_if.bid                    = axi_interconnect.mintf_arr[1].BID;
    assign axi_interconnect.mintf_arr[1].BREADY  = cptra_ss_mcu_ifu_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[1].ARVALID = cptra_ss_mcu_ifu_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[1].ARADDR[31:0]  = cptra_ss_mcu_ifu_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[1].ARID    = cptra_ss_mcu_ifu_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[1].ARLEN   = cptra_ss_mcu_ifu_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[1].ARSIZE  = cptra_ss_mcu_ifu_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[1].ARBURST = cptra_ss_mcu_ifu_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[1].ARLOCK  = cptra_ss_mcu_ifu_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[1].ARUSER  = cptra_ss_mcu_ifu_m_axi_if.aruser;
    assign cptra_ss_mcu_ifu_m_axi_if.arready                = axi_interconnect.mintf_arr[1].ARREADY;
    assign cptra_ss_mcu_ifu_m_axi_if.rvalid                 = axi_interconnect.mintf_arr[1].RVALID;
    assign cptra_ss_mcu_ifu_m_axi_if.rdata                  = axi_interconnect.mintf_arr[1].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_ifu_m_axi_if.rresp                  = axi_interconnect.mintf_arr[1].RRESP;
    assign cptra_ss_mcu_ifu_m_axi_if.ruser                  = axi_interconnect.mintf_arr[1].RUSER;
    assign cptra_ss_mcu_ifu_m_axi_if.rid                    = axi_interconnect.mintf_arr[1].RID;
    assign cptra_ss_mcu_ifu_m_axi_if.rlast                  = axi_interconnect.mintf_arr[1].RLAST;
    assign axi_interconnect.mintf_arr[1].RREADY  = cptra_ss_mcu_ifu_m_axi_if.rready;

    //Interconnect 2 - SysBus
    assign axi_interconnect.mintf_arr[2].AWVALID = cptra_ss_mcu_sb_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[2].AWADDR[31:0]  = cptra_ss_mcu_sb_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[2].AWID    = cptra_ss_mcu_sb_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[2].AWLEN   = cptra_ss_mcu_sb_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[2].AWSIZE  = cptra_ss_mcu_sb_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[2].AWBURST = cptra_ss_mcu_sb_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[2].AWLOCK  = cptra_ss_mcu_sb_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[2].AWUSER  = cptra_ss_mcu_sb_m_axi_if.awuser;
    assign cptra_ss_mcu_sb_m_axi_if.awready              = axi_interconnect.mintf_arr[2].AWREADY;
    assign axi_interconnect.mintf_arr[2].WVALID  = cptra_ss_mcu_sb_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[2].WDATA   = cptra_ss_mcu_sb_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[2].WSTRB   = cptra_ss_mcu_sb_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[2].WLAST   = cptra_ss_mcu_sb_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[2].WUSER  = cptra_ss_mcu_sb_m_axi_if.wuser;
    assign cptra_ss_mcu_sb_m_axi_if.wready               = axi_interconnect.mintf_arr[2].WREADY;
    assign cptra_ss_mcu_sb_m_axi_if.bvalid               = axi_interconnect.mintf_arr[2].BVALID;
    assign cptra_ss_mcu_sb_m_axi_if.bresp                = axi_interconnect.mintf_arr[2].BRESP;
    assign cptra_ss_mcu_sb_m_axi_if.buser                = axi_interconnect.mintf_arr[2].BUSER;
    assign cptra_ss_mcu_sb_m_axi_if.bid                  = axi_interconnect.mintf_arr[2].BID;
    assign axi_interconnect.mintf_arr[2].BREADY  = cptra_ss_mcu_sb_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[2].ARVALID = cptra_ss_mcu_sb_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[2].ARADDR[31:0]  = cptra_ss_mcu_sb_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[2].ARID    = cptra_ss_mcu_sb_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[2].ARLEN   = cptra_ss_mcu_sb_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[2].ARSIZE  = cptra_ss_mcu_sb_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[2].ARBURST = cptra_ss_mcu_sb_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[2].ARLOCK  = cptra_ss_mcu_sb_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[2].ARUSER  = cptra_ss_mcu_sb_m_axi_if.aruser;
    assign cptra_ss_mcu_sb_m_axi_if.arready              = axi_interconnect.mintf_arr[2].ARREADY;
    assign cptra_ss_mcu_sb_m_axi_if.rvalid               = axi_interconnect.mintf_arr[2].RVALID;
    assign cptra_ss_mcu_sb_m_axi_if.rdata                = axi_interconnect.mintf_arr[2].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_sb_m_axi_if.rresp                = axi_interconnect.mintf_arr[2].RRESP;
    assign cptra_ss_mcu_sb_m_axi_if.ruser                = axi_interconnect.mintf_arr[2].RUSER;
    assign cptra_ss_mcu_sb_m_axi_if.rid                  = axi_interconnect.mintf_arr[2].RID;
    assign cptra_ss_mcu_sb_m_axi_if.rlast                = axi_interconnect.mintf_arr[2].RLAST;
    assign axi_interconnect.mintf_arr[2].RREADY  = cptra_ss_mcu_sb_m_axi_if.rready;

    // //Interconnect 2 Sub - MCU DMA
    // // assign mcu_dma_s_axi_if.awvalid                = axi_interconnect.sintf_arr[2].AWVALID;
    // // assign mcu_dma_s_axi_if.awaddr                 = axi_interconnect.sintf_arr[2].AWADDR[31:0];
    // // assign mcu_dma_s_axi_if.awid                   = axi_interconnect.sintf_arr[2].AWID;
    // // assign mcu_dma_s_axi_if.awlen                  = axi_interconnect.sintf_arr[2].AWLEN;
    // // assign mcu_dma_s_axi_if.awsize                 = axi_interconnect.sintf_arr[2].AWSIZE;
    // // assign mcu_dma_s_axi_if.awburst                = axi_interconnect.sintf_arr[2].AWBURST;
    // // assign mcu_dma_s_axi_if.awlock                 = axi_interconnect.sintf_arr[2].AWLOCK;
    // // assign mcu_dma_s_axi_if.awuser                 = axi_interconnect.sintf_arr[2].AWUSER;
    // assign axi_interconnect.sintf_arr[2].AWREADY   = '0; //mcu_dma_s_axi_if.awready;
    // // assign mcu_dma_s_axi_if.wvalid                 = axi_interconnect.sintf_arr[2].WVALID;
    // // assign mcu_dma_s_axi_if.wdata                  = axi_interconnect.sintf_arr[2].WDATA;// Native 64-bit width, no dwidth conversion
    // // assign mcu_dma_s_axi_if.wstrb                  = axi_interconnect.sintf_arr[2].WSTRB;// Native 64-bit width, no dwidth conversion
    // // assign mcu_dma_s_axi_if.wlast                  = axi_interconnect.sintf_arr[2].WLAST;
    // assign axi_interconnect.sintf_arr[2].WREADY    = '0; //mcu_dma_s_axi_if.wready;
    // assign axi_interconnect.sintf_arr[2].BVALID    = '0; //mcu_dma_s_axi_if.bvalid;
    // assign axi_interconnect.sintf_arr[2].BRESP     = '0; //mcu_dma_s_axi_if.bresp;
    // assign axi_interconnect.sintf_arr[2].BID       = '0; //mcu_dma_s_axi_if.bid;
    // // assign mcu_dma_s_axi_if.bready                 = axi_interconnect.sintf_arr[2].BREADY;
    // // assign mcu_dma_s_axi_if.arvalid                = axi_interconnect.sintf_arr[2].ARVALID;
    // // assign mcu_dma_s_axi_if.araddr                 = axi_interconnect.sintf_arr[2].ARADDR[31:0];
    // // assign mcu_dma_s_axi_if.arid                   = axi_interconnect.sintf_arr[2].ARID;
    // // assign mcu_dma_s_axi_if.arlen                  = axi_interconnect.sintf_arr[2].ARLEN;
    // // assign mcu_dma_s_axi_if.arsize                 = axi_interconnect.sintf_arr[2].ARSIZE;
    // // assign mcu_dma_s_axi_if.arburst                = axi_interconnect.sintf_arr[2].ARBURST;
    // // assign mcu_dma_s_axi_if.arlock                 = axi_interconnect.sintf_arr[2].ARLOCK;
    // // assign mcu_dma_s_axi_if.aruser                 = axi_interconnect.sintf_arr[2].ARUSER;
    // assign axi_interconnect.sintf_arr[2].ARREADY = '0; //mcu_dma_s_axi_if.arready;
    // assign axi_interconnect.sintf_arr[2].RVALID  = '0; //mcu_dma_s_axi_if.rvalid;
    // assign axi_interconnect.sintf_arr[2].RDATA   = '0; //64'(mcu_dma_s_axi_if.rdata);// Native 64-bit width, no dwidth conversion
    // assign axi_interconnect.sintf_arr[2].RRESP   = '0; //mcu_dma_s_axi_if.rresp;
    // assign axi_interconnect.sintf_arr[2].RID     = '0; //mcu_dma_s_axi_if.rid;
    // assign axi_interconnect.sintf_arr[2].RLAST   = '0; //mcu_dma_s_axi_if.rlast;
    // // assign mcu_dma_s_axi_if.rready               = axi_interconnect.sintf_arr[2].RREADY;

    //Interconnect 3 - CPTRA soc axi if
    assign cptra_ss_cptra_core_s_axi_if.awvalid           = axi_interconnect.sintf_arr[3].AWVALID;
    assign cptra_ss_cptra_core_s_axi_if.awaddr            = axi_interconnect.sintf_arr[3].AWADDR[31:0];
    assign cptra_ss_cptra_core_s_axi_if.awid              = axi_interconnect.sintf_arr[3].AWID;
    assign cptra_ss_cptra_core_s_axi_if.awlen             = axi_interconnect.sintf_arr[3].AWLEN;
    assign cptra_ss_cptra_core_s_axi_if.awsize            = axi_interconnect.sintf_arr[3].AWSIZE;
    assign cptra_ss_cptra_core_s_axi_if.awburst           = axi_interconnect.sintf_arr[3].AWBURST;
    assign cptra_ss_cptra_core_s_axi_if.awlock            = axi_interconnect.sintf_arr[3].AWLOCK;
    assign cptra_ss_cptra_core_s_axi_if.awuser            = axi_interconnect.sintf_arr[3].AWUSER;
    assign axi_interconnect.sintf_arr[3].AWREADY = cptra_ss_cptra_core_s_axi_if.awready;
    assign cptra_ss_cptra_core_s_axi_if.wvalid            = axi_interconnect.sintf_arr[3].WVALID;
    assign cptra_ss_cptra_core_s_axi_if.wdata             = axi_interconnect.sintf_arr[3].WDATA >> (cptra_ss_cptra_core_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_cptra_core_s_axi_if.wstrb             = axi_interconnect.sintf_arr[3].WSTRB >> (cptra_ss_cptra_core_s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign cptra_ss_cptra_core_s_axi_if.wlast             = axi_interconnect.sintf_arr[3].WLAST;
    assign cptra_ss_cptra_core_s_axi_if.wuser            = axi_interconnect.sintf_arr[3].WUSER;
    assign axi_interconnect.sintf_arr[3].WREADY  = cptra_ss_cptra_core_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[3].BVALID  = cptra_ss_cptra_core_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[3].BRESP   = cptra_ss_cptra_core_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[3].BUSER   = cptra_ss_cptra_core_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[3].BID     = cptra_ss_cptra_core_s_axi_if.bid;
    assign cptra_ss_cptra_core_s_axi_if.bready            = axi_interconnect.sintf_arr[3].BREADY;
    assign cptra_ss_cptra_core_s_axi_if.arvalid           = axi_interconnect.sintf_arr[3].ARVALID;
    assign cptra_ss_cptra_core_s_axi_if.araddr            = axi_interconnect.sintf_arr[3].ARADDR[31:0];
    assign cptra_ss_cptra_core_s_axi_if.arid              = axi_interconnect.sintf_arr[3].ARID;
    assign cptra_ss_cptra_core_s_axi_if.arlen             = axi_interconnect.sintf_arr[3].ARLEN;
    assign cptra_ss_cptra_core_s_axi_if.arsize            = axi_interconnect.sintf_arr[3].ARSIZE;
    assign cptra_ss_cptra_core_s_axi_if.arburst           = axi_interconnect.sintf_arr[3].ARBURST;
    assign cptra_ss_cptra_core_s_axi_if.arlock            = axi_interconnect.sintf_arr[3].ARLOCK;
    assign cptra_ss_cptra_core_s_axi_if.aruser            = axi_interconnect.sintf_arr[3].ARUSER;
    assign axi_interconnect.sintf_arr[3].ARREADY = cptra_ss_cptra_core_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[3].RUSER    = cptra_ss_cptra_core_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[3].RVALID  = cptra_ss_cptra_core_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[3].RDATA   = 64'(cptra_ss_cptra_core_s_axi_if.rdata) << (cptra_ss_cptra_core_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[3].RRESP   = cptra_ss_cptra_core_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[3].RID     = cptra_ss_cptra_core_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[3].RLAST   = cptra_ss_cptra_core_s_axi_if.rlast;
    assign cptra_ss_cptra_core_s_axi_if.rready            = axi_interconnect.sintf_arr[3].RREADY;

    //Interconnect MGR 3 - cptra dma
    assign axi_interconnect.mintf_arr[3].AWVALID = cptra_ss_cptra_core_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[3].AWADDR[31:0]  = cptra_ss_cptra_core_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[3].AWID    = cptra_ss_cptra_core_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[3].AWLEN   = cptra_ss_cptra_core_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[3].AWSIZE  = cptra_ss_cptra_core_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[3].AWBURST = cptra_ss_cptra_core_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[3].AWLOCK  = cptra_ss_cptra_core_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[3].AWUSER  = cptra_ss_cptra_core_m_axi_if.awuser;
    assign cptra_ss_cptra_core_m_axi_if.awready           = axi_interconnect.mintf_arr[3].AWREADY;
    assign axi_interconnect.mintf_arr[3].WVALID  = cptra_ss_cptra_core_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[3].WUSER   = cptra_ss_cptra_core_m_axi_if.wuser;
    assign axi_interconnect.mintf_arr[3].WDATA   = cptra_ss_cptra_core_m_axi_if.wdata << (cptra_ss_cptra_core_m_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[3].WSTRB   = cptra_ss_cptra_core_m_axi_if.wstrb << (cptra_ss_cptra_core_m_axi_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[3].WLAST   = cptra_ss_cptra_core_m_axi_if.wlast;
    assign cptra_ss_cptra_core_m_axi_if.wready            = axi_interconnect.mintf_arr[3].WREADY;
    assign cptra_ss_cptra_core_m_axi_if.bvalid            = axi_interconnect.mintf_arr[3].BVALID;
    assign cptra_ss_cptra_core_m_axi_if.bresp             = axi_interconnect.mintf_arr[3].BRESP;
    assign cptra_ss_cptra_core_m_axi_if.bid               = axi_interconnect.mintf_arr[3].BID;
    assign cptra_ss_cptra_core_m_axi_if.buser             = axi_interconnect.mintf_arr[3].BUSER;
    assign axi_interconnect.mintf_arr[3].BREADY  = cptra_ss_cptra_core_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[3].ARVALID = cptra_ss_cptra_core_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[3].ARADDR[31:0]  = cptra_ss_cptra_core_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[3].ARID    = cptra_ss_cptra_core_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[3].ARLEN   = cptra_ss_cptra_core_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[3].ARSIZE  = cptra_ss_cptra_core_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[3].ARBURST = cptra_ss_cptra_core_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[3].ARLOCK  = cptra_ss_cptra_core_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[3].ARUSER  = cptra_ss_cptra_core_m_axi_if.aruser;
    assign cptra_ss_cptra_core_m_axi_if.arready           = axi_interconnect.mintf_arr[3].ARREADY;
    assign cptra_ss_cptra_core_m_axi_if.rvalid            = axi_interconnect.mintf_arr[3].RVALID;
    assign cptra_ss_cptra_core_m_axi_if.rdata             = axi_interconnect.mintf_arr[3].RDATA >> (cptra_ss_cptra_core_m_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_cptra_core_m_axi_if.rresp             = axi_interconnect.mintf_arr[3].RRESP;
    assign cptra_ss_cptra_core_m_axi_if.ruser             = axi_interconnect.mintf_arr[3].RUSER;
    assign cptra_ss_cptra_core_m_axi_if.rid               = axi_interconnect.mintf_arr[3].RID;
    assign cptra_ss_cptra_core_m_axi_if.rlast             = axi_interconnect.mintf_arr[3].RLAST;
    assign axi_interconnect.mintf_arr[3].RREADY  = cptra_ss_cptra_core_m_axi_if.rready;

    assign m_axi_bfm_if_FIXME.awready                   = '0;
    assign m_axi_bfm_if_FIXME.wready                    = '0;
    assign m_axi_bfm_if_FIXME.bvalid                    = '0;
    assign m_axi_bfm_if_FIXME.bresp                     = '0;
    assign m_axi_bfm_if_FIXME.bid                       = '0;
    assign m_axi_bfm_if_FIXME.buser                     = '0;
    assign m_axi_bfm_if_FIXME.arready                   = '0;
    assign m_axi_bfm_if_FIXME.rvalid                    = '0;
    assign m_axi_bfm_if_FIXME.rdata                     = '0;
    assign m_axi_bfm_if_FIXME.rresp                     = '0;
    assign m_axi_bfm_if_FIXME.rid                       = '0;
    assign m_axi_bfm_if_FIXME.rlast                     = '0;
    assign m_axi_bfm_if_FIXME.ruser                     = '0;
    //Interconnect 4 - master bfm
    assign axi_interconnect.mintf_arr[4].AWVALID  = m_axi_bfm_if.awvalid;
    assign axi_interconnect.mintf_arr[4].AWADDR[31:0]   = m_axi_bfm_if.awaddr;
    assign axi_interconnect.mintf_arr[4].AWID     = m_axi_bfm_if.awid;
    assign axi_interconnect.mintf_arr[4].AWLEN    = m_axi_bfm_if.awlen;
    assign axi_interconnect.mintf_arr[4].AWSIZE   = m_axi_bfm_if.awsize;
    assign axi_interconnect.mintf_arr[4].AWBURST  = m_axi_bfm_if.awburst;
    assign axi_interconnect.mintf_arr[4].AWLOCK   = m_axi_bfm_if.awlock;
    assign axi_interconnect.mintf_arr[4].AWUSER   = m_axi_bfm_if.awuser;
    assign m_axi_bfm_if.awready                   = axi_interconnect.mintf_arr[4].AWREADY;
    assign axi_interconnect.mintf_arr[4].WVALID   = m_axi_bfm_if.wvalid;
    assign axi_interconnect.mintf_arr[4].WDATA    = m_axi_bfm_if.wdata << (m_axi_bfm_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[4].WSTRB    = m_axi_bfm_if.wstrb << (m_axi_bfm_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[4].WLAST    = m_axi_bfm_if.wlast;
    assign axi_interconnect.mintf_arr[4].WUSER   = m_axi_bfm_if.wuser;
    assign m_axi_bfm_if.wready                    = axi_interconnect.mintf_arr[4].WREADY;
    assign m_axi_bfm_if.bvalid                    = axi_interconnect.mintf_arr[4].BVALID;
    assign m_axi_bfm_if.bresp                     = axi_interconnect.mintf_arr[4].BRESP;
    assign m_axi_bfm_if.bid                       = axi_interconnect.mintf_arr[4].BID;
    assign m_axi_bfm_if.buser                     = axi_interconnect.mintf_arr[4].BUSER;
    assign axi_interconnect.mintf_arr[4].BREADY   = m_axi_bfm_if.bready;
    assign axi_interconnect.mintf_arr[4].ARVALID  = m_axi_bfm_if.arvalid;
    assign axi_interconnect.mintf_arr[4].ARADDR[31:0]   = m_axi_bfm_if.araddr;
    assign axi_interconnect.mintf_arr[4].ARID     = m_axi_bfm_if.arid;
    assign axi_interconnect.mintf_arr[4].ARLEN    = m_axi_bfm_if.arlen;
    assign axi_interconnect.mintf_arr[4].ARSIZE   = m_axi_bfm_if.arsize;
    assign axi_interconnect.mintf_arr[4].ARBURST  = m_axi_bfm_if.arburst;
    assign axi_interconnect.mintf_arr[4].ARLOCK   = m_axi_bfm_if.arlock;
    assign axi_interconnect.mintf_arr[4].ARUSER   = m_axi_bfm_if.aruser;
    assign m_axi_bfm_if.arready                   = axi_interconnect.mintf_arr[4].ARREADY;
    assign m_axi_bfm_if.rvalid                    = axi_interconnect.mintf_arr[4].RVALID;
    assign m_axi_bfm_if.rdata                     = axi_interconnect.mintf_arr[4].RDATA >> (m_axi_bfm_if_rd_is_upper_dw_latched ? 32 : 0);
    assign m_axi_bfm_if.rresp                     = axi_interconnect.mintf_arr[4].RRESP;
    assign m_axi_bfm_if.rid                       = axi_interconnect.mintf_arr[4].RID;
    assign m_axi_bfm_if.rlast                     = axi_interconnect.mintf_arr[4].RLAST;
    assign m_axi_bfm_if.ruser                     = axi_interconnect.mintf_arr[4].RUSER;
    assign axi_interconnect.mintf_arr[4].RREADY   = m_axi_bfm_if.rready;

    assign cptra_ss_mci_s_axi_if.awvalid                      = axi_interconnect.sintf_arr[4].AWVALID;
    assign cptra_ss_mci_s_axi_if.awaddr                       = axi_interconnect.sintf_arr[4].AWADDR[31:0];
    assign cptra_ss_mci_s_axi_if.awid                         = axi_interconnect.sintf_arr[4].AWID;
    assign cptra_ss_mci_s_axi_if.awlen                        = axi_interconnect.sintf_arr[4].AWLEN;
    assign cptra_ss_mci_s_axi_if.awsize                       = axi_interconnect.sintf_arr[4].AWSIZE;
    assign cptra_ss_mci_s_axi_if.awburst                      = axi_interconnect.sintf_arr[4].AWBURST;
    assign cptra_ss_mci_s_axi_if.awlock                       = axi_interconnect.sintf_arr[4].AWLOCK;
    assign cptra_ss_mci_s_axi_if.awuser                       = axi_interconnect.sintf_arr[4].AWUSER;
    assign axi_interconnect.sintf_arr[4].AWREADY = cptra_ss_mci_s_axi_if.awready;
    assign cptra_ss_mci_s_axi_if.wvalid                       = axi_interconnect.sintf_arr[4].WVALID;
    assign cptra_ss_mci_s_axi_if.wdata                        = axi_interconnect.sintf_arr[4].WDATA >> (cptra_ss_mci_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_mci_s_axi_if.wstrb                        = axi_interconnect.sintf_arr[4].WSTRB >> (cptra_ss_mci_s_axi_if_wr_is_upper_dw_latched ? 4  : 0);
    assign cptra_ss_mci_s_axi_if.wlast                        = axi_interconnect.sintf_arr[4].WLAST;
    assign cptra_ss_mci_s_axi_if.wuser                        = axi_interconnect.sintf_arr[4].WUSER;
    assign axi_interconnect.sintf_arr[4].WREADY      = cptra_ss_mci_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[4].BVALID      = cptra_ss_mci_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[4].BRESP       = cptra_ss_mci_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[4].BUSER       = cptra_ss_mci_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[4].BID         = cptra_ss_mci_s_axi_if.bid;
    assign cptra_ss_mci_s_axi_if.bready                       = axi_interconnect.sintf_arr[4].BREADY;
    assign cptra_ss_mci_s_axi_if.arvalid                      = axi_interconnect.sintf_arr[4].ARVALID;
    assign cptra_ss_mci_s_axi_if.araddr                       = axi_interconnect.sintf_arr[4].ARADDR[31:0];
    assign cptra_ss_mci_s_axi_if.arid                         = axi_interconnect.sintf_arr[4].ARID;
    assign cptra_ss_mci_s_axi_if.arlen                        = axi_interconnect.sintf_arr[4].ARLEN;
    assign cptra_ss_mci_s_axi_if.arsize                       = axi_interconnect.sintf_arr[4].ARSIZE;
    assign cptra_ss_mci_s_axi_if.arburst                      = axi_interconnect.sintf_arr[4].ARBURST;
    assign cptra_ss_mci_s_axi_if.arlock                       = axi_interconnect.sintf_arr[4].ARLOCK;
    assign cptra_ss_mci_s_axi_if.aruser                       = axi_interconnect.sintf_arr[4].ARUSER;
    assign axi_interconnect.sintf_arr[4].ARREADY       = cptra_ss_mci_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[4].RVALID        = cptra_ss_mci_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[4].RUSER         = cptra_ss_mci_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[4].RDATA         = 64'(cptra_ss_mci_s_axi_if.rdata) << (cptra_ss_mci_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[4].RRESP         = cptra_ss_mci_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[4].RID           = cptra_ss_mci_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[4].RLAST         = cptra_ss_mci_s_axi_if.rlast;
    assign cptra_ss_mci_s_axi_if.rready                         = axi_interconnect.sintf_arr[4].RREADY;

    //Interconnect 5
    assign cptra_ss_otp_core_axi_wr_req_i.awaddr = axi_interconnect.sintf_arr[5].AWADDR[31:0];
    assign cptra_ss_otp_core_axi_wr_req_i.awburst = axi_interconnect.sintf_arr[5].AWBURST;
    assign cptra_ss_otp_core_axi_wr_req_i.awsize = axi_interconnect.sintf_arr[5].AWSIZE;
    assign cptra_ss_otp_core_axi_wr_req_i.awlen = axi_interconnect.sintf_arr[5].AWLEN;
    assign cptra_ss_otp_core_axi_wr_req_i.awuser = axi_interconnect.sintf_arr[5].AWUSER;
    assign cptra_ss_otp_core_axi_wr_req_i.awid = axi_interconnect.sintf_arr[5].AWID;
    assign cptra_ss_otp_core_axi_wr_req_i.awlock = axi_interconnect.sintf_arr[5].AWLOCK;
    assign cptra_ss_otp_core_axi_wr_req_i.awvalid = axi_interconnect.sintf_arr[5].AWVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.wdata = axi_interconnect.sintf_arr[5].WDATA >> (fuse_core_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_otp_core_axi_wr_req_i.wstrb = axi_interconnect.sintf_arr[5].WSTRB >> (fuse_core_axi_wr_is_upper_dw_latched ? 4 : 0);
    assign cptra_ss_otp_core_axi_wr_req_i.wlast = axi_interconnect.sintf_arr[5].WLAST;
    assign cptra_ss_otp_core_axi_wr_req_i.wvalid = axi_interconnect.sintf_arr[5].WVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.bready = axi_interconnect.sintf_arr[5].BREADY;
    assign axi_interconnect.sintf_arr[5].AWREADY = cptra_ss_otp_core_axi_wr_rsp_o.awready;
    assign axi_interconnect.sintf_arr[5].WREADY = cptra_ss_otp_core_axi_wr_rsp_o.wready;
    assign axi_interconnect.sintf_arr[5].BRESP = cptra_ss_otp_core_axi_wr_rsp_o.bresp;
    assign axi_interconnect.sintf_arr[5].BID = cptra_ss_otp_core_axi_wr_rsp_o.bid;
    assign axi_interconnect.sintf_arr[5].BVALID = cptra_ss_otp_core_axi_wr_rsp_o.bvalid;
    assign axi_interconnect.sintf_arr[5].BUSER  = '0; // FIXME connect?
    assign cptra_ss_otp_core_axi_rd_req_i.araddr = axi_interconnect.sintf_arr[5].ARADDR[31:0];
    assign cptra_ss_otp_core_axi_rd_req_i.arburst = axi_interconnect.sintf_arr[5].ARBURST;
    assign cptra_ss_otp_core_axi_rd_req_i.arsize = axi_interconnect.sintf_arr[5].ARSIZE;
    assign cptra_ss_otp_core_axi_rd_req_i.arlen = axi_interconnect.sintf_arr[5].ARLEN;
    assign cptra_ss_otp_core_axi_rd_req_i.aruser = axi_interconnect.sintf_arr[5].ARUSER;
    assign cptra_ss_otp_core_axi_rd_req_i.arid = axi_interconnect.sintf_arr[5].ARID;
    assign cptra_ss_otp_core_axi_rd_req_i.arlock = axi_interconnect.sintf_arr[5].ARLOCK;
    assign cptra_ss_otp_core_axi_rd_req_i.arvalid = axi_interconnect.sintf_arr[5].ARVALID;
    assign cptra_ss_otp_core_axi_rd_req_i.rready = axi_interconnect.sintf_arr[5].RREADY;
    assign axi_interconnect.sintf_arr[5].ARREADY = cptra_ss_otp_core_axi_rd_rsp_o.arready;
    assign axi_interconnect.sintf_arr[5].RDATA = 64'(cptra_ss_otp_core_axi_rd_rsp_o.rdata) << (fuse_core_axi_rd_is_upper_dw_latched ? 32 : 0);;
    assign axi_interconnect.sintf_arr[5].RRESP = cptra_ss_otp_core_axi_rd_rsp_o.rresp;
    assign axi_interconnect.sintf_arr[5].RID = cptra_ss_otp_core_axi_rd_rsp_o.rid;
    assign axi_interconnect.sintf_arr[5].RLAST = cptra_ss_otp_core_axi_rd_rsp_o.rlast;
    assign axi_interconnect.sintf_arr[5].RVALID = cptra_ss_otp_core_axi_rd_rsp_o.rvalid;
    assign axi_interconnect.sintf_arr[5].RUSER  = '0 ; // FIXME

    //Interconnect 6
    assign axi_interconnect.sintf_arr[6].AWREADY = '0;
    assign axi_interconnect.sintf_arr[6].WREADY = '0;
    assign axi_interconnect.sintf_arr[6].BRESP = '0;
    assign axi_interconnect.sintf_arr[6].BID = '0;
    assign axi_interconnect.sintf_arr[6].BVALID = '0;
    assign axi_interconnect.sintf_arr[6].BUSER  = '0;
    assign axi_interconnect.sintf_arr[6].ARREADY = '0;
    assign axi_interconnect.sintf_arr[6].RDATA = '0;
    assign axi_interconnect.sintf_arr[6].RRESP = '0;
    assign axi_interconnect.sintf_arr[6].RID = '0;
    assign axi_interconnect.sintf_arr[6].RLAST = '0;
    assign axi_interconnect.sintf_arr[6].RUSER = '0;
    assign axi_interconnect.sintf_arr[6].RVALID = '0;

    //Interconnect 7 - LCC
    assign cptra_ss_lc_axi_wr_req_i.awvalid = axi_interconnect.sintf_arr[7].AWVALID;
    assign cptra_ss_lc_axi_wr_req_i.awaddr = axi_interconnect.sintf_arr[7].AWADDR[31:0];
    assign cptra_ss_lc_axi_wr_req_i.awid = axi_interconnect.sintf_arr[7].AWID;
    assign cptra_ss_lc_axi_wr_req_i.awlen = axi_interconnect.sintf_arr[7].AWLEN;
    assign cptra_ss_lc_axi_wr_req_i.awsize = axi_interconnect.sintf_arr[7].AWSIZE;
    assign cptra_ss_lc_axi_wr_req_i.awburst = axi_interconnect.sintf_arr[7].AWBURST;
    assign cptra_ss_lc_axi_wr_req_i.awlock = axi_interconnect.sintf_arr[7].AWLOCK;
    assign cptra_ss_lc_axi_wr_req_i.awuser = axi_interconnect.sintf_arr[7].AWUSER;
    assign axi_interconnect.sintf_arr[7].AWREADY = cptra_ss_lc_axi_wr_rsp_o.awready;
    assign cptra_ss_lc_axi_wr_req_i.wvalid = axi_interconnect.sintf_arr[7].WVALID;
    assign cptra_ss_lc_axi_wr_req_i.wdata = axi_interconnect.sintf_arr[7].WDATA >> (lc_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_lc_axi_wr_req_i.wstrb = axi_interconnect.sintf_arr[7].WSTRB >> (lc_axi_wr_is_upper_dw_latched ? 4 : 0);
    assign cptra_ss_lc_axi_wr_req_i.wlast = axi_interconnect.sintf_arr[7].WLAST;
    assign axi_interconnect.sintf_arr[7].WREADY = cptra_ss_lc_axi_wr_rsp_o.wready;
    assign axi_interconnect.sintf_arr[7].BRESP = cptra_ss_lc_axi_wr_rsp_o.bresp;
    assign axi_interconnect.sintf_arr[7].BID = cptra_ss_lc_axi_wr_rsp_o.bid;
    assign axi_interconnect.sintf_arr[7].BVALID = cptra_ss_lc_axi_wr_rsp_o.bvalid;
    assign axi_interconnect.sintf_arr[7].BUSER  = '0; // FIXME?
    assign cptra_ss_lc_axi_wr_req_i.bready = axi_interconnect.sintf_arr[7].BREADY;
    assign cptra_ss_lc_axi_rd_req_i.arvalid = axi_interconnect.sintf_arr[7].ARVALID;
    assign cptra_ss_lc_axi_rd_req_i.araddr = axi_interconnect.sintf_arr[7].ARADDR[31:0];
    assign cptra_ss_lc_axi_rd_req_i.arid = axi_interconnect.sintf_arr[7].ARID;
    assign cptra_ss_lc_axi_rd_req_i.arlen = axi_interconnect.sintf_arr[7].ARLEN;
    assign cptra_ss_lc_axi_rd_req_i.arsize = axi_interconnect.sintf_arr[7].ARSIZE;
    assign cptra_ss_lc_axi_rd_req_i.arburst = axi_interconnect.sintf_arr[7].ARBURST;
    assign cptra_ss_lc_axi_rd_req_i.arlock = axi_interconnect.sintf_arr[7].ARLOCK;
    assign cptra_ss_lc_axi_rd_req_i.aruser = axi_interconnect.sintf_arr[7].ARUSER;
    assign axi_interconnect.sintf_arr[7].ARREADY = cptra_ss_lc_axi_rd_rsp_o.arready;
    assign axi_interconnect.sintf_arr[7].RDATA = 64'(cptra_ss_lc_axi_rd_rsp_o.rdata) << (lc_axi_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[7].RRESP = cptra_ss_lc_axi_rd_rsp_o.rresp;
    assign axi_interconnect.sintf_arr[7].RID = cptra_ss_lc_axi_rd_rsp_o.rid;
    assign axi_interconnect.sintf_arr[7].RLAST = cptra_ss_lc_axi_rd_rsp_o.rlast;
    assign axi_interconnect.sintf_arr[7].RUSER = '0; // FIXME
    assign axi_interconnect.sintf_arr[7].RVALID = cptra_ss_lc_axi_rd_rsp_o.rvalid;
    assign cptra_ss_lc_axi_rd_req_i.rready = axi_interconnect.sintf_arr[7].RREADY;

    //Interconnect 1 - I3C
    assign cptra_ss_i3c_s_axi_if.awvalid                    = axi_interconnect.sintf_arr[1].AWVALID;
    assign cptra_ss_i3c_s_axi_if.awaddr                     = axi_interconnect.sintf_arr[1].AWADDR[31:0];
    assign cptra_ss_i3c_s_axi_if.awid                       = axi_interconnect.sintf_arr[1].AWID;
    assign cptra_ss_i3c_s_axi_if.awlen                      = axi_interconnect.sintf_arr[1].AWLEN;
    assign cptra_ss_i3c_s_axi_if.awsize                     = axi_interconnect.sintf_arr[1].AWSIZE;
    assign cptra_ss_i3c_s_axi_if.awburst                    = axi_interconnect.sintf_arr[1].AWBURST;
    assign cptra_ss_i3c_s_axi_if.awlock                     = axi_interconnect.sintf_arr[1].AWLOCK;
    assign cptra_ss_i3c_s_axi_if.awuser                     = axi_interconnect.sintf_arr[1].AWUSER;
    assign axi_interconnect.sintf_arr[1].AWREADY = cptra_ss_i3c_s_axi_if.awready;
    assign cptra_ss_i3c_s_axi_if.wvalid                     = axi_interconnect.sintf_arr[1].WVALID;
    assign cptra_ss_i3c_s_axi_if.wdata                      = axi_interconnect.sintf_arr[1].WDATA >> (cptra_ss_i3c_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_i3c_s_axi_if.wstrb                      = axi_interconnect.sintf_arr[1].WSTRB >> (cptra_ss_i3c_s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign cptra_ss_i3c_s_axi_if.wlast                      = axi_interconnect.sintf_arr[1].WLAST;
    assign cptra_ss_i3c_s_axi_if.wuser                      = axi_interconnect.sintf_arr[1].WUSER;
    assign axi_interconnect.sintf_arr[1].WREADY  = cptra_ss_i3c_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[1].BVALID  = cptra_ss_i3c_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[1].BRESP   = cptra_ss_i3c_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[1].BUSER   = cptra_ss_i3c_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[1].BID     = cptra_ss_i3c_s_axi_if.bid;
    assign cptra_ss_i3c_s_axi_if.bready                     = axi_interconnect.sintf_arr[1].BREADY;
    assign cptra_ss_i3c_s_axi_if.arvalid                    = axi_interconnect.sintf_arr[1].ARVALID;
    assign cptra_ss_i3c_s_axi_if.araddr                     = axi_interconnect.sintf_arr[1].ARADDR[31:0];
    assign cptra_ss_i3c_s_axi_if.arid                       = axi_interconnect.sintf_arr[1].ARID;
    assign cptra_ss_i3c_s_axi_if.arlen                      = axi_interconnect.sintf_arr[1].ARLEN;
    assign cptra_ss_i3c_s_axi_if.arsize                     = axi_interconnect.sintf_arr[1].ARSIZE;
    assign cptra_ss_i3c_s_axi_if.arburst                    = axi_interconnect.sintf_arr[1].ARBURST;
    assign cptra_ss_i3c_s_axi_if.arlock                     = axi_interconnect.sintf_arr[1].ARLOCK;
    assign cptra_ss_i3c_s_axi_if.aruser                     = axi_interconnect.sintf_arr[1].ARUSER;
    assign axi_interconnect.sintf_arr[1].ARREADY = cptra_ss_i3c_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[1].RVALID  = cptra_ss_i3c_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[1].RDATA   = 64'(cptra_ss_i3c_s_axi_if.rdata) << (cptra_ss_i3c_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[1].RRESP   = cptra_ss_i3c_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[1].RUSER   = cptra_ss_i3c_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[1].RID     = cptra_ss_i3c_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[1].RLAST   = cptra_ss_i3c_s_axi_if.rlast;
    assign cptra_ss_i3c_s_axi_if.rready                     = axi_interconnect.sintf_arr[1].RREADY;

    mci_mcu_sram_if #(
        .ADDR_WIDTH(MCU_SRAM_ADDR_WIDTH)
    ) cptra_ss_mci_mcu_sram_req_if (
        .clk(core_clk),
        .rst_b(cptra_ss_rst_b_i)
    );

    mci_mcu_sram_if #(
        .ADDR_WIDTH(MCU_MBOX0_ADDR_W),
        .DATA_WIDTH(MCU_MBOX0_DATA_W),
        .ECC_WIDTH(MCU_MBOX0_ECC_DATA_W)
    )
    cptra_ss_mcu_mbox0_sram_req_if (
        .clk(core_clk),
        .rst_b(cptra_ss_rst_b_i)
    );
    
    mci_mcu_sram_if #(
        .ADDR_WIDTH(MCU_MBOX1_ADDR_W),
        .DATA_WIDTH(MCU_MBOX1_DATA_W),
        .ECC_WIDTH(MCU_MBOX1_ECC_DATA_W)
    )
    cptra_ss_mcu_mbox1_sram_req_if (
        .clk(core_clk),
        .rst_b(cptra_ss_rst_b_i)
    );

    axi_mem_if #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64)
    ) mcu_rom_mem_export_if (
        .clk(core_clk),
        .rst_b(cptra_ss_rst_b_i)
    );

    //=================== BEGIN CALIPTRA_TOP_TB ========================
    logic                       cptra_ss_cptra_core_bootfsm_bp_i;
    logic                       cptra_ss_cptra_core_scan_mode_i;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_ss_cptra_obf_key_i;
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0]     cptra_ss_cptra_csr_hmac_key_i;
    
    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    //jtag interface
    logic                      cptra_ss_cptra_core_jtag_tck_i;    // JTAG clk
    logic                      cptra_ss_cptra_core_jtag_tms_i;    // JTAG TMS
    logic                      cptra_ss_cptra_core_jtag_tdi_i;    // JTAG tdi
    logic                      cptra_ss_cptra_core_jtag_trst_n_i; // JTAG Reset
    logic                      cptra_ss_cptra_core_jtag_tdo_o;    // JTAG TDO
    logic                      cptra_ss_cptra_core_jtag_tdoEn_o;  // JTAG TDO enable

    logic ready_for_fuses;
    logic ready_for_mb_processing;
    logic mailbox_data_avail;
    logic cptra_ss_cptra_core_mbox_sram_cs_o;
    logic cptra_ss_cptra_core_mbox_sram_we_o;
    logic [CPTRA_MBOX_ADDR_W-1:0] cptra_sscptra_core_mbox_sram_addr_o;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_wdata_o;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_rdata_i;

    logic cptra_ss_cptra_core_imem_cs_o;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] cptra_ss_cptra_core_imem_addr_o;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] cptra_ss_cptra_core_imem_rdata_i;


    ras_test_ctrl_t ras_test_ctrl;
    logic [63:0] cptra_ss_cptra_core_generic_input_wires_i;
    logic        cptra_ss_cptra_core_etrng_req_o;
    logic  [3:0] cptra_ss_cptra_core_itrng_data_i;
    logic        cptra_ss_cptra_core_itrng_valid_i;

    logic cptra_error_fatal;
    logic cptra_error_non_fatal;

    //Interrupt flags
    logic int_flag;
    logic cycleCnt_smpl_en;

    //Reset flags
    logic assert_hard_rst_flag;
    logic deassert_hard_rst_flag;
    logic assert_rst_flag_from_service;
    logic deassert_rst_flag_from_service;



    caliptra_top_tb_soc_bfm #(
        .SKIP_BRINGUP(1)
    ) soc_bfm_inst (
        .core_clk        (core_clk        ),

        .cptra_pwrgood (),
        .cptra_rst_b     (     ),

        .BootFSM_BrkPoint(cptra_ss_cptra_core_bootfsm_bp_i),
        .cycleCnt        (cycleCnt        ),


        .cptra_obf_key     (cptra_ss_cptra_obf_key_i     ),
        .cptra_csr_hmac_key(cptra_ss_cptra_csr_hmac_key_i),

        .cptra_uds_rand  (cptra_uds_rand  ),
        .cptra_fe_rand   (cptra_fe_rand   ),
        .cptra_obf_key_tb(cptra_obf_key_tb),

        .m_axi_bfm_if(m_axi_bfm_if_FIXME),

        .ready_for_fuses         (ready_for_fuses         ),
        .ready_for_mb_processing (ready_for_mb_processing ),
        .mailbox_data_avail      (mailbox_data_avail      ),

        .ras_test_ctrl(ras_test_ctrl),

        .generic_input_wires(cptra_ss_cptra_core_generic_input_wires_i),

        .cptra_error_fatal(cptra_error_fatal),
        .cptra_error_non_fatal(cptra_error_non_fatal),
        
        //Interrupt flags
        .int_flag(int_flag),
        .cycleCnt_smpl_en(cycleCnt_smpl_en),

        .assert_hard_rst_flag(assert_hard_rst_flag),
        .deassert_hard_rst_flag(deassert_hard_rst_flag),
        .assert_rst_flag_from_service(assert_rst_flag_from_service),
        .deassert_rst_flag_from_service(deassert_rst_flag_from_service)

    );
    
    // JTAG DPI
    jtagdpi #(
        .Name           ("jtag0"),
        .ListenPort     (5000)
    ) jtagdpi_cptra_core (
        .clk_i          (core_clk),
        .rst_ni         (cptra_ss_rst_b_i),
        .jtag_tck       (cptra_ss_cptra_core_jtag_tck_i),
        .jtag_tms       (cptra_ss_cptra_core_jtag_tms_i),
        .jtag_tdi       (cptra_ss_cptra_core_jtag_tdi_i),
        .jtag_tdo       (cptra_ss_cptra_core_jtag_tdo_o),
        .jtag_trst_n    (cptra_ss_cptra_core_jtag_trst_n_i),
        .jtag_srst_n    ()
    );


`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
    physical_rng physical_rng (
        .clk    (core_clk),
        .enable (cptra_ss_cptra_core_etrng_req_o),
        .data   (cptra_ss_cptra_core_itrng_data_i),
        .valid  (cptra_ss_cptra_core_itrng_valid_i)
    );
`endif

    //=========================================================================-
    // Services for SRAM exports, STDOUT, etc
    //=========================================================================-
    caliptra_top_tb_services #(
        .UVM_TB(0)
    ) tb_services_i (
        .clk(core_clk),

        .cptra_rst_b(cptra_ss_rst_b_i),

        // Caliptra Memory Export Interface
        .el2_mem_export (cptra_ss_cptra_core_el2_mem_export.veer_sram_sink),
        .mldsa_memory_export (mldsa_memory_export.resp),

        //SRAM interface for mbox
        .mbox_sram_cs   (cptra_ss_cptra_core_mbox_sram_cs_o   ),
        .mbox_sram_we   (cptra_ss_cptra_core_mbox_sram_we_o   ),
        .mbox_sram_addr (cptra_sscptra_core_mbox_sram_addr_o ),
        .mbox_sram_wdata(cptra_ss_cptra_core_mbox_sram_wdata_o),
        .mbox_sram_rdata(cptra_ss_cptra_core_mbox_sram_rdata_i),

        //SRAM interface for imem
        .imem_cs   (cptra_ss_cptra_core_imem_cs_o   ),
        .imem_addr (cptra_ss_cptra_core_imem_addr_o ),
        .imem_rdata(cptra_ss_cptra_core_imem_rdata_i),

        // Security State
        .security_state(), // TODO: Remove this since we do not need it anymore, thanks to MCI

        //Scan mode
        .scan_mode(cptra_ss_cptra_core_scan_mode_i),

        // TB Controls
        .ras_test_ctrl(ras_test_ctrl),
        .cycleCnt(cycleCnt),

        //Interrupt flags
        .int_flag(int_flag),
        .cycleCnt_smpl_en(cycleCnt_smpl_en),

        //Reset flags
        .assert_hard_rst_flag(assert_hard_rst_flag),
        .deassert_hard_rst_flag(deassert_hard_rst_flag),

        .assert_rst_flag(assert_rst_flag_from_service),
        .deassert_rst_flag(deassert_rst_flag_from_service),
        
        .cptra_uds_tb(cptra_uds_rand),
        .cptra_fe_tb(cptra_fe_rand),
        .cptra_obf_key_tb(cptra_obf_key_tb)

    );

    caliptra_top_sva sva();
    caliptra_ss_top_sva ss_sva();

    //=========================================================================-
    // AXI MEM instance : IMEM
    //=========================================================================-
    //axi_slv #(.TAGW(`css_mcu0_RV_LSU_BUS_TAG)) imem(

    // axi_slv #(.TAGW(8)) imem(

    //     .aclk           (core_clk),
    //     .rst_l          (cptra_ss_rst_b_i),

    //     .arvalid        (axi_interconnect.sintf_arr[0].ARVALID),
    //     .arready        (axi_interconnect.sintf_arr[0].ARREADY),
    //     .araddr         (axi_interconnect.sintf_arr[0].ARADDR[31:0]),
    //     .arid           (axi_interconnect.sintf_arr[0].ARID),
    //     .arlen          (axi_interconnect.sintf_arr[0].ARLEN),
    //     .arburst        (axi_interconnect.sintf_arr[0].ARBURST),
    //     .arsize         (axi_interconnect.sintf_arr[0].ARSIZE),

    //     .rvalid         (axi_interconnect.sintf_arr[0].RVALID),
    //     .rready         (axi_interconnect.sintf_arr[0].RREADY),
    //     .rdata          (axi_interconnect.sintf_arr[0].RDATA),
    //     .rresp          (axi_interconnect.sintf_arr[0].RRESP),
    //     .rid            (axi_interconnect.sintf_arr[0].RID),
    //     .rlast          (axi_interconnect.sintf_arr[0].RLAST),

    //     .awvalid        (axi_interconnect.sintf_arr[0].AWVALID),
    //     .awready        (axi_interconnect.sintf_arr[0].AWREADY),
    //     .awaddr         (axi_interconnect.sintf_arr[0].AWADDR[31:0]),
    //     .awid           (axi_interconnect.sintf_arr[0].AWID),
    //     .awlen          (axi_interconnect.sintf_arr[0].AWLEN),
    //     .awburst        (axi_interconnect.sintf_arr[0].AWBURST),
    //     .awsize         (axi_interconnect.sintf_arr[0].AWSIZE),

    //     .wdata          (axi_interconnect.sintf_arr[0].WDATA),
    //     .wstrb          (axi_interconnect.sintf_arr[0].WSTRB),
    //     .wvalid         (axi_interconnect.sintf_arr[0].WVALID),
    //     .wready         (axi_interconnect.sintf_arr[0].WREADY),

    //     .bvalid         (axi_interconnect.sintf_arr[0].BVALID),
    //     .bready         (axi_interconnect.sintf_arr[0].BREADY),
    //     .bresp          (axi_interconnect.sintf_arr[0].BRESP),
    //     .bid            (axi_interconnect.sintf_arr[0].BID)

    // );
    assign axi_interconnect.sintf_arr[0].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[0].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;

    assign cptra_ss_mcu_rom_s_axi_if.awvalid                      = axi_interconnect.sintf_arr[2].AWVALID;
    assign cptra_ss_mcu_rom_s_axi_if.awaddr                       = axi_interconnect.sintf_arr[2].AWADDR[31:0];
    assign cptra_ss_mcu_rom_s_axi_if.awid                         = axi_interconnect.sintf_arr[2].AWID;
    assign cptra_ss_mcu_rom_s_axi_if.awlen                        = axi_interconnect.sintf_arr[2].AWLEN;
    assign cptra_ss_mcu_rom_s_axi_if.awsize                       = axi_interconnect.sintf_arr[2].AWSIZE;
    assign cptra_ss_mcu_rom_s_axi_if.awburst                      = axi_interconnect.sintf_arr[2].AWBURST;
    assign cptra_ss_mcu_rom_s_axi_if.awlock                       = axi_interconnect.sintf_arr[2].AWLOCK; 
    assign cptra_ss_mcu_rom_s_axi_if.awuser                       = axi_interconnect.sintf_arr[2].AWUSER;
    assign axi_interconnect.sintf_arr[2].AWREADY     = cptra_ss_mcu_rom_s_axi_if.awready;
    assign cptra_ss_mcu_rom_s_axi_if.wvalid                       = axi_interconnect.sintf_arr[2].WVALID;
    assign cptra_ss_mcu_rom_s_axi_if.wdata                        = axi_interconnect.sintf_arr[2].WDATA;// >> (cptra_ss_mcu_rom_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_ss_mcu_rom_s_axi_if.wstrb                        = axi_interconnect.sintf_arr[2].WSTRB;// >> (cptra_ss_mcu_rom_s_axi_if_wr_is_upper_dw_latched ? 4  : 0);
    assign cptra_ss_mcu_rom_s_axi_if.wlast                        = axi_interconnect.sintf_arr[2].WLAST;
    assign cptra_ss_mcu_rom_s_axi_if.wuser                        = axi_interconnect.sintf_arr[2].WUSER; 
    assign axi_interconnect.sintf_arr[2].WREADY      = cptra_ss_mcu_rom_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[2].BVALID      = cptra_ss_mcu_rom_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[2].BRESP       = cptra_ss_mcu_rom_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[2].BUSER       = cptra_ss_mcu_rom_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[2].BID         = cptra_ss_mcu_rom_s_axi_if.bid;
    assign cptra_ss_mcu_rom_s_axi_if.bready                       = axi_interconnect.sintf_arr[2].BREADY;
    assign cptra_ss_mcu_rom_s_axi_if.arvalid                      = axi_interconnect.sintf_arr[2].ARVALID;
    assign cptra_ss_mcu_rom_s_axi_if.araddr                       = axi_interconnect.sintf_arr[2].ARADDR[31:0];
    assign cptra_ss_mcu_rom_s_axi_if.arid                         = axi_interconnect.sintf_arr[2].ARID;
    assign cptra_ss_mcu_rom_s_axi_if.arlen                        = axi_interconnect.sintf_arr[2].ARLEN;
    assign cptra_ss_mcu_rom_s_axi_if.arsize                       = axi_interconnect.sintf_arr[2].ARSIZE;
    assign cptra_ss_mcu_rom_s_axi_if.arburst                      = axi_interconnect.sintf_arr[2].ARBURST;
    assign cptra_ss_mcu_rom_s_axi_if.arlock                       = axi_interconnect.sintf_arr[2].ARLOCK;
    assign cptra_ss_mcu_rom_s_axi_if.aruser                       = axi_interconnect.sintf_arr[2].ARUSER;
    assign axi_interconnect.sintf_arr[2].ARREADY       = cptra_ss_mcu_rom_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[2].RVALID        = cptra_ss_mcu_rom_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[2].RDATA         = 64'(cptra_ss_mcu_rom_s_axi_if.rdata);// << (cptra_ss_mcu_rom_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[2].RRESP         = cptra_ss_mcu_rom_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[2].RUSER         = cptra_ss_mcu_rom_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[2].RID           = cptra_ss_mcu_rom_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[2].RLAST         = cptra_ss_mcu_rom_s_axi_if.rlast;
    assign cptra_ss_mcu_rom_s_axi_if.rready            = axi_interconnect.sintf_arr[2].RREADY;



  //-------------------------------------------------------------------------
  // Aggregated signals for the OTP macro interface.
  // These signals will connect both to caliptra_ss_top ports and to prim_generic_otp.
  //-------------------------------------------------------------------------
  otp_ctrl_pkg::prim_generic_otp_outputs_t cptra_ss_fuse_macro_outputs_tb;
  otp_ctrl_pkg::prim_generic_otp_inputs_t  cptra_ss_fuse_macro_inputs_tb;

   // driven by lc_ctrl_bfm
   logic cptra_ss_lc_esclate_scrap_state0_i;
   logic cptra_ss_lc_esclate_scrap_state1_i;

   
    lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_ack_i;
    lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_req_o;

    // JTAG Assignment for top level caliptra SS design
    jtag_pkg::jtag_req_t cptra_ss_lc_ctrl_jtag_i;
    jtag_pkg::jtag_rsp_t cptra_ss_lc_ctrl_jtag_o;
    assign cptra_ss_lc_ctrl_jtag_i = '0;

    lc_ctrl_bfm u_lc_ctrl_bfm (
        .clk(core_clk),
        .reset_n(cptra_ss_rst_b_i),

        .lc_axi_rd_req(cptra_ss_lc_axi_rd_req_i),
        .lc_axi_rd_rsp(cptra_ss_lc_axi_rd_rsp_o),
        .fake_reset(lcc_bfm_reset),
        .Allow_RMA_or_SCRAP_on_PPD(cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i),

        // Escalation State Interface
        .esc_scrap_state0(cptra_ss_lc_esclate_scrap_state0_i),
        .esc_scrap_state1(cptra_ss_lc_esclate_scrap_state1_i),

        // Clock manager interface
        .lc_clk_byp_req_o(cptra_ss_lc_clk_byp_req_o),
        .lc_clk_byp_ack_i(cptra_ss_lc_clk_byp_ack_i)
    );

    initial begin
        cptra_ss_FIPS_ZEROIZATION_PPD_i = 1'b0;
    end


    //--------------------------------------------------------------------------------------------

    assign lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(caliptra_ss_dut.u_lc_ctrl.pwr_lc_o.lc_done);
    assign lcc_init_req.lc_init = mci_to_lcc_init_req; 


    fuse_ctrl_bfm u_fuse_ctrl_bfm (
        .core_clk            (core_clk            ),
        .cptra_pwrgood       (cptra_ss_pwrgood_i    ),
        .fc_partition_init   (pwr_otp_init_i      ),
        .lc_dft_en_i         (),
        .lc_escalate_en_i    (),
        .lc_check_byp_en_i   (),
        .otp_lc_data_o (caliptra_ss_dut.u_otp_ctrl.otp_lc_data_o),
        .fuse_ctrl_rdy       (fuse_ctrl_rdy       )
    );


    prim_generic_otp #(
        .Width            ( otp_ctrl_pkg::OtpWidth            ),
        .Depth            ( otp_ctrl_pkg::OtpDepth            ),
        .SizeWidth        ( otp_ctrl_pkg::OtpSizeWidth        ),
        .PwrSeqWidth      ( otp_ctrl_pkg::OtpPwrSeqWidth      ),
        .TestCtrlWidth    ( otp_ctrl_pkg::OtpTestCtrlWidth    ),
        .TestStatusWidth  ( otp_ctrl_pkg::OtpTestStatusWidth  ),
        .TestVectWidth    ( otp_ctrl_pkg::OtpTestVectWidth    ),
        .MemInitFile      ("otp-img.2048.vmem"                  ),
        .VendorTestOffset ( otp_ctrl_reg_pkg::VendorTestOffset    ),
        .VendorTestSize   ( otp_ctrl_reg_pkg::VendorTestSize      )
    ) u_otp (
        // Clock and Reset
        .clk_i          ( cptra_ss_fuse_macro_inputs_tb.clk_i ),
        .rst_ni         ( cptra_ss_fuse_macro_inputs_tb.rst_ni ),
        // Observability controls to/from AST
        .obs_ctrl_i     ( cptra_ss_fuse_macro_inputs_tb.obs_ctrl_i ),
        .otp_obs_o      ( cptra_ss_fuse_macro_outputs_tb.otp_obs_o ),
        // Power sequencing signals to/from AST
        .pwr_seq_o      ( cptra_ss_fuse_macro_outputs_tb.pwr_seq_o ),
        .pwr_seq_h_i    ( cptra_ss_fuse_macro_inputs_tb.pwr_seq_h_i ),
        // Other DFT signals
        .scanmode_i     ( cptra_ss_fuse_macro_inputs_tb.scanmode_i ),
        .scan_en_i      ( cptra_ss_fuse_macro_inputs_tb.scan_en_i ),
        .scan_rst_ni    ( cptra_ss_fuse_macro_inputs_tb.scan_rst_ni ),
        // Alert signals
        .fatal_alert_o  ( cptra_ss_fuse_macro_outputs_tb.fatal_alert_o ),
        .recov_alert_o  ( cptra_ss_fuse_macro_outputs_tb.recov_alert_o ),
        // Ready/valid handshake and command interface
        .ready_o        ( cptra_ss_fuse_macro_outputs_tb.ready_o ),
        .valid_i        ( cptra_ss_fuse_macro_inputs_tb.valid_i ),
        .size_i         ( cptra_ss_fuse_macro_inputs_tb.size_i ),
        .cmd_i          ( cptra_ss_fuse_macro_inputs_tb.cmd_i ),
        .addr_i         ( cptra_ss_fuse_macro_inputs_tb.addr_i ),
        .wdata_i        ( cptra_ss_fuse_macro_inputs_tb.wdata_i ),
        // Response channel
        .valid_o        ( cptra_ss_fuse_macro_outputs_tb.valid_o ),
        .rdata_o        ( cptra_ss_fuse_macro_outputs_tb.rdata_o ),
        .err_o          ( cptra_ss_fuse_macro_outputs_tb.err_o )
    );

    // --- I3C env and interface ---
    ai3c_env i3c_env0;
    wand  SCL;
    wand  SDA;

    // --- Avery I3C master ---
    ai3c_device#(`AI3C_LANE_NUM) master0;
    ai3c_intf#(`AI3C_LANE_NUM) master0_intf(SDA, SCL);

    // // // --- Avery I3C slave ---
    // ai3c_device#(`AI3C_LANE_NUM) slaves[$];
    // ai3c_device#(`AI3C_LANE_NUM) slave;
    // ai3c_intf#(`AI3C_LANE_NUM) slave_intf(i3c_sda_io, i3c_scl_io);

    // --- AXI interface for I3C ---
    logic i3c_axi_rd_is_upper_dw_latched; // FIXME
    logic i3c_axi_wr_is_upper_dw_latched; // FIXME
    logic [31:0] i3c_axi_rdata_32; // FIXME
    logic [31:0] i3c_axi_wdata_32; // FIXME
    logic [3:0]  i3c_axi_wstrb_4; // FIXME

    `ifdef DIGITAL_IO_I3C
        wire cptra_ss_sel_od_pp_o;
    `else
        wire cptra_ss_i3c_scl_io;
        wire cptra_ss_i3c_sda_io;
    `endif

    initial begin
        string avy_test_name;
        
        // --- Avery I3C slave ---
        // slave = new("slave", , AI3C_SLAVE, slave_intf);
        // slave.log.enable_bus_tracker = 1;
        // slave.cfg_info.basic_mode();
        // slave.set("static_addr", 7'b010_0001);
        // slaves.push_back(slave);
        // i3c_env0.add_slave(slaves[0]);
        // slaves[0].set("start_bfm");

        // --- Avery I3C master ---
        master0 = new("master0", , AI3C_MASTER, master0_intf);
        master0.cfg_info.is_main_master = 1;
        master0.log.enable_bus_tracker  = 1;
        master0.set("add_i3c_dev", 7'h5A); // virtual target 0 static address
        master0.set("add_i3c_dev", 7'h5B); // virtual target 1 static address - recovery target
        master0.cfg_info.receive_all_txn = 0;
        

        // --- I3C env ---
        i3c_env0 = new("i3c_env0");
        i3c_env0.add_master(master0);

        // run test for i3C
        if($value$plusargs("AVY_TEST=%s", avy_test_name)) begin
            $display("Waiting for 150us before Running I3C test [%s]", avy_test_name);
            #150us;  // system boot delay
            i3c_env0.sb.enable_sb=0;
            master0.set("start_bfm");
            ai3c_run_test(avy_test_name, i3c_env0); 
        end

    end

    //instantiate caliptra ss top module
    logic [124:0] cptra_ss_cptra_generic_fw_exec_ctrl_o;
    logic         cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o;
    logic         cptra_ss_mci_boot_seq_brkpoint_i;
    logic         cptra_ss_mcu_no_rom_config_i;
    logic [31:0]  cptra_ss_strap_mcu_reset_vector_i;
    logic [63:0]  cptra_ss_mci_generic_input_wires_i; 
    logic [63:0]  cptra_ss_mci_generic_output_wires_o;
    logic         cptra_ss_all_error_fatal_o;
    logic         cptra_ss_all_error_non_fatal_o;
    logic [31:0]  cptra_ss_strap_mcu_lsu_axi_user_i;
    logic [31:0]  cptra_ss_strap_mcu_ifu_axi_user_i;
    logic [31:0]  cptra_ss_strap_mcu_sram_config_axi_user_i;
    logic [31:0]  cptra_ss_strap_mci_soc_config_axi_user_i;
    logic [pt.PIC_TOTAL_INT:`VEER_INTR_EXT_LSB] cptra_ss_mcu_ext_int;
    logic         cptra_ss_mcu_jtag_tck_i;
    logic         cptra_ss_mcu_jtag_tms_i;
    logic         cptra_ss_mcu_jtag_tdi_i;
    logic         cptra_ss_mcu_jtag_trst_n_i;
    logic         cptra_ss_mcu_jtag_tdo_o;
    logic         cptra_ss_mcu_jtag_tdoEn_o;
    logic [63:0]  cptra_ss_strap_caliptra_base_addr_i;
    logic [63:0]  cptra_ss_strap_mci_base_addr_i;
    logic [63:0]  cptra_ss_strap_recovery_ifc_base_addr_i;
    logic [63:0]  cptra_ss_strap_otp_fc_base_addr_i;
    logic [63:0]  cptra_ss_strap_uds_seed_base_addr_i;
    logic [31:0]  cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;
    logic [31:0]  cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i;
    logic [31:0]  cptra_ss_strap_caliptra_dma_axi_user_i;
    logic [31:0]  cptra_ss_strap_generic_0_i;
    logic [31:0]  cptra_ss_strap_generic_1_i;
    logic [31:0]  cptra_ss_strap_generic_2_i;
    logic [31:0]  cptra_ss_strap_generic_3_i;
    logic         cptra_ss_dbg_manuf_enable_o;
    logic [63:0]  cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o;

    assign cptra_ss_mci_boot_seq_brkpoint_i     = 1'b0;
    assign cptra_ss_mcu_no_rom_config_i         = 1'b0;
    assign cptra_ss_strap_mcu_reset_vector_i    = `css_mcu0_RV_RESET_VEC;
    assign cptra_ss_mci_generic_input_wires_i   = 64'h0;
    assign cptra_ss_mcu_ext_int = '0;
    assign cptra_ss_strap_caliptra_base_addr_i  = 64'(`SOC_SOC_IFC_REG_BASE_ADDR - (`SOC_SOC_IFC_REG_BASE_ADDR & ((1<<SOC_IFC_ADDR_W)-1)));
    assign cptra_ss_strap_mci_base_addr_i       = 64'(`SOC_MCI_TOP_BASE_ADDR);
    assign cptra_ss_strap_recovery_ifc_base_addr_i = {32'h0, `SOC_I3CCSR_I3C_EC_START};
    assign cptra_ss_strap_otp_fc_base_addr_i    = 64'h0000_0000_7000_0000;
    assign cptra_ss_strap_uds_seed_base_addr_i  = 64'h0000_0000_0000_0048;
    assign cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i = 32'h0;
    assign cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i        = 32'h0;
    assign cptra_ss_strap_generic_0_i           = 32'h0;
    assign cptra_ss_strap_generic_1_i           = 32'h0;
    assign cptra_ss_strap_generic_2_i           = 32'h0;
    assign cptra_ss_strap_generic_3_i           = 32'h0;
    assign cptra_ss_debug_intent_i              = 1'b0;

    // JTAG DPI
    jtagdpi #(
        .Name           ("jtag1"),
        .ListenPort     (6000)
    ) jtagdpi_mcu (
        .clk_i          (core_clk),
        .rst_ni         (cptra_ss_rst_b_i),
        .jtag_tck       (cptra_ss_mcu_jtag_tck_i),
        .jtag_tms       (cptra_ss_mcu_jtag_tms_i),
        .jtag_tdi       (cptra_ss_mcu_jtag_tdi_i),
        .jtag_tdo       (cptra_ss_mcu_jtag_tdo_o),
        .jtag_trst_n    (cptra_ss_mcu_jtag_trst_n_i),
        .jtag_srst_n    ()
    );

    caliptra_ss_top #(
        .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB),
        .MCU_MBOX0_SIZE_KB(MCU_MBOX0_SIZE_KB),
        .SET_MCU_MBOX0_AXI_USER_INTEG(SET_MCU_MBOX0_AXI_USER_INTEG),
        .MCU_MBOX0_VALID_AXI_USER(MCU_MBOX0_VALID_AXI_USER),
        .MCU_MBOX1_SIZE_KB(MCU_MBOX1_SIZE_KB),
        .SET_MCU_MBOX1_AXI_USER_INTEG(SET_MCU_MBOX1_AXI_USER_INTEG),
        .MCU_MBOX1_VALID_AXI_USER(MCU_MBOX1_VALID_AXI_USER)

    )
    caliptra_ss_dut (

        .cptra_ss_clk_i(core_clk),
        .cptra_ss_pwrgood_i(cptra_ss_pwrgood_i),
        .cptra_ss_rst_b_i(cptra_ss_rst_b_i),
        .cptra_ss_mci_cptra_rst_b_i(cptra_ss_mci_cptra_rst_b_o),
        .cptra_ss_mci_cptra_rst_b_o,
    
    //SoC AXI Interface
        .cptra_ss_cptra_core_s_axi_if,
    
    // AXI Manager INF
        .cptra_ss_cptra_core_m_axi_if,
    
    //MCU ROM Sub Interface
        .cptra_ss_mcu_rom_s_axi_if,
        .mcu_rom_mem_export_if,
    
    //MCI AXI Sub Interface
        .cptra_ss_mci_s_axi_if,
    
    // AXI Manager INF
    
        .cptra_ss_mcu_lsu_m_axi_if,
        .cptra_ss_mcu_ifu_m_axi_if,
        .cptra_ss_mcu_sb_m_axi_if,
        // .mcu_dma_s_axi_if,
        .cptra_ss_i3c_s_axi_if,
    
        .cptra_ss_lc_axi_wr_req_i,
        .cptra_ss_lc_axi_wr_rsp_o,
        .cptra_ss_lc_axi_rd_req_i,
        .cptra_ss_lc_axi_rd_rsp_o,
    
        .cptra_ss_otp_core_axi_wr_req_i,
        .cptra_ss_otp_core_axi_wr_rsp_o,
        .cptra_ss_otp_core_axi_rd_req_i,
        .cptra_ss_otp_core_axi_rd_rsp_o,
    
    //--------------------
    //caliptra core signals
    //--------------------
        .cptra_ss_cptra_obf_key_i,
        .cptra_ss_cptra_csr_hmac_key_i,  
    
    //Caliptra JTAG Interface
        .cptra_ss_cptra_core_jtag_tck_i,    // JTAG clk
        .cptra_ss_cptra_core_jtag_tms_i,    // JTAG TMS
        .cptra_ss_cptra_core_jtag_tdi_i,    // JTAG tdi
        .cptra_ss_cptra_core_jtag_trst_n_i, // JTAG Reset
        .cptra_ss_cptra_core_jtag_tdo_o,    // JTAG TDO
        .cptra_ss_cptra_core_jtag_tdoEn_o,  // JTAG TDO enable
        .cptra_ss_cptra_generic_fw_exec_ctrl_o,
        .cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o,
        .cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i(cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o),
        .cptra_ss_debug_intent_i,
        .cptra_ss_dbg_manuf_enable_o,
        .cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o,

    // LC Controller JTAG
        .cptra_ss_lc_ctrl_jtag_i,
        .cptra_ss_lc_ctrl_jtag_o,

    // Caliptra Memory Export Interface
        .cptra_ss_cptra_core_el2_mem_export,
        .mldsa_memory_export_req(mldsa_memory_export.req),
    
    //SRAM interface for mbox
        .cptra_ss_cptra_core_mbox_sram_cs_o,
        .cptra_ss_cptra_core_mbox_sram_we_o,
        .cptra_sscptra_core_mbox_sram_addr_o,
        .cptra_ss_cptra_core_mbox_sram_wdata_o,
        .cptra_ss_cptra_core_mbox_sram_rdata_i,
    
    //SRAM interface for imem
        .cptra_ss_cptra_core_imem_cs_o,
        .cptra_ss_cptra_core_imem_addr_o,
        .cptra_ss_cptra_core_imem_rdata_i,

        .cptra_ss_cptra_core_bootfsm_bp_i,
       
    // TRNG Interface
    `ifdef CALIPTRA_INTERNAL_TRNG
        // External Request
        .cptra_ss_cptra_core_etrng_req_o,
        // Physical Source for Internal TRNG
        .cptra_ss_cptra_core_itrng_data_i,
        .cptra_ss_cptra_core_itrng_valid_i,
    `endif
    
    
    //MCU
        .cptra_ss_strap_mcu_lsu_axi_user_i,
        .cptra_ss_strap_mcu_ifu_axi_user_i,
        .cptra_ss_strap_mcu_sram_config_axi_user_i,
        .cptra_ss_strap_mci_soc_config_axi_user_i,

    //MCI
        .cptra_ss_mci_mcu_sram_req_if,
        .cptra_ss_mcu_mbox0_sram_req_if,
        .cptra_ss_mcu_mbox1_sram_req_if,
        .cptra_ss_mcu0_el2_mem_export,
        .cptra_ss_mci_boot_seq_brkpoint_i,
        .cptra_ss_mcu_no_rom_config_i,
        .cptra_ss_mci_generic_input_wires_i,
        .cptra_ss_strap_mcu_reset_vector_i,
        .cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i,
        .cptra_ss_FIPS_ZEROIZATION_PPD_i,
        .cptra_ss_soc_mcu_mbox0_data_avail,
        .cptra_ss_soc_mcu_mbox1_data_avail,

        .cptra_ss_mci_generic_output_wires_o,
        .cptra_ss_all_error_fatal_o,
        .cptra_ss_all_error_non_fatal_o,

        .cptra_ss_mcu_ext_int,
        .cptra_ss_mcu_jtag_tck_i,
        .cptra_ss_mcu_jtag_tms_i,
        .cptra_ss_mcu_jtag_tdi_i,
        .cptra_ss_mcu_jtag_trst_n_i,
        .cptra_ss_mcu_jtag_tdo_o,
        .cptra_ss_mcu_jtag_tdoEn_o,

    //Strap
        .cptra_ss_strap_caliptra_base_addr_i,
        .cptra_ss_strap_mci_base_addr_i,
        .cptra_ss_strap_recovery_ifc_base_addr_i,
        .cptra_ss_strap_otp_fc_base_addr_i,
        .cptra_ss_strap_uds_seed_base_addr_i,
        .cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i,
        .cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i,
        .cptra_ss_strap_caliptra_dma_axi_user_i,
        .cptra_ss_strap_generic_0_i,
        .cptra_ss_strap_generic_1_i,
        .cptra_ss_strap_generic_2_i,
        .cptra_ss_strap_generic_3_i,
    
        .cptra_ss_lc_clk_byp_ack_i           (cptra_ss_lc_clk_byp_ack_i),
        .cptra_ss_lc_clk_byp_req_o           (cptra_ss_lc_clk_byp_req_o),
        .cptra_ss_lc_ctrl_scan_rst_ni_i      (1'b1), // Note: Since we do not use dmi and use JTAG we do not need this
    
        .cptra_ss_lc_esclate_scrap_state0_i,
        .cptra_ss_lc_esclate_scrap_state1_i,
    
        .cptra_ss_soc_dft_en_o,
        .cptra_ss_soc_hw_debug_en_o,

        .cptra_ss_fuse_macro_outputs_i (cptra_ss_fuse_macro_outputs_tb),
        .cptra_ss_fuse_macro_inputs_o  (cptra_ss_fuse_macro_inputs_tb),
    
    // I3C Interface
    `ifdef DIGITAL_IO_I3C
        .cptra_ss_i3c_scl_i(master0_intf.scl_and),
        .cptra_ss_i3c_sda_i(master0_intf.sda_and),
        .cptra_ss_i3c_scl_o(master0_intf.scl_and),
        .cptra_ss_i3c_sda_o(master0_intf.sda_and),
        .cptra_ss_sel_od_pp_o,
    `else
        .cptra_ss_i3c_scl_io,
        .cptra_ss_i3c_sda_io,
    `endif

        // -- remove in final version
        .cptra_ss_cptra_core_generic_input_wires_i,
        .cptra_ss_cptra_core_scan_mode_i,
        .cptra_error_fatal,
        .cptra_error_non_fatal,
        .ready_for_fuses,
        .ready_for_mb_processing,
        .mailbox_data_avail

    );

    // Instantiate caliptra_ss_top_tb_soc_bfm
    caliptra_ss_top_tb_soc_bfm #(
        .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB)
    )u_caliptra_ss_top_tb_soc_bfm (
        .core_clk,
        .cptra_pwrgood (cptra_ss_pwrgood_i),
        .cptra_rst_b(rst_l),
        .cycleCnt,

        .cptra_ss_strap_mcu_lsu_axi_user_i,
        .cptra_ss_strap_mcu_ifu_axi_user_i,
        .cptra_ss_strap_mcu_sram_config_axi_user_i,
        .cptra_ss_strap_mci_soc_config_axi_user_i,
        .cptra_ss_strap_caliptra_dma_axi_user_i,


        .m_axi_bfm_if,
        .tb_services_if(i_caliptra_ss_bfm_services_if.bfm)

    );
    
    // Instantiate caliptra_ss_top_tb_services
    caliptra_ss_top_tb_services u_caliptra_ss_top_tb_services (
        .clk                         (core_clk                    ),
        .rst_l                       (cptra_ss_rst_b_i            ),
        .cycleCnt                    (cycleCnt                    ),
        .cptra_ss_mcu0_el2_mem_export(cptra_ss_mcu0_el2_mem_export),
        .soc_bfm_if(i_caliptra_ss_bfm_services_if.tb_services),
        .cptra_ss_mci_mcu_sram_req_if,
        .cptra_ss_mcu_mbox0_sram_req_if,
        .cptra_ss_mcu_mbox1_sram_req_if,
        .mcu_rom_mem_export_if
    );
    

endmodule

// --- Avery I3C Test Case Bench ---
// This is the top level module for the Avery I3C test case bench.
// it triggers i3c test cases.
`include "ai3c_tests_bench.sv"
