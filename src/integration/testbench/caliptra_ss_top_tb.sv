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
`include "caliptra_ss_top_tb_intc_includes.svh"



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
    logic                       cptra_ss_mci_cptra_rst_b_o;
    logic                       cptra_ss_rdc_clk_cg_o;
    logic                       cptra_ss_mcu_clk_cg_o;
    logic                       cptra_ss_mcu_rst_b_o;
    
    logic                       cptra_ss_warm_reset_rdc_clk_dis_o;
    logic                       cptra_ss_early_warm_reset_warn_o;
    logic                       cptra_ss_mcu_fw_update_rdc_clk_dis_o;

    logic        [31:0]         trace_rv_i_insn_ip;
    logic        [31:0]         trace_rv_i_address_ip;
    logic                       trace_rv_i_valid_ip;
    logic                       trace_rv_i_exception_ip;
    logic        [4:0]          trace_rv_i_ecause_ip;
    logic                       trace_rv_i_interrupt_ip;
    logic        [31:0]         trace_rv_i_tval_ip;

    logic                       o_debug_mode_status;


    logic                       jtag_tdo;

    logic                       cptra_ss_mcu_halt_status_o;
    logic                       cptra_ss_mcu_halt_status_i;
    logic                       cptra_ss_mcu_halt_req_o;
    logic                       cptra_ss_mcu_halt_ack_o;
    logic                       cptra_ss_mcu_halt_ack_i;

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
    logic lcc_clock_switch_req;
    int lcc_clock_selection;

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
        forever begin
            if (lcc_clock_switch_req) begin
                frequency = lcc_clock_selection;
            end
            case (frequency)
                333: core_clk = #(1.501) ~core_clk; // 333MHz -> ~3.003s period, ~1.501.ns half-period
                400: core_clk = #(1.25) ~core_clk;  // 400MHz -> 2.5ns period, 1.25ns half-period
                500: core_clk = #(1.0) ~core_clk;   // 500MHz -> 2.0ns period, 1.0ns half-period
                1000: core_clk = #(0.5) ~core_clk;   // 1000MHz -> 1.0ns period, 0.5ns half-period
                default: begin
                    $display("Error: Unsupported frequency value %d in file", frequency);
                    $finish;
                end
            endcase
        end
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
    ) m_axi_bfm_if_FIXME (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));
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

    // MCU SB AXI Interface
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
    // MCU IFU AXI Interface (downsized)
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(64), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_ifu_ds_m_axi_if (.clk(core_clk), .rst_n(cptra_ss_rst_b_i));

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

    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awcache;
    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arcache;
    logic [2:0] cptra_ss_mcu_lsu_m_axi_if_awprot;
    logic [2:0] cptra_ss_mcu_lsu_m_axi_if_arprot;
    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awregion;
    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arregion;
    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_awqos;
    logic [3:0] cptra_ss_mcu_lsu_m_axi_if_arqos;

    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awcache;
    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arcache;
    logic [2:0] cptra_ss_mcu_ifu_m_axi_if_awprot;
    logic [2:0] cptra_ss_mcu_ifu_m_axi_if_arprot;
    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awregion;
    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arregion;
    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_awqos;
    logic [3:0] cptra_ss_mcu_ifu_m_axi_if_arqos;
    // ----- FIXME remove these signals once interconnect supports downsizing
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_awcache;
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_arcache;
    logic [2:0] cptra_ss_mcu_ifu_ds_m_axi_if_awprot;
    logic [2:0] cptra_ss_mcu_ifu_ds_m_axi_if_arprot;
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_awregion;
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_arregion;
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_awqos;
    logic [3:0] cptra_ss_mcu_ifu_ds_m_axi_if_arqos;
    // ----- END FIXME

    logic [3:0] cptra_ss_mcu_sb_m_axi_if_awcache;
    logic [3:0] cptra_ss_mcu_sb_m_axi_if_arcache;
    logic [2:0] cptra_ss_mcu_sb_m_axi_if_awprot;
    logic [2:0] cptra_ss_mcu_sb_m_axi_if_arprot;
    logic [3:0] cptra_ss_mcu_sb_m_axi_if_awregion;
    logic [3:0] cptra_ss_mcu_sb_m_axi_if_arregion;
    logic [3:0] cptra_ss_mcu_sb_m_axi_if_awqos;
    logic [3:0] cptra_ss_mcu_sb_m_axi_if_arqos;

    // Signal that may be viewed in waves to review the mapping of
    // functional AXI interfaces to indexed ports of the interconnect
    struct packed {
        logic [$clog2(AAXI_INTC_MASTER_CNT)-1:0] MCU_LSU_IDX           ; // CSS_INTC_MINTF_MCU_LSU_IDX    0
        logic [$clog2(AAXI_INTC_MASTER_CNT)-1:0] MCU_IFU_IDX           ; // CSS_INTC_MINTF_MCU_IFU_IDX    1
        logic [$clog2(AAXI_INTC_MASTER_CNT)-1:0] MCU_SB_IDX            ; // CSS_INTC_MINTF_MCU_SB_IDX     2
        logic [$clog2(AAXI_INTC_MASTER_CNT)-1:0] CPTRA_DMA_IDX         ; // CSS_INTC_MINTF_CPTRA_DMA_IDX  3
        logic [$clog2(AAXI_INTC_MASTER_CNT)-1:0] SOC_BFM_IDX           ; // CSS_INTC_MINTF_SOC_BFM_IDX    4

        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_NC0_IDX          ; // CSS_INTC_SINTF_NC0_IDX           0 /* Currently unconnected */
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_I3C_IDX          ; // CSS_INTC_SINTF_I3C_IDX           1
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_MCU_ROM_IDX      ; // CSS_INTC_SINTF_MCU_ROM_IDX       2
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_CPTRA_SOC_IFC_IDX; // CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX 3
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_MCI_IDX          ; // CSS_INTC_SINTF_MCI_IDX           4
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_FC_IDX           ; // CSS_INTC_SINTF_FC_IDX            5
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_NC1_IDX          ; // CSS_INTC_SINTF_NC1_IDX           6 /* Currently unconnected */
        logic [$clog2(AAXI_INTC_SLAVE_CNT)-1:0] SINTF_LCC_IDX          ; // CSS_INTC_SINTF_LCC_IDX           7
    } debug_axi_intf_indices = '{
        MCU_LSU_IDX            : `CSS_INTC_MINTF_MCU_LSU_IDX,
        MCU_IFU_IDX            : `CSS_INTC_MINTF_MCU_IFU_IDX,
        MCU_SB_IDX             : `CSS_INTC_MINTF_MCU_SB_IDX,
        CPTRA_DMA_IDX          : `CSS_INTC_MINTF_CPTRA_DMA_IDX,
        SOC_BFM_IDX            : `CSS_INTC_MINTF_SOC_BFM_IDX,

        SINTF_NC0_IDX          : `CSS_INTC_SINTF_NC0_IDX,
        SINTF_I3C_IDX          : `CSS_INTC_SINTF_I3C_IDX,
        SINTF_MCU_ROM_IDX      : `CSS_INTC_SINTF_MCU_ROM_IDX,
        SINTF_CPTRA_SOC_IFC_IDX: `CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX,
        SINTF_MCI_IDX          : `CSS_INTC_SINTF_MCI_IDX,
        SINTF_FC_IDX           : `CSS_INTC_SINTF_FC_IDX,
        SINTF_NC1_IDX          : `CSS_INTC_SINTF_NC1_IDX,
        SINTF_LCC_IDX          : `CSS_INTC_SINTF_LCC_IDX
    };

    // AXI Interconnect upper address tie to 0
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX  ].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX  ].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX  ].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX  ].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX   ].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX   ].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX  ].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX  ].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX  ].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX  ].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;

    // Slave port 0 disconnection.
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].ARREADY = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RVALID = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RDATA = 64'h0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RRESP = 2'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RID = 8'h0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RLAST = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].RUSER = '0;

    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].AWREADY = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].WREADY = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].BVALID = 1'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].BRESP = 2'b0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].BUSER = '0;

    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].BID = 8'h0;


    //Interconnect 0 - MCU LSU
    // FIXME
    // Require wsize < 3 so that we can force wsize to '2' in the hack below
    // This is a workaround for the issue in the interconnect where (wsize == 0) && (wstrb == 0x2)
    // gets erroneously manipulated into an output with (wsize == 2), but the address remains
    // unaligned.
    // That condition violates AXI spec.
    // The workaround here is to force aligned accesses, and use _only_ wstrb
    // for lane control, which is compliant to AXI.
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BITlsu, (cptra_ss_mcu_lsu_m_axi_if.awvalid && cptra_ss_mcu_lsu_m_axi_if.awready) -> (cptra_ss_mcu_lsu_m_axi_if.awsize < 3), core_clk, !cptra_ss_rst_b_i)
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWVALID = cptra_ss_mcu_lsu_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWADDR[31:0]  = cptra_ss_mcu_lsu_m_axi_if.awaddr[31:0] & 32'hFFFF_FFFC /*FIXME*/;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWID    = cptra_ss_mcu_lsu_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWLEN   = cptra_ss_mcu_lsu_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWSIZE  = 2; // FIXME cptra_ss_mcu_lsu_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWBURST = cptra_ss_mcu_lsu_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWLOCK  = cptra_ss_mcu_lsu_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWUSER  = cptra_ss_mcu_lsu_m_axi_if.awuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWCACHE  = cptra_ss_mcu_lsu_m_axi_if_awcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWPROT   = cptra_ss_mcu_lsu_m_axi_if_awprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWQOS    = cptra_ss_mcu_lsu_m_axi_if_awqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWREGION = cptra_ss_mcu_lsu_m_axi_if_awregion;
    assign cptra_ss_mcu_lsu_m_axi_if.awready              = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].AWREADY;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WVALID  = cptra_ss_mcu_lsu_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WDATA   = cptra_ss_mcu_lsu_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WSTRB   = cptra_ss_mcu_lsu_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WLAST   = cptra_ss_mcu_lsu_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WUSER  = cptra_ss_mcu_lsu_m_axi_if.wuser;
    assign cptra_ss_mcu_lsu_m_axi_if.wready               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].WREADY;
    assign cptra_ss_mcu_lsu_m_axi_if.bvalid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].BVALID;
    assign cptra_ss_mcu_lsu_m_axi_if.bresp                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].BRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.buser                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].BUSER;
    assign cptra_ss_mcu_lsu_m_axi_if.bid                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].BID;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].BREADY  = cptra_ss_mcu_lsu_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARVALID = cptra_ss_mcu_lsu_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARADDR[31:0]  = cptra_ss_mcu_lsu_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARID    = cptra_ss_mcu_lsu_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARLEN   = cptra_ss_mcu_lsu_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARSIZE  = cptra_ss_mcu_lsu_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARBURST = cptra_ss_mcu_lsu_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARLOCK  = cptra_ss_mcu_lsu_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARUSER  = cptra_ss_mcu_lsu_m_axi_if.aruser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARCACHE  = cptra_ss_mcu_lsu_m_axi_if_arcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARPROT   = cptra_ss_mcu_lsu_m_axi_if_arprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARQOS    = cptra_ss_mcu_lsu_m_axi_if_arqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARREGION = cptra_ss_mcu_lsu_m_axi_if_arregion;
    assign cptra_ss_mcu_lsu_m_axi_if.arready              = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].ARREADY;
    assign cptra_ss_mcu_lsu_m_axi_if.rvalid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RVALID;
    assign cptra_ss_mcu_lsu_m_axi_if.rdata                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_lsu_m_axi_if.rresp                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.ruser                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RUSER;
    assign cptra_ss_mcu_lsu_m_axi_if.rid                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RID;
    assign cptra_ss_mcu_lsu_m_axi_if.rlast                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RLAST;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_LSU_IDX].RREADY  = cptra_ss_mcu_lsu_m_axi_if.rready;

    //Interconnect 1 - MCU IFU
    // FIXME remove this downsizer once Avery VIP supports downsizing
    caliptra_ss_top_tb_axi_64_to_32_downsizer i_cptra_ss_mcu_ifu_m_axi_if_downsizer (
        .clk              (core_clk                          ),
        .rst_n            (cptra_ss_rst_b_i                  ),
        .m_axi_if         (cptra_ss_mcu_ifu_m_axi_if         ),
        .m_axi_if_arcache (cptra_ss_mcu_ifu_m_axi_if_arcache ),
        .m_axi_if_arprot  (cptra_ss_mcu_ifu_m_axi_if_arprot  ),
        .m_axi_if_arregion(cptra_ss_mcu_ifu_m_axi_if_arregion),
        .m_axi_if_arqos   (cptra_ss_mcu_ifu_m_axi_if_arqos   ),
        .m_axi_if_awcache (cptra_ss_mcu_ifu_m_axi_if_awcache ),
        .m_axi_if_awprot  (cptra_ss_mcu_ifu_m_axi_if_awprot  ),
        .m_axi_if_awregion(cptra_ss_mcu_ifu_m_axi_if_awregion),
        .m_axi_if_awqos   (cptra_ss_mcu_ifu_m_axi_if_awqos   ),
        .s_axi_if         (cptra_ss_mcu_ifu_ds_m_axi_if         ),
        .s_axi_if_arcache (cptra_ss_mcu_ifu_ds_m_axi_if_arcache ),
        .s_axi_if_arprot  (cptra_ss_mcu_ifu_ds_m_axi_if_arprot  ),
        .s_axi_if_arregion(cptra_ss_mcu_ifu_ds_m_axi_if_arregion),
        .s_axi_if_arqos   (cptra_ss_mcu_ifu_ds_m_axi_if_arqos   ),
        .s_axi_if_awcache (cptra_ss_mcu_ifu_ds_m_axi_if_awcache ),
        .s_axi_if_awprot  (cptra_ss_mcu_ifu_ds_m_axi_if_awprot  ),
        .s_axi_if_awregion(cptra_ss_mcu_ifu_ds_m_axi_if_awregion),
        .s_axi_if_awqos   (cptra_ss_mcu_ifu_ds_m_axi_if_awqos   )
    );
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWVALID = cptra_ss_mcu_ifu_ds_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWADDR[31:0]  = cptra_ss_mcu_ifu_ds_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWID    = cptra_ss_mcu_ifu_ds_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWLEN   = cptra_ss_mcu_ifu_ds_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWSIZE  = cptra_ss_mcu_ifu_ds_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWBURST = cptra_ss_mcu_ifu_ds_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWLOCK  = cptra_ss_mcu_ifu_ds_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWUSER  = cptra_ss_mcu_ifu_ds_m_axi_if.awuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWCACHE  = cptra_ss_mcu_ifu_ds_m_axi_if_awcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWPROT   = cptra_ss_mcu_ifu_ds_m_axi_if_awprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWQOS    = cptra_ss_mcu_ifu_ds_m_axi_if_awqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWREGION = cptra_ss_mcu_ifu_ds_m_axi_if_awregion;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.awready                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].AWREADY;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WVALID  = cptra_ss_mcu_ifu_ds_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WDATA   = cptra_ss_mcu_ifu_ds_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WSTRB   = cptra_ss_mcu_ifu_ds_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WLAST   = cptra_ss_mcu_ifu_ds_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WUSER  = cptra_ss_mcu_ifu_ds_m_axi_if.wuser;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.wready                 = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].WREADY;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.bvalid                 = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].BVALID;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.bresp                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].BRESP;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.buser                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].BUSER;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.bid                    = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].BID;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].BREADY  = cptra_ss_mcu_ifu_ds_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARVALID = cptra_ss_mcu_ifu_ds_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARADDR[31:0]  = cptra_ss_mcu_ifu_ds_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARID    = cptra_ss_mcu_ifu_ds_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARLEN   = cptra_ss_mcu_ifu_ds_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARSIZE  = cptra_ss_mcu_ifu_ds_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARBURST = cptra_ss_mcu_ifu_ds_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARLOCK  = cptra_ss_mcu_ifu_ds_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARUSER  = cptra_ss_mcu_ifu_ds_m_axi_if.aruser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARCACHE  = cptra_ss_mcu_ifu_ds_m_axi_if_arcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARPROT   = cptra_ss_mcu_ifu_ds_m_axi_if_arprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARQOS    = cptra_ss_mcu_ifu_ds_m_axi_if_arqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARREGION = cptra_ss_mcu_ifu_ds_m_axi_if_arregion;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.arready                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].ARREADY;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.rvalid                 = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RVALID;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.rdata                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_ifu_ds_m_axi_if.rresp                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RRESP;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.ruser                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RUSER;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.rid                    = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RID;
    assign cptra_ss_mcu_ifu_ds_m_axi_if.rlast                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RLAST;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_IFU_IDX].RREADY  = cptra_ss_mcu_ifu_ds_m_axi_if.rready;

    //Interconnect 2 - SysBus
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWVALID = cptra_ss_mcu_sb_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWADDR[31:0]  = cptra_ss_mcu_sb_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWID    = cptra_ss_mcu_sb_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWLEN   = cptra_ss_mcu_sb_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWSIZE  = cptra_ss_mcu_sb_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWBURST = cptra_ss_mcu_sb_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWLOCK  = cptra_ss_mcu_sb_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWUSER  = cptra_ss_mcu_sb_m_axi_if.awuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWCACHE  = cptra_ss_mcu_sb_m_axi_if_awcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWPROT   = cptra_ss_mcu_sb_m_axi_if_awprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWQOS    = cptra_ss_mcu_sb_m_axi_if_awqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWREGION = cptra_ss_mcu_sb_m_axi_if_awregion;
    assign cptra_ss_mcu_sb_m_axi_if.awready              = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].AWREADY;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WVALID  = cptra_ss_mcu_sb_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WDATA   = cptra_ss_mcu_sb_m_axi_if.wdata;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WSTRB   = cptra_ss_mcu_sb_m_axi_if.wstrb;// Native 64-bit width, no dwidth conversion
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WLAST   = cptra_ss_mcu_sb_m_axi_if.wlast;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WUSER  = cptra_ss_mcu_sb_m_axi_if.wuser;
    assign cptra_ss_mcu_sb_m_axi_if.wready               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].WREADY;
    assign cptra_ss_mcu_sb_m_axi_if.bvalid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].BVALID;
    assign cptra_ss_mcu_sb_m_axi_if.bresp                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].BRESP;
    assign cptra_ss_mcu_sb_m_axi_if.buser                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].BUSER;
    assign cptra_ss_mcu_sb_m_axi_if.bid                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].BID;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].BREADY  = cptra_ss_mcu_sb_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARVALID = cptra_ss_mcu_sb_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARADDR[31:0]  = cptra_ss_mcu_sb_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARID    = cptra_ss_mcu_sb_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARLEN   = cptra_ss_mcu_sb_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARSIZE  = cptra_ss_mcu_sb_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARBURST = cptra_ss_mcu_sb_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARLOCK  = cptra_ss_mcu_sb_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARUSER  = cptra_ss_mcu_sb_m_axi_if.aruser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARCACHE  = cptra_ss_mcu_sb_m_axi_if_arcache;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARPROT   = cptra_ss_mcu_sb_m_axi_if_arprot;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARQOS    = cptra_ss_mcu_sb_m_axi_if_arqos;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARREGION = cptra_ss_mcu_sb_m_axi_if_arregion;
    assign cptra_ss_mcu_sb_m_axi_if.arready              = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].ARREADY;
    assign cptra_ss_mcu_sb_m_axi_if.rvalid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RVALID;
    assign cptra_ss_mcu_sb_m_axi_if.rdata                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RDATA;// Native 64-bit width, no dwidth conversion
    assign cptra_ss_mcu_sb_m_axi_if.rresp                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RRESP;
    assign cptra_ss_mcu_sb_m_axi_if.ruser                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RUSER;
    assign cptra_ss_mcu_sb_m_axi_if.rid                  = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RID;
    assign cptra_ss_mcu_sb_m_axi_if.rlast                = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RLAST;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_MCU_SB_IDX].RREADY  = cptra_ss_mcu_sb_m_axi_if.rready;

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
    assign cptra_ss_cptra_core_s_axi_if.awvalid           = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWVALID;
    assign cptra_ss_cptra_core_s_axi_if.awaddr            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWADDR[31:0];
    assign cptra_ss_cptra_core_s_axi_if.awid              = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWID;
    assign cptra_ss_cptra_core_s_axi_if.awlen             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWLEN;
    assign cptra_ss_cptra_core_s_axi_if.awsize            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWSIZE;
    assign cptra_ss_cptra_core_s_axi_if.awburst           = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWBURST;
    assign cptra_ss_cptra_core_s_axi_if.awlock            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWLOCK;
    assign cptra_ss_cptra_core_s_axi_if.awuser            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].AWREADY = cptra_ss_cptra_core_s_axi_if.awready;
    assign cptra_ss_cptra_core_s_axi_if.wvalid            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WVALID;
    assign cptra_ss_cptra_core_s_axi_if.wdata             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WDATA;
    assign cptra_ss_cptra_core_s_axi_if.wstrb             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WSTRB;
    assign cptra_ss_cptra_core_s_axi_if.wlast             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WLAST;
    assign cptra_ss_cptra_core_s_axi_if.wuser             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].WREADY  = cptra_ss_cptra_core_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].BVALID  = cptra_ss_cptra_core_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].BRESP   = cptra_ss_cptra_core_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].BUSER   = cptra_ss_cptra_core_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].BID     = cptra_ss_cptra_core_s_axi_if.bid;
    assign cptra_ss_cptra_core_s_axi_if.bready            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].BREADY;
    assign cptra_ss_cptra_core_s_axi_if.arvalid           = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARVALID;
    assign cptra_ss_cptra_core_s_axi_if.araddr            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARADDR[31:0];
    assign cptra_ss_cptra_core_s_axi_if.arid              = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARID;
    assign cptra_ss_cptra_core_s_axi_if.arlen             = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARLEN;
    assign cptra_ss_cptra_core_s_axi_if.arsize            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARSIZE;
    assign cptra_ss_cptra_core_s_axi_if.arburst           = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARBURST;
    assign cptra_ss_cptra_core_s_axi_if.arlock            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARLOCK;
    assign cptra_ss_cptra_core_s_axi_if.aruser            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].ARREADY = cptra_ss_cptra_core_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RUSER   = cptra_ss_cptra_core_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RVALID  = cptra_ss_cptra_core_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RDATA   = 64'(cptra_ss_cptra_core_s_axi_if.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RRESP   = cptra_ss_cptra_core_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RID     = cptra_ss_cptra_core_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RLAST   = cptra_ss_cptra_core_s_axi_if.rlast;
    assign cptra_ss_cptra_core_s_axi_if.rready            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX].RREADY;

    //Interconnect MGR 3 - cptra dma
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWVALID = cptra_ss_cptra_core_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWADDR[31:0]  = cptra_ss_cptra_core_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWID    = cptra_ss_cptra_core_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWLEN   = cptra_ss_cptra_core_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWSIZE  = cptra_ss_cptra_core_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWBURST = cptra_ss_cptra_core_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWLOCK  = cptra_ss_cptra_core_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWUSER  = cptra_ss_cptra_core_m_axi_if.awuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWCACHE  = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWPROT   = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWQOS    = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWREGION = '0;
    assign cptra_ss_cptra_core_m_axi_if.awready           = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].AWREADY;

    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WVALID  = cptra_ss_cptra_core_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WUSER   = cptra_ss_cptra_core_m_axi_if.wuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WDATA   = cptra_ss_cptra_core_m_axi_if.wdata;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WSTRB   = cptra_ss_cptra_core_m_axi_if.wstrb;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WLAST   = cptra_ss_cptra_core_m_axi_if.wlast;
    assign cptra_ss_cptra_core_m_axi_if.wready            = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].WREADY;

    assign cptra_ss_cptra_core_m_axi_if.bvalid            = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].BVALID;
    assign cptra_ss_cptra_core_m_axi_if.bresp             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].BRESP;
    assign cptra_ss_cptra_core_m_axi_if.bid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].BID;
    assign cptra_ss_cptra_core_m_axi_if.buser             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].BUSER;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].BREADY  = cptra_ss_cptra_core_m_axi_if.bready;

    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARVALID = cptra_ss_cptra_core_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARADDR[31:0]  = cptra_ss_cptra_core_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARID    = cptra_ss_cptra_core_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARLEN   = cptra_ss_cptra_core_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARSIZE  = cptra_ss_cptra_core_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARBURST = cptra_ss_cptra_core_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARLOCK  = cptra_ss_cptra_core_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARUSER  = cptra_ss_cptra_core_m_axi_if.aruser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARCACHE  = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARPROT   = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARQOS    = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARREGION = '0;
    assign cptra_ss_cptra_core_m_axi_if.arready           = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].ARREADY;
    assign cptra_ss_cptra_core_m_axi_if.rvalid            = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RVALID;
    assign cptra_ss_cptra_core_m_axi_if.rdata             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RDATA;
    assign cptra_ss_cptra_core_m_axi_if.rresp             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RRESP;
    assign cptra_ss_cptra_core_m_axi_if.ruser             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RUSER;
    assign cptra_ss_cptra_core_m_axi_if.rid               = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RID;
    assign cptra_ss_cptra_core_m_axi_if.rlast             = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RLAST;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_CPTRA_DMA_IDX].RREADY  = cptra_ss_cptra_core_m_axi_if.rready;

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
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWVALID  = m_axi_bfm_if.awvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWADDR[31:0]   = m_axi_bfm_if.awaddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWID     = m_axi_bfm_if.awid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWLEN    = m_axi_bfm_if.awlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWSIZE   = m_axi_bfm_if.awsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWBURST  = m_axi_bfm_if.awburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWLOCK   = m_axi_bfm_if.awlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWUSER   = m_axi_bfm_if.awuser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWCACHE  = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWPROT   = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWQOS    = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWREGION = '0;
    assign m_axi_bfm_if.awready                   = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].AWREADY;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WVALID   = m_axi_bfm_if.wvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WDATA    = m_axi_bfm_if.wdata;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WSTRB    = m_axi_bfm_if.wstrb;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WLAST    = m_axi_bfm_if.wlast;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WUSER   = m_axi_bfm_if.wuser;
    assign m_axi_bfm_if.wready                    = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].WREADY;
    assign m_axi_bfm_if.bvalid                    = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].BVALID;
    assign m_axi_bfm_if.bresp                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].BRESP;
    assign m_axi_bfm_if.bid                       = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].BID;
    assign m_axi_bfm_if.buser                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].BUSER;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].BREADY   = m_axi_bfm_if.bready;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARVALID  = m_axi_bfm_if.arvalid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARADDR[31:0]   = m_axi_bfm_if.araddr;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARID     = m_axi_bfm_if.arid;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARLEN    = m_axi_bfm_if.arlen;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARSIZE   = m_axi_bfm_if.arsize;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARBURST  = m_axi_bfm_if.arburst;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARLOCK   = m_axi_bfm_if.arlock;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARUSER   = m_axi_bfm_if.aruser;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARCACHE  = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARPROT   = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARQOS    = '0;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARREGION = '0;
    assign m_axi_bfm_if.arready                   = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].ARREADY;
    assign m_axi_bfm_if.rvalid                    = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RVALID;
    assign m_axi_bfm_if.rdata                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RDATA;
    assign m_axi_bfm_if.rresp                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RRESP;
    assign m_axi_bfm_if.rid                       = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RID;
    assign m_axi_bfm_if.rlast                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RLAST;
    assign m_axi_bfm_if.ruser                     = axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RUSER;
    assign axi_interconnect.mintf_arr[`CSS_INTC_MINTF_SOC_BFM_IDX].RREADY   = m_axi_bfm_if.rready;

    assign cptra_ss_mci_s_axi_if.awvalid                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWVALID;
    assign cptra_ss_mci_s_axi_if.awaddr                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWADDR[31:0];
    assign cptra_ss_mci_s_axi_if.awid                         = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWID;
    assign cptra_ss_mci_s_axi_if.awlen                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWLEN;
    assign cptra_ss_mci_s_axi_if.awsize                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWSIZE;
    assign cptra_ss_mci_s_axi_if.awburst                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWBURST;
    assign cptra_ss_mci_s_axi_if.awlock                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWLOCK;
    assign cptra_ss_mci_s_axi_if.awuser                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].AWREADY = cptra_ss_mci_s_axi_if.awready;
    assign cptra_ss_mci_s_axi_if.wvalid                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WVALID;
    assign cptra_ss_mci_s_axi_if.wdata                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WDATA;
    assign cptra_ss_mci_s_axi_if.wstrb                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WSTRB;
    assign cptra_ss_mci_s_axi_if.wlast                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WLAST;
    assign cptra_ss_mci_s_axi_if.wuser                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].WREADY      = cptra_ss_mci_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].BVALID      = cptra_ss_mci_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].BRESP       = cptra_ss_mci_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].BUSER       = cptra_ss_mci_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].BID         = cptra_ss_mci_s_axi_if.bid;
    assign cptra_ss_mci_s_axi_if.bready                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].BREADY;
    assign cptra_ss_mci_s_axi_if.arvalid                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARVALID;
    assign cptra_ss_mci_s_axi_if.araddr                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARADDR[31:0];
    assign cptra_ss_mci_s_axi_if.arid                         = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARID;
    assign cptra_ss_mci_s_axi_if.arlen                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARLEN;
    assign cptra_ss_mci_s_axi_if.arsize                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARSIZE;
    assign cptra_ss_mci_s_axi_if.arburst                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARBURST;
    assign cptra_ss_mci_s_axi_if.arlock                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARLOCK;
    assign cptra_ss_mci_s_axi_if.aruser                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].ARREADY       = cptra_ss_mci_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RVALID        = cptra_ss_mci_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RUSER         = cptra_ss_mci_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RDATA         = 64'(cptra_ss_mci_s_axi_if.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RRESP         = cptra_ss_mci_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RID           = cptra_ss_mci_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RLAST         = cptra_ss_mci_s_axi_if.rlast;
    assign cptra_ss_mci_s_axi_if.rready                         = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCI_IDX].RREADY;

    //Interconnect 5
    assign cptra_ss_otp_core_axi_wr_req_i.awaddr  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWADDR[31:0];
    assign cptra_ss_otp_core_axi_wr_req_i.awburst = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWBURST;
    assign cptra_ss_otp_core_axi_wr_req_i.awsize  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWSIZE;
    assign cptra_ss_otp_core_axi_wr_req_i.awlen   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWLEN;
    assign cptra_ss_otp_core_axi_wr_req_i.awuser  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWUSER;
    assign cptra_ss_otp_core_axi_wr_req_i.awid    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWID;
    assign cptra_ss_otp_core_axi_wr_req_i.awlock  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWLOCK;
    assign cptra_ss_otp_core_axi_wr_req_i.awvalid = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.wdata   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].WDATA;
    assign cptra_ss_otp_core_axi_wr_req_i.wstrb   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].WSTRB;
    assign cptra_ss_otp_core_axi_wr_req_i.wlast   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].WLAST;
    assign cptra_ss_otp_core_axi_wr_req_i.wvalid  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].WVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.bready  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].BREADY;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].AWREADY = cptra_ss_otp_core_axi_wr_rsp_o.awready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].WREADY  = cptra_ss_otp_core_axi_wr_rsp_o.wready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].BRESP   = cptra_ss_otp_core_axi_wr_rsp_o.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].BID     = cptra_ss_otp_core_axi_wr_rsp_o.bid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].BVALID  = cptra_ss_otp_core_axi_wr_rsp_o.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].BUSER   = '0; // FIXME connect?
    assign cptra_ss_otp_core_axi_rd_req_i.araddr  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARADDR[31:0];
    assign cptra_ss_otp_core_axi_rd_req_i.arburst = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARBURST;
    assign cptra_ss_otp_core_axi_rd_req_i.arsize  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARSIZE;
    assign cptra_ss_otp_core_axi_rd_req_i.arlen   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARLEN;
    assign cptra_ss_otp_core_axi_rd_req_i.aruser  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARUSER;
    assign cptra_ss_otp_core_axi_rd_req_i.arid    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARID;
    assign cptra_ss_otp_core_axi_rd_req_i.arlock  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARLOCK;
    assign cptra_ss_otp_core_axi_rd_req_i.arvalid = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARVALID;
    assign cptra_ss_otp_core_axi_rd_req_i.rready  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RREADY;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].ARREADY = cptra_ss_otp_core_axi_rd_rsp_o.arready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RDATA   = 64'(cptra_ss_otp_core_axi_rd_rsp_o.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RRESP   = cptra_ss_otp_core_axi_rd_rsp_o.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RID     = cptra_ss_otp_core_axi_rd_rsp_o.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RLAST   = cptra_ss_otp_core_axi_rd_rsp_o.rlast;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RVALID  = cptra_ss_otp_core_axi_rd_rsp_o.rvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_FC_IDX].RUSER   = '0 ; // FIXME

    //Interconnect 6
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].AWREADY = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].WREADY = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].BRESP = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].BID = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].BVALID = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].BUSER  = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].ARREADY = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RDATA = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RRESP = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RID = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RLAST = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RUSER = '0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC1_IDX].RVALID = '0;

    //Interconnect 7 - LCC
    assign cptra_ss_lc_axi_wr_req_i.awvalid = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWVALID;
    assign cptra_ss_lc_axi_wr_req_i.awaddr  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWADDR[31:0];
    assign cptra_ss_lc_axi_wr_req_i.awid    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWID;
    assign cptra_ss_lc_axi_wr_req_i.awlen   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWLEN;
    assign cptra_ss_lc_axi_wr_req_i.awsize  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWSIZE;
    assign cptra_ss_lc_axi_wr_req_i.awburst = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWBURST;
    assign cptra_ss_lc_axi_wr_req_i.awlock  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWLOCK;
    assign cptra_ss_lc_axi_wr_req_i.awuser  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].AWREADY = cptra_ss_lc_axi_wr_rsp_o.awready;

    assign cptra_ss_lc_axi_wr_req_i.wvalid = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].WVALID;
    assign cptra_ss_lc_axi_wr_req_i.wdata  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].WDATA;
    assign cptra_ss_lc_axi_wr_req_i.wstrb  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].WSTRB;
    assign cptra_ss_lc_axi_wr_req_i.wlast  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].WLAST;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].WREADY = cptra_ss_lc_axi_wr_rsp_o.wready;

    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].BRESP  = cptra_ss_lc_axi_wr_rsp_o.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].BID    = cptra_ss_lc_axi_wr_rsp_o.bid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].BVALID = cptra_ss_lc_axi_wr_rsp_o.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].BUSER  = '0; // FIXME?
    assign cptra_ss_lc_axi_wr_req_i.bready  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].BREADY;

    assign cptra_ss_lc_axi_rd_req_i.arvalid = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARVALID;
    assign cptra_ss_lc_axi_rd_req_i.araddr  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARADDR[31:0];
    assign cptra_ss_lc_axi_rd_req_i.arid    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARID;
    assign cptra_ss_lc_axi_rd_req_i.arlen   = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARLEN;
    assign cptra_ss_lc_axi_rd_req_i.arsize  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARSIZE;
    assign cptra_ss_lc_axi_rd_req_i.arburst = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARBURST;
    assign cptra_ss_lc_axi_rd_req_i.arlock  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARLOCK;
    assign cptra_ss_lc_axi_rd_req_i.aruser  = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].ARREADY = cptra_ss_lc_axi_rd_rsp_o.arready;

    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RDATA   = 64'(cptra_ss_lc_axi_rd_rsp_o.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RRESP   = cptra_ss_lc_axi_rd_rsp_o.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RID     = cptra_ss_lc_axi_rd_rsp_o.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RLAST   = cptra_ss_lc_axi_rd_rsp_o.rlast;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RUSER   = '0; // FIXME
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RVALID  = cptra_ss_lc_axi_rd_rsp_o.rvalid;
    assign cptra_ss_lc_axi_rd_req_i.rready = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_LCC_IDX].RREADY;

    //Interconnect 1 - I3C
    assign cptra_ss_i3c_s_axi_if.awvalid                    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWVALID;
    assign cptra_ss_i3c_s_axi_if.awaddr                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWADDR[31:0];
    assign cptra_ss_i3c_s_axi_if.awid                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWID;
    assign cptra_ss_i3c_s_axi_if.awlen                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWLEN;
    assign cptra_ss_i3c_s_axi_if.awsize                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWSIZE;
    assign cptra_ss_i3c_s_axi_if.awburst                    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWBURST;
    assign cptra_ss_i3c_s_axi_if.awlock                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWLOCK;
    assign cptra_ss_i3c_s_axi_if.awuser                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].AWREADY = cptra_ss_i3c_s_axi_if.awready;
    assign cptra_ss_i3c_s_axi_if.wvalid                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WVALID;
    assign cptra_ss_i3c_s_axi_if.wdata                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WDATA;
    assign cptra_ss_i3c_s_axi_if.wstrb                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WSTRB;
    assign cptra_ss_i3c_s_axi_if.wlast                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WLAST;
    assign cptra_ss_i3c_s_axi_if.wuser                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].WREADY  = cptra_ss_i3c_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].BVALID  = cptra_ss_i3c_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].BRESP   = cptra_ss_i3c_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].BUSER   = cptra_ss_i3c_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].BID     = cptra_ss_i3c_s_axi_if.bid;
    assign cptra_ss_i3c_s_axi_if.bready                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].BREADY;
    assign cptra_ss_i3c_s_axi_if.arvalid                    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARVALID;
    assign cptra_ss_i3c_s_axi_if.araddr                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARADDR[31:0];
    assign cptra_ss_i3c_s_axi_if.arid                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARID;
    assign cptra_ss_i3c_s_axi_if.arlen                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARLEN;
    assign cptra_ss_i3c_s_axi_if.arsize                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARSIZE;
    assign cptra_ss_i3c_s_axi_if.arburst                    = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARBURST;
    assign cptra_ss_i3c_s_axi_if.arlock                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARLOCK;
    assign cptra_ss_i3c_s_axi_if.aruser                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].ARREADY = cptra_ss_i3c_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RVALID  = cptra_ss_i3c_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RDATA   = 64'(cptra_ss_i3c_s_axi_if.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RRESP   = cptra_ss_i3c_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RUSER   = cptra_ss_i3c_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RID     = cptra_ss_i3c_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RLAST   = cptra_ss_i3c_s_axi_if.rlast;
    assign cptra_ss_i3c_s_axi_if.rready                     = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_I3C_IDX].RREADY;

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
        .ADDR_WIDTH(CPTRA_SS_ROM_MEM_ADDR_W),
        .DATA_WIDTH(CPTRA_SS_ROM_DATA_W)
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
    logic [CPTRA_MBOX_ADDR_W-1:0] cptra_ss_cptra_core_mbox_sram_addr_o;
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

    assign ready_for_fuses         = 0;
    assign ready_for_mb_processing = 0;
    assign mailbox_data_avail      = 0;

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
        .mbox_sram_addr (cptra_ss_cptra_core_mbox_sram_addr_o ),
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
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_NC0_IDX].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32] = 32'h0;

    assign cptra_ss_mcu_rom_s_axi_if.awvalid                      = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWVALID;
    assign cptra_ss_mcu_rom_s_axi_if.awaddr                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWADDR[31:0];
    assign cptra_ss_mcu_rom_s_axi_if.awid                         = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWID;
    assign cptra_ss_mcu_rom_s_axi_if.awlen                        = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWLEN;
    assign cptra_ss_mcu_rom_s_axi_if.awsize                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWSIZE;
    assign cptra_ss_mcu_rom_s_axi_if.awburst                      = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWBURST;
    assign cptra_ss_mcu_rom_s_axi_if.awlock                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWLOCK;
    assign cptra_ss_mcu_rom_s_axi_if.awuser                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].AWREADY     = 0;//cptra_ss_mcu_rom_s_axi_if.awready;
    assign cptra_ss_mcu_rom_s_axi_if.wvalid                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WVALID;
    assign cptra_ss_mcu_rom_s_axi_if.wdata                        = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WDATA;
    assign cptra_ss_mcu_rom_s_axi_if.wstrb                        = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WSTRB;
    assign cptra_ss_mcu_rom_s_axi_if.wlast                        = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WLAST;
    assign cptra_ss_mcu_rom_s_axi_if.wuser                        = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].WREADY      = 0;//cptra_ss_mcu_rom_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].BVALID      = 0;//cptra_ss_mcu_rom_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].BRESP       = 0;//cptra_ss_mcu_rom_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].BUSER       = 0;//cptra_ss_mcu_rom_s_axi_if.buser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].BID         = 0;//cptra_ss_mcu_rom_s_axi_if.bid;
    assign cptra_ss_mcu_rom_s_axi_if.bready                       = 0;//axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].BREADY;
    assign cptra_ss_mcu_rom_s_axi_if.arvalid                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARVALID;
    assign cptra_ss_mcu_rom_s_axi_if.araddr                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARADDR[31:0];
    assign cptra_ss_mcu_rom_s_axi_if.arid                         = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARID;
    assign cptra_ss_mcu_rom_s_axi_if.arlen                        = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARLEN;
    assign cptra_ss_mcu_rom_s_axi_if.arsize                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARSIZE;
    assign cptra_ss_mcu_rom_s_axi_if.arburst                      = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARBURST;
    assign cptra_ss_mcu_rom_s_axi_if.arlock                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARLOCK;
    assign cptra_ss_mcu_rom_s_axi_if.aruser                       = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARUSER;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].ARREADY       = cptra_ss_mcu_rom_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RVALID        = cptra_ss_mcu_rom_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RDATA         = 64'(cptra_ss_mcu_rom_s_axi_if.rdata);
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RRESP         = cptra_ss_mcu_rom_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RUSER         = cptra_ss_mcu_rom_s_axi_if.ruser;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RID           = cptra_ss_mcu_rom_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RLAST         = cptra_ss_mcu_rom_s_axi_if.rlast;
    assign cptra_ss_mcu_rom_s_axi_if.rready            = axi_interconnect.sintf_arr[`CSS_INTC_SINTF_MCU_ROM_IDX].RREADY;



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

    // JTAG DPI
    jtagdpi #(
        .Name           ("jtag2"),
        .ListenPort     (7000)
    ) jtagdpi_lcc (
        .clk_i          (core_clk),
        .rst_ni         (cptra_ss_rst_b_i),
        .jtag_tck       (cptra_ss_lc_ctrl_jtag_i.tck),
        .jtag_tms       (cptra_ss_lc_ctrl_jtag_i.tms),
        .jtag_tdi       (cptra_ss_lc_ctrl_jtag_i.tdi),
        .jtag_tdo       (cptra_ss_lc_ctrl_jtag_o.tdo),
        .jtag_trst_n    (cptra_ss_lc_ctrl_jtag_i.trst_n),
        .jtag_srst_n    ()
    );


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

    wire cptra_ss_sel_od_pp_o;
    logic cptra_ss_i3c_scl_oe;
    logic cptra_ss_i3c_sda_oe;
    
    logic cptra_ss_i3c_recovery_payload_available_o;
    logic cptra_ss_i3c_recovery_image_activated_o;

    logic cptra_i3c_axi_user_id_filtering_enable_i;
    assign cptra_i3c_axi_user_id_filtering_enable_i = 1'b1;

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

//if I3C_BOOT_USING_ENTDAA is defined, then set the dynamic address to 0
`ifdef I3C_BOOT_USING_ENTDAA
        master0.set("add_i3c_dev_da",0);
        master0.set("add_i3c_dev_da",0);
`endif

//if I3C_BOOT_USING_ENTDAA is not defined, then use the static address
`ifndef I3C_BOOT_USING_ENTDAA
        master0.set("add_i3c_dev", 7'h5A); // virtual target 0 static address
        master0.set("add_i3c_dev", 7'h5B); // virtual target 1 static address - recovery target
`endif
        
        master0.cfg_info.receive_all_txn = 0;


        // --- I3C env ---
        i3c_env0 = new("i3c_env0");
        i3c_env0.add_master(master0);

        // run test for i3C
        if($value$plusargs("AVY_TEST=%s", avy_test_name)) begin
            $display("Waiting for 400us before Running I3C test [%s]", avy_test_name);
            #400us;  // system boot delay
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
        .MCU_MBOX1_VALID_AXI_USER(MCU_MBOX1_VALID_AXI_USER),
        .LCC_SecVolatileRawUnlockEn(LCC_SecVolatileRawUnlockEn)
    )
    caliptra_ss_dut (

        .cptra_ss_clk_i(core_clk),
        .cptra_ss_rdc_clk_cg_o,
        .cptra_ss_mcu_clk_cg_o,
        .cptra_ss_pwrgood_i(cptra_ss_pwrgood_i),
        .cptra_ss_rst_b_i(cptra_ss_rst_b_i),
        .cptra_ss_mci_cptra_rst_b_i(cptra_ss_mci_cptra_rst_b_o),
        .cptra_ss_mci_cptra_rst_b_o,
        .cptra_ss_mcu_rst_b_o,
        .cptra_ss_mcu_rst_b_i(cptra_ss_mcu_rst_b_o),

    // RDC related signals
        .cptra_ss_warm_reset_rdc_clk_dis_o,
        .cptra_ss_early_warm_reset_warn_o,
        .cptra_ss_mcu_fw_update_rdc_clk_dis_o,
 

    //SoC AXI Interface
        .cptra_ss_cptra_core_s_axi_if_r_sub(cptra_ss_cptra_core_s_axi_if.r_sub),
        .cptra_ss_cptra_core_s_axi_if_w_sub(cptra_ss_cptra_core_s_axi_if.w_sub),

    // AXI Manager INF
        .cptra_ss_cptra_core_m_axi_if_r_mgr(cptra_ss_cptra_core_m_axi_if.r_mgr),
        .cptra_ss_cptra_core_m_axi_if_w_mgr(cptra_ss_cptra_core_m_axi_if.w_mgr),

    //MCU ROM Sub Interface
        .cptra_ss_mcu_rom_s_axi_if_r_sub(cptra_ss_mcu_rom_s_axi_if.r_sub),
        .cptra_ss_mcu_rom_s_axi_if_w_sub(cptra_ss_mcu_rom_s_axi_if.w_sub),
        .mcu_rom_mem_export_if,

    //MCI AXI Sub Interface
        .cptra_ss_mci_s_axi_if_r_sub(cptra_ss_mci_s_axi_if.r_sub),
        .cptra_ss_mci_s_axi_if_w_sub(cptra_ss_mci_s_axi_if.w_sub),

    // AXI Manager INF

        .cptra_ss_mcu_lsu_m_axi_if_r_mgr(cptra_ss_mcu_lsu_m_axi_if.r_mgr),
        .cptra_ss_mcu_lsu_m_axi_if_w_mgr(cptra_ss_mcu_lsu_m_axi_if.w_mgr),
        .cptra_ss_mcu_lsu_m_axi_if_awcache,
        .cptra_ss_mcu_lsu_m_axi_if_arcache,
        .cptra_ss_mcu_lsu_m_axi_if_awprot,
        .cptra_ss_mcu_lsu_m_axi_if_arprot,
        .cptra_ss_mcu_lsu_m_axi_if_awregion,
        .cptra_ss_mcu_lsu_m_axi_if_arregion,
        .cptra_ss_mcu_lsu_m_axi_if_awqos,
        .cptra_ss_mcu_lsu_m_axi_if_arqos,
        .cptra_ss_mcu_ifu_m_axi_if_r_mgr(cptra_ss_mcu_ifu_m_axi_if.r_mgr),
        .cptra_ss_mcu_ifu_m_axi_if_w_mgr(cptra_ss_mcu_ifu_m_axi_if.w_mgr),
        .cptra_ss_mcu_ifu_m_axi_if_awcache,
        .cptra_ss_mcu_ifu_m_axi_if_arcache,
        .cptra_ss_mcu_ifu_m_axi_if_awprot,
        .cptra_ss_mcu_ifu_m_axi_if_arprot,
        .cptra_ss_mcu_ifu_m_axi_if_awregion,
        .cptra_ss_mcu_ifu_m_axi_if_arregion,
        .cptra_ss_mcu_ifu_m_axi_if_awqos,
        .cptra_ss_mcu_ifu_m_axi_if_arqos,
        .cptra_ss_mcu_sb_m_axi_if_r_mgr(cptra_ss_mcu_sb_m_axi_if.r_mgr),
        .cptra_ss_mcu_sb_m_axi_if_w_mgr(cptra_ss_mcu_sb_m_axi_if.w_mgr),
        .cptra_ss_mcu_sb_m_axi_if_awcache,
        .cptra_ss_mcu_sb_m_axi_if_arcache,
        .cptra_ss_mcu_sb_m_axi_if_awprot,
        .cptra_ss_mcu_sb_m_axi_if_arprot,
        .cptra_ss_mcu_sb_m_axi_if_awregion,
        .cptra_ss_mcu_sb_m_axi_if_arregion,
        .cptra_ss_mcu_sb_m_axi_if_awqos,
        .cptra_ss_mcu_sb_m_axi_if_arqos,
        // .mcu_dma_s_axi_if,
        .cptra_ss_i3c_s_axi_if_r_sub(cptra_ss_i3c_s_axi_if.r_sub),
        .cptra_ss_i3c_s_axi_if_w_sub(cptra_ss_i3c_s_axi_if.w_sub),

        .cptra_ss_mcu_halt_status_o,
        .cptra_ss_mcu_halt_status_i,
        .cptra_ss_mcu_halt_req_o,
        .cptra_ss_mcu_halt_ack_o,
        .cptra_ss_mcu_halt_ack_i,

        .cptra_ss_lc_axi_wr_req_i,
        .cptra_ss_lc_axi_wr_rsp_o,
        .cptra_ss_lc_axi_rd_req_i,
        .cptra_ss_lc_axi_rd_rsp_o,

        .cptra_ss_raw_unlock_token_hashed_i (caliptra_ss_top_pkg::RndCnstRawUnlockTokenHashed),

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
        .cptra_ss_cptra_core_mbox_sram_addr_o,
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
        .caliptra_ss_life_cycle_steady_state_o(),

        .cptra_ss_soc_dft_en_o,
        .cptra_ss_soc_hw_debug_en_o,

        .cptra_ss_fuse_macro_outputs_i (cptra_ss_fuse_macro_outputs_tb),
        .cptra_ss_fuse_macro_inputs_o  (cptra_ss_fuse_macro_inputs_tb),

        .cptra_ss_i3c_scl_i(master0_intf.scl_and),
        .cptra_ss_i3c_sda_i(master0_intf.sda_and),
        .cptra_ss_i3c_scl_o(master0_intf.scl_and),
        .cptra_ss_i3c_sda_o(master0_intf.sda_and),
        .cptra_ss_i3c_scl_oe,
        .cptra_ss_i3c_sda_oe,
        .cptra_ss_sel_od_pp_o,
        .cptra_i3c_axi_user_id_filtering_enable_i,
        .cptra_ss_i3c_recovery_payload_available_o,
        .cptra_ss_i3c_recovery_payload_available_i(cptra_ss_i3c_recovery_payload_available_o),
        .cptra_ss_i3c_recovery_image_activated_o,
        .cptra_ss_i3c_recovery_image_activated_i(cptra_ss_i3c_recovery_image_activated_o),

        .cptra_ss_cptra_core_generic_input_wires_i,
        .cptra_ss_cptra_core_scan_mode_i,
        .cptra_error_fatal,
        .cptra_error_non_fatal
    );

    // Instantiate caliptra_ss_top_tb_soc_bfm
    caliptra_ss_top_tb_soc_bfm #(
        .MCU_SRAM_SIZE_KB(MCU_SRAM_SIZE_KB)
    )u_caliptra_ss_top_tb_soc_bfm (
        .core_clk,
        .cptra_pwrgood (cptra_ss_pwrgood_i),
        .cptra_rst_b(cptra_ss_rst_b_i),
        .cycleCnt,

        .cptra_ss_strap_mcu_lsu_axi_user_i,
        .cptra_ss_strap_mcu_ifu_axi_user_i,
        .cptra_ss_strap_mcu_sram_config_axi_user_i,
        .cptra_ss_strap_mci_soc_config_axi_user_i,
        .cptra_ss_strap_caliptra_dma_axi_user_i,

        .cptra_ss_mci_boot_seq_brkpoint_i,
        .cptra_ss_mcu_no_rom_config_i,
        .cptra_ss_strap_mcu_reset_vector_i,
        
        .cptra_ss_mcu_halt_status_o,
        .cptra_ss_mcu_halt_status_i,
        .cptra_ss_mcu_halt_req_o,
        .cptra_ss_mcu_halt_ack_o,
        .cptra_ss_mcu_halt_ack_i,

        .m_axi_bfm_if,
        .tb_services_if(i_caliptra_ss_bfm_services_if.bfm)

    );

    // Instantiate caliptra_ss_top_tb_services
    caliptra_ss_top_tb_services u_caliptra_ss_top_tb_services (
        .clk                         (core_clk                    ),
        .rst_l                       (cptra_ss_rst_b_i            ),
        .cptra_ss_rdc_clk_cg_o,
        .cycleCnt                    (cycleCnt                    ),
        .cptra_ss_mcu0_el2_mem_export(cptra_ss_mcu0_el2_mem_export),
        .cptra_ss_mci_generic_input_wires_o(cptra_ss_mci_generic_input_wires_i),
        .soc_bfm_if(i_caliptra_ss_bfm_services_if.tb_services),
        .cptra_ss_mci_mcu_sram_req_if,
        .cptra_ss_mcu_mbox0_sram_req_if,
        .cptra_ss_mcu_mbox1_sram_req_if,
        .mcu_rom_mem_export_if
    );

    `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpStateRegsCheck_A, u_otp.u_state_regs, 1'b0)
    `CALIPTRA_SS_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(OtpPrimOnehotCheck_A, u_otp.u_reg_top.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check, 1'b0)


endmodule

// --- Avery I3C Test Case Bench ---
// This is the top level module for the Avery I3C test case bench.
// it triggers i3c test cases.
`include "ai3c_tests_bench.sv"
