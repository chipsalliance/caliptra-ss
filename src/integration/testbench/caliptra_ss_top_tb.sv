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

module caliptra_ss_top_tb
    import tb_top_pkg::*;
    import aaxi_pkg::*;
#(
    `include "css_mcu0_el2_param.vh"
) (


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
    import axi_pkg::*;
    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;
    import ai2c_pkg::*;
    import ai3c_pkg::*;
    import avery_pkg_test::*;

`ifndef VERILATOR
    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width
`endif

    bit                         core_clk;
`ifndef VERILATOR
    bit          [31:0]         mem_signature_begin = 32'd0; // TODO:
    bit          [31:0]         mem_signature_end   = 32'd0;
    bit          [31:0]         mem_mailbox         = 32'h21000410;
`endif
    logic                       rst_l;
    logic                       porst_l;
    logic [pt.PIC_TOTAL_INT:1]  ext_int_tb;
    logic [pt.PIC_TOTAL_INT:1]  ext_int;
    logic                       nmi_int_tb;
    logic                       timer_int;
    logic                       soft_int;

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

    logic                       mailbox_write;
    logic        [63:0]         mailbox_data;

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

`ifdef css_mcu0_RV_BUILD_AXI4
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
         logic                                         ss_dbg_manuf_enable_i   ; 
         logic [63:0]                                  ss_soc_dbg_unlock_level_i;
      
      
         soc_ifc_pkg::security_state_t                security_state_o;

//---------------------------I3C---------------------------------------
         logic payload_available_o;
         logic image_activated_o;
      
//------------------------------------------------------------------------

    logic pwr_otp_init_i;
    logic Allow_RMA_on_PPD;
    logic fake_reset;
//    //-------------------------- I3C AXI signals--------------------------
//    // AXI Write Channels
//        wire                             i3c_axi_awvalid;
//        wire                             i3c_axi_awready;
//        wire [`CALIPTRA_AXI_ID_WIDTH:0]  i3c_axi_awid;
//        wire [31:0]                      i3c_axi_awaddr;
//        wire [2:0]                       i3c_axi_awsize;
//        wire [2:0]                       i3c_axi_awprot;
//        wire [7:0]                       i3c_axi_awlen;
//        wire [1:0]                       i3c_axi_awburst;
//
//
//        wire                             i3c_axi_wvalid;
//        wire                             i3c_axi_wready;
//        wire [63:0]                      i3c_axi_wdata;
//        wire [7:0]                       i3c_axi_wstrb;
//        wire                             i3c_axi_wlast;
//
//        wire                             i3c_axi_bvalid;
//        wire                             i3c_axi_bready;
//        wire [1:0]                       i3c_axi_bresp;
//        wire [`CALIPTRA_AXI_ID_WIDTH:0]  i3c_axi_bid;
//
//        // AXI Read Channels
//        wire                             i3c_axi_arvalid;
//        wire                             i3c_axi_arready;
//        wire [`CALIPTRA_AXI_ID_WIDTH:0]  i3c_axi_arid;
//        wire [31:0]                      i3c_axi_araddr;
//        wire [2:0]                       i3c_axi_arsize;
//        wire [2:0]                       i3c_axi_arprot;
//        wire [7:0]                       i3c_axi_arlen;
//        wire [1:0]                       i3c_axi_arburst;
//
//        wire                             i3c_axi_rvalid;
//        wire                             i3c_axi_rready;
//        wire [`CALIPTRA_AXI_ID_WIDTH:0]  i3c_axi_rid;
//        wire [63:0]                      i3c_axi_rdata;
//        wire [1:0]                       i3c_axi_rresp;
//        wire                             i3c_axi_rlast;

    string                      abi_reg[32]; // ABI register names
    css_mcu0_el2_mem_if         css_mcu0_el2_mem_export ();
    el2_mem_if                  cptra_core_el2_mem_export ();        

    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_wr_fdata;
    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_fdout;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

    logic fuse_ctrl_rdy;
    
    tb_top_pkg::veer_sram_error_injection_mode_t error_injection_mode;

    `define MCU_DEC caliptra_ss_dut.rvtop_wrapper.rvtop.veer.dec


    assign mailbox_write    = caliptra_ss_dut.mci_top_i.s_axi_w_if.awvalid && (caliptra_ss_dut.mci_top_i.s_axi_w_if.awaddr == mem_mailbox) && rst_l;
    assign mailbox_data     = caliptra_ss_dut.mci_top_i.s_axi_w_if.wdata;

    assign mailbox_data_val = mailbox_data[7:0] > 8'h5 && mailbox_data[7:0] < 8'h7f;

    parameter MAX_CYCLES = 200_000;
    bit       hex_file_is_empty;

    integer fd, tp, el;

    always @(negedge core_clk) begin
        // console Monitor
        if( mailbox_data_val & mailbox_write) begin
            $fwrite(fd,"%c", mailbox_data[7:0]);
            $write("%c", mailbox_data[7:0]);
            if (mailbox_data[7:0] inside {8'h0A,8'h0D}) begin // CR/LF
                $fflush(fd);
            end
        end
        // Interrupt signals control
        // data[7:0] == 0x80 - clear ext irq line index given by data[15:8]
        // data[7:0] == 0x81 - set ext irq line index given by data[15:8]
        // data[7:0] == 0x82 - clean NMI, timer and soft irq lines to bits data[8:10]
        // data[7:0] == 0x83 - set NMI, timer and soft irq lines to bits data[8:10]
        // data[7:0] == 0x90 - clear all interrupt request signals
        if(mailbox_write && (mailbox_data[7:0] >= 8'h80 && mailbox_data[7:0] < 8'h84)) begin
            if (mailbox_data[7:0] == 8'h80) begin
                if (mailbox_data[15:8] > 0 && mailbox_data[15:8] < pt.PIC_TOTAL_INT)
                    ext_int_tb[mailbox_data[15:8]] <= 1'b0;
            end
            if (mailbox_data[7:0] == 8'h81) begin
                if (mailbox_data[15:8] > 0 && mailbox_data[15:8] < pt.PIC_TOTAL_INT)
                    ext_int_tb[mailbox_data[15:8]] <= 1'b1;
            end
            if (mailbox_data[7:0] == 8'h82) begin
                nmi_int_tb   <= nmi_int_tb   & ~mailbox_data[8];
                timer_int <= timer_int & ~mailbox_data[9];
                soft_int  <= soft_int  & ~mailbox_data[10];
            end
            if (mailbox_data[7:0] == 8'h83) begin
                nmi_int_tb   <= nmi_int_tb   |  mailbox_data[8];
                timer_int <= timer_int |  mailbox_data[9];
                soft_int  <= soft_int  |  mailbox_data[10];
            end
        end
        if(mailbox_write && (mailbox_data[7:0] == 8'h90)) begin
            ext_int_tb   <= {pt.PIC_TOTAL_INT-1{1'b0}};
            nmi_int_tb   <= 1'b0;
            timer_int    <= 1'b0;
            soft_int     <= 1'b0;
        end
        // ECC error injection
        if(mailbox_write && (mailbox_data[7:0] == 8'he0)) begin
            $display("Injecting single bit ICCM error");
            error_injection_mode.iccm_single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he1)) begin
            $display("Injecting double bit ICCM error");
            error_injection_mode.iccm_double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he2)) begin
            $display("Injecting single bit DCCM error");
            error_injection_mode.dccm_single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he3)) begin
            $display("Injecting double bit DCCM error");
            error_injection_mode.dccm_double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he4)) begin
            $display("Disable ECC error injection");
            error_injection_mode <= '0;
        end
        // ECC error injection - FIXME
        error_injection_mode.dccm_single_bit_error <= 1'b0;
        error_injection_mode.dccm_double_bit_error <= 1'b0;

        // Memory signature dump
        if(mailbox_write && (mailbox_data[7:0] == 8'hFF || mailbox_data[7:0] == 8'h01)) begin
            if (mem_signature_begin < mem_signature_end) begin
                dump_signature();
            end
            // End Of test monitor
            else if(mailbox_data[7:0] == 8'hff) begin
                $display("* TESTCASE PASSED");
                $display("\nFinished : minstret = %0d, mcycle = %0d", `MCU_DEC.tlu.minstretl[31:0],`MCU_DEC.tlu.mcyclel[31:0]);
                $display("See \"mcu_exec.log\" for execution trace with register updates..\n");
                if($test$plusargs("AVY_TEST")) begin
                    $display("Waiting 500us for I3C tests to finish..\n");
                    #500us;
                end
                $finish;
            end
            else if(mailbox_data[7:0] == 8'h1) begin
                $error("* TESTCASE FAILED");
                $finish;
            end
        end
    end


    // trace monitor
    always @(posedge core_clk) begin
        wb_valid      <= `MCU_DEC.dec_i0_wen_r;
        wb_dest       <= `MCU_DEC.dec_i0_waddr_r;
        wb_data       <= `MCU_DEC.dec_i0_wdata_r;
        wb_csr_valid  <= `MCU_DEC.dec_csr_wen_r;
        wb_csr_dest   <= `MCU_DEC.dec_csr_wraddr_r;
        wb_csr_data   <= `MCU_DEC.dec_csr_wrdata_r;
        if (trace_rv_i_valid_ip) begin
           $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", trace_rv_i_valid_ip, 0, trace_rv_i_address_ip,
                  0, trace_rv_i_insn_ip,trace_rv_i_exception_ip,trace_rv_i_ecause_ip,
                  trace_rv_i_tval_ip,trace_rv_i_interrupt_ip);
           // Basic trace - no exception register updates
           // #1 0 ee000000 b0201073 c 0b02       00000000
           commit_count++;
           $fwrite (el, "%10d : %8s 0 %h %h%13s %14s ; %s\n", cycleCnt, $sformatf("#%0d",commit_count),
                        trace_rv_i_address_ip, trace_rv_i_insn_ip,
                        (wb_dest !=0 && wb_valid)?  $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "            ",
                        (wb_csr_valid)? $sformatf("c%h=%h", wb_csr_dest, wb_csr_data) : "             ",
                        dasm(trace_rv_i_insn_ip, trace_rv_i_address_ip, wb_dest & {5{wb_valid}}, wb_data)
                   );
        end
        if(`MCU_DEC.dec_nonblock_load_wen) begin
            $fwrite (el, "%10d : %32s=%h                ; nbL\n", cycleCnt, abi_reg[`MCU_DEC.dec_nonblock_load_waddr], `MCU_DEC.lsu_nonblock_load_data);
            caliptra_ss_top_tb.gpr[0][`MCU_DEC.dec_nonblock_load_waddr] = `MCU_DEC.lsu_nonblock_load_data;
        end
        if(`MCU_DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h                ; nbD\n", cycleCnt, abi_reg[`MCU_DEC.div_waddr_wb], `MCU_DEC.exu_div_result);
            caliptra_ss_top_tb.gpr[0][`MCU_DEC.div_waddr_wb] = `MCU_DEC.exu_div_result;
        end
    end


    initial begin
        abi_reg[0] = "zero";
        abi_reg[1] = "ra";
        abi_reg[2] = "sp";
        abi_reg[3] = "gp";
        abi_reg[4] = "tp";
        abi_reg[5] = "t0";
        abi_reg[6] = "t1";
        abi_reg[7] = "t2";
        abi_reg[8] = "s0";
        abi_reg[9] = "s1";
        abi_reg[10] = "a0";
        abi_reg[11] = "a1";
        abi_reg[12] = "a2";
        abi_reg[13] = "a3";
        abi_reg[14] = "a4";
        abi_reg[15] = "a5";
        abi_reg[16] = "a6";
        abi_reg[17] = "a7";
        abi_reg[18] = "s2";
        abi_reg[19] = "s3";
        abi_reg[20] = "s4";
        abi_reg[21] = "s5";
        abi_reg[22] = "s6";
        abi_reg[23] = "s7";
        abi_reg[24] = "s8";
        abi_reg[25] = "s9";
        abi_reg[26] = "s10";
        abi_reg[27] = "s11";
        abi_reg[28] = "t3";
        abi_reg[29] = "t4";
        abi_reg[30] = "t5";
        abi_reg[31] = "t6";

        ext_int_tb  = {pt.PIC_TOTAL_INT-1{1'b0}};
        timer_int   = 0;
        soft_int    = 0;

        $readmemh("mcu_lmem.hex",     lmem.mem);
        $readmemh("mcu_program.hex",  imem.mem);

        tp = $fopen("trace_port.csv","w");
        el = $fopen("mcu_exec.log","w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value    csr=value     ; mnemonic\n");
        fd = $fopen("mcu_console.log","w");
        commit_count = 0;

        css_mcu0_dummy_dccm_preloader.ram = '{default:8'h0};
        hex_file_is_empty = $system("test -s mcu_dccm.hex");
        if (!hex_file_is_empty) $readmemh("mcu_dccm.hex",css_mcu0_dummy_dccm_preloader.ram,0,32'h0001_FFFF);

        // preload_dccm();
        preload_css_mcu0_dccm();
        preload_iccm();

// `ifndef VERILATOR
//         // if($test$plusargs("dumpon")) $dumpvars;
//         // forever  ACLK     = #5 ~ACLK;
// `endif

    end

    initial  begin
        core_clk = 0;
        // forever  core_clk = #5 ~core_clk;
        forever  core_clk = #(0.5) ~core_clk; // 1GHz
    end

    assign rst_l = cycleCnt > 5 ? 1'b1 : 1'b0;
    // assign rst_l = fuse_ctrl_rdy ? 1'b1 : 1'b0;
    assign porst_l = cycleCnt > 2;

   //=========================================================================
   // AXI Interconnect
   //=========================================================================

    aaxi4_interconnect axi_interconnect(
        .core_clk (core_clk),
        .rst_l    (rst_l)
    );

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH - 3),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) m_axi_bfm_if (.clk(core_clk), .rst_n(rst_l));

    // Cptra Mgr Axi Interface
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) cptra_core_m_axi_if (.clk(core_clk), .rst_n(rst_l));

    // Cptra Sub AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_core_s_axi_if (.clk(core_clk), .rst_n(rst_l));

    // MCI Mgr AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) mci_m_axi_if (.clk(core_clk), .rst_n(rst_l));

    // MCI Sub AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) mci_s_axi_if (.clk(core_clk), .rst_n(rst_l));

    // MCU LSU AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) mcu_lsu_m_axi_if (.clk(core_clk), .rst_n(rst_l));

    // MCU IFU AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) mcu_ifu_m_axi_if (.clk(core_clk), .rst_n(rst_l));

    // MCU DMA AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) mcu_dma_s_axi_if (.clk(core_clk), .rst_n(rst_l));

    // I3C AXI Interface
    axi_if #(
        .AW(32), //-- FIXME : Assign a common paramter
        .DW(32), //-- FIXME : Assign a common paramter,
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) i3c_s_axi_if (.clk(core_clk), .rst_n(rst_l));

    axi_struct_pkg::axi_wr_req_t lc_axi_wr_req;
    axi_struct_pkg::axi_wr_rsp_t lc_axi_wr_rsp;
    axi_struct_pkg::axi_rd_req_t lc_axi_rd_req;
    axi_struct_pkg::axi_rd_rsp_t lc_axi_rd_rsp;

    axi_struct_pkg::axi_wr_req_t core_axi_wr_req;
    axi_struct_pkg::axi_wr_rsp_t core_axi_wr_rsp;
    axi_struct_pkg::axi_rd_req_t core_axi_rd_req;
    axi_struct_pkg::axi_rd_rsp_t core_axi_rd_rsp;
    
    logic cptra_core_m_axi_if_rd_is_upper_dw_latched;
    logic cptra_core_m_axi_if_wr_is_upper_dw_latched;
    logic m_axi_bfm_if_rd_is_upper_dw_latched;
    logic m_axi_bfm_if_wr_is_upper_dw_latched;
    logic fuse_core_axi_rd_is_upper_dw_latched;
    logic fuse_core_axi_wr_is_upper_dw_latched;
    logic mci_s_axi_if_rd_is_upper_dw_latched;
    logic mci_s_axi_if_wr_is_upper_dw_latched;
    logic cptra_core_s_axi_if_rd_is_upper_dw_latched;
    logic cptra_core_s_axi_if_wr_is_upper_dw_latched;
    logic lc_axi_rd_is_upper_dw_latched;
    logic lc_axi_wr_is_upper_dw_latched;
    logic mcu_lsu_m_axi_if_rd_is_upper_dw_latched;
    logic mcu_lsu_m_axi_if_wr_is_upper_dw_latched;
    logic mcu_ifu_m_axi_if_rd_is_upper_dw_latched;
    logic mcu_ifu_m_axi_if_wr_is_upper_dw_latched;
    logic mcu_dma_s_axi_if_rd_is_upper_dw_latched;
    logic mcu_dma_s_axi_if_wr_is_upper_dw_latched;
    logic i3c_s_axi_if_rd_is_upper_dw_latched;
    logic i3c_s_axi_if_wr_is_upper_dw_latched;

    `define SS_DATA_WIDTH_HACK(inf_name, core_clk = core_clk, rst_l = rst_l)\
    always@(posedge core_clk or negedge rst_l)\
        if (!rst_l)\
            ``inf_name``_wr_is_upper_dw_latched <= 0;\
        else if (``inf_name``.awvalid && ``inf_name``.awready)\
            ``inf_name``_wr_is_upper_dw_latched <= ``inf_name``.awaddr[2] && (``inf_name``.awsize < 3);\
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT``inf_name``, (``inf_name``.awvalid && ``inf_name``.awready) -> (``inf_name``.awsize < 3), core_clk, !rst_l)\
    always@(posedge core_clk or negedge rst_l)\
        if (!rst_l)\
            ``inf_name``_rd_is_upper_dw_latched <= 0;\
        else if (``inf_name``.arvalid && ``inf_name``.arready)\
            ``inf_name``_rd_is_upper_dw_latched <= ``inf_name``.araddr[2] && (``inf_name``.arsize < 3);\
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT``inf_name``, (``inf_name``.arvalid && ``inf_name``.arready) -> (``inf_name``.arsize < 3), core_clk, !rst_l)
    

    `SS_DATA_WIDTH_HACK(cptra_core_m_axi_if)
    `SS_DATA_WIDTH_HACK(cptra_core_s_axi_if)
    `SS_DATA_WIDTH_HACK(m_axi_bfm_if)
    `SS_DATA_WIDTH_HACK(mci_s_axi_if)
    `SS_DATA_WIDTH_HACK(mcu_lsu_m_axi_if)
    `SS_DATA_WIDTH_HACK(mcu_ifu_m_axi_if)
    `SS_DATA_WIDTH_HACK(mcu_dma_s_axi_if)
    `SS_DATA_WIDTH_HACK(i3c_s_axi_if)
        
    //These don't fit the macro FIXME LATER
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
    if (!rst_l)
        lc_axi_wr_is_upper_dw_latched <= 0;
    else if (lc_axi_wr_req.awvalid && lc_axi_wr_rsp.awready)
        lc_axi_wr_is_upper_dw_latched <= lc_axi_wr_req.awaddr[2] && (lc_axi_wr_req.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT, (lc_axi_wr_req.awvalid && lc_axi_wr_rsp.awready) -> (lc_axi_wr_req.awsize < 3), core_clk, !rst_l)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            lc_axi_rd_is_upper_dw_latched <= 0;
        else if (lc_axi_rd_req.arvalid && lc_axi_rd_rsp.arready)
            lc_axi_rd_is_upper_dw_latched <= lc_axi_rd_req.araddr[2] && (lc_axi_rd_req.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT, (lc_axi_rd_req.arvalid && lc_axi_rd_rsp.arready) -> (lc_axi_rd_req.arsize < 3), core_clk, !rst_l)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            fuse_core_axi_wr_is_upper_dw_latched <= 0;
        else if (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready)
            fuse_core_axi_wr_is_upper_dw_latched <= core_axi_wr_req.awaddr[2] && (core_axi_wr_req.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT, (core_axi_wr_req.awvalid && core_axi_wr_rsp.awready) -> (core_axi_wr_req.awsize < 3), core_clk, !rst_l)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            fuse_core_axi_rd_is_upper_dw_latched <= 0;
        else if (core_axi_rd_req.arvalid && core_axi_rd_rsp.arready)
            fuse_core_axi_rd_is_upper_dw_latched <= core_axi_rd_req.araddr[2] && (core_axi_rd_req.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT, (core_axi_rd_req.arvalid && core_axi_rd_rsp.arready) -> (core_axi_rd_req.arsize < 3), core_clk, !rst_l)

    // AXI Interconnect connections

    //Interconnect 0 - MCU LSU
    assign axi_interconnect.mintf_arr[0].AWVALID = mcu_lsu_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[0].AWADDR  = mcu_lsu_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[0].AWID    = mcu_lsu_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[0].AWLEN   = mcu_lsu_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[0].AWSIZE  = mcu_lsu_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[0].AWBURST = mcu_lsu_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[0].AWLOCK  = mcu_lsu_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[0].AWUSER  = mcu_lsu_m_axi_if.awuser;
    assign mcu_lsu_m_axi_if.awready                = axi_interconnect.mintf_arr[0].AWREADY;
    assign axi_interconnect.mintf_arr[0].WVALID  = mcu_lsu_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[0].WDATA   = mcu_lsu_m_axi_if.wdata << (mcu_lsu_m_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[0].WSTRB   = mcu_lsu_m_axi_if.wstrb << (mcu_lsu_m_axi_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[0].WLAST   = mcu_lsu_m_axi_if.wlast;
    assign mcu_lsu_m_axi_if.wready                 = axi_interconnect.mintf_arr[0].WREADY;
    assign mcu_lsu_m_axi_if.bvalid                 = axi_interconnect.mintf_arr[0].BVALID;
    assign mcu_lsu_m_axi_if.bresp                  = axi_interconnect.mintf_arr[0].BRESP;
    assign mcu_lsu_m_axi_if.bid                    = axi_interconnect.mintf_arr[0].BID;
    assign axi_interconnect.mintf_arr[0].BREADY  = mcu_lsu_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[0].ARVALID = mcu_lsu_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[0].ARADDR  = mcu_lsu_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[0].ARID    = mcu_lsu_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[0].ARLEN   = mcu_lsu_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[0].ARSIZE  = mcu_lsu_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[0].ARBURST = mcu_lsu_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[0].ARLOCK  = mcu_lsu_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[0].ARUSER  = mcu_lsu_m_axi_if.aruser;
    assign mcu_lsu_m_axi_if.arready                = axi_interconnect.mintf_arr[0].ARREADY;
    assign mcu_lsu_m_axi_if.rvalid                 = axi_interconnect.mintf_arr[0].RVALID;
    assign mcu_lsu_m_axi_if.rdata                  = axi_interconnect.mintf_arr[0].RDATA >> (mcu_lsu_m_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign mcu_lsu_m_axi_if.rresp                  = axi_interconnect.mintf_arr[0].RRESP;
    assign mcu_lsu_m_axi_if.rid                    = axi_interconnect.mintf_arr[0].RID;
    assign mcu_lsu_m_axi_if.rlast                  = axi_interconnect.mintf_arr[0].RLAST;
    assign axi_interconnect.mintf_arr[0].RREADY  = mcu_lsu_m_axi_if.rready;

    //Interconnect 1 - MCU IFU
    assign axi_interconnect.mintf_arr[1].AWVALID = mcu_ifu_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[1].AWADDR  = mcu_ifu_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[1].AWID    = mcu_ifu_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[1].AWLEN   = mcu_ifu_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[1].AWSIZE  = mcu_ifu_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[1].AWBURST = mcu_ifu_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[1].AWLOCK  = mcu_ifu_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[1].AWUSER  = mcu_ifu_m_axi_if.awuser;
    assign mcu_ifu_m_axi_if.awready                = axi_interconnect.mintf_arr[1].AWREADY;
    assign axi_interconnect.mintf_arr[1].WVALID  = mcu_ifu_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[1].WDATA   = mcu_ifu_m_axi_if.wdata << (mcu_ifu_m_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[1].WSTRB   = mcu_ifu_m_axi_if.wstrb << (mcu_ifu_m_axi_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[1].WLAST   = mcu_ifu_m_axi_if.wlast;
    assign mcu_ifu_m_axi_if.wready                 = axi_interconnect.mintf_arr[1].WREADY;
    assign mcu_ifu_m_axi_if.bvalid                 = axi_interconnect.mintf_arr[1].BVALID;
    assign mcu_ifu_m_axi_if.bresp                  = axi_interconnect.mintf_arr[1].BRESP;
    assign mcu_ifu_m_axi_if.bid                    = axi_interconnect.mintf_arr[1].BID;
    assign axi_interconnect.mintf_arr[1].BREADY  = mcu_ifu_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[1].ARVALID = mcu_ifu_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[1].ARADDR  = mcu_ifu_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[1].ARID    = mcu_ifu_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[1].ARLEN   = mcu_ifu_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[1].ARSIZE  = mcu_ifu_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[1].ARBURST = mcu_ifu_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[1].ARLOCK  = mcu_ifu_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[1].ARUSER  = mcu_ifu_m_axi_if.aruser;
    assign mcu_ifu_m_axi_if.arready                = axi_interconnect.mintf_arr[1].ARREADY;
    assign mcu_ifu_m_axi_if.rvalid                 = axi_interconnect.mintf_arr[1].RVALID;
    assign mcu_ifu_m_axi_if.rdata                  = axi_interconnect.mintf_arr[1].RDATA >> (mcu_ifu_m_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign mcu_ifu_m_axi_if.rresp                  = axi_interconnect.mintf_arr[1].RRESP;
    assign mcu_ifu_m_axi_if.rid                    = axi_interconnect.mintf_arr[1].RID;
    assign mcu_ifu_m_axi_if.rlast                  = axi_interconnect.mintf_arr[1].RLAST;
    assign axi_interconnect.mintf_arr[1].RREADY  = mcu_ifu_m_axi_if.rready;

    //Interconnect 2 MGR - Tie Off
    assign axi_interconnect.mintf_arr[2].AWVALID = '0;
    assign axi_interconnect.mintf_arr[2].AWADDR  = '0;
    assign axi_interconnect.mintf_arr[2].AWID    = '0;
    assign axi_interconnect.mintf_arr[2].AWLEN   = '0;
    assign axi_interconnect.mintf_arr[2].AWSIZE  = '0;
    assign axi_interconnect.mintf_arr[2].AWBURST = '0;
    assign axi_interconnect.mintf_arr[2].AWLOCK  = '0;
    assign axi_interconnect.mintf_arr[2].AWUSER  = '0;
    
    assign axi_interconnect.mintf_arr[2].WVALID = '0;
    assign axi_interconnect.mintf_arr[2].WDATA  = '0;
    assign axi_interconnect.mintf_arr[2].WSTRB  = '0;
    assign axi_interconnect.mintf_arr[2].WLAST  = '0;
    assign axi_interconnect.mintf_arr[2].BREADY = '0;

    assign axi_interconnect.mintf_arr[2].ARVALID = '0;
    assign axi_interconnect.mintf_arr[2].ARADDR  = '0;
    assign axi_interconnect.mintf_arr[2].ARID    = '0;
    assign axi_interconnect.mintf_arr[2].ARLEN   = '0;
    assign axi_interconnect.mintf_arr[2].ARSIZE  = '0;
    assign axi_interconnect.mintf_arr[2].ARBURST = '0;
    assign axi_interconnect.mintf_arr[2].ARLOCK  = '0;
    assign axi_interconnect.mintf_arr[2].ARUSER  = '0;
    assign axi_interconnect.mintf_arr[2].RREADY = '0;

    //Interconnect 2 Sub - MCU DMA
    assign mcu_dma_s_axi_if.awvalid                = axi_interconnect.sintf_arr[2].AWVALID;
    assign mcu_dma_s_axi_if.awaddr                 = axi_interconnect.sintf_arr[2].AWADDR;
    assign mcu_dma_s_axi_if.awid                   = axi_interconnect.sintf_arr[2].AWID;
    assign mcu_dma_s_axi_if.awlen                  = axi_interconnect.sintf_arr[2].AWLEN;
    assign mcu_dma_s_axi_if.awsize                 = axi_interconnect.sintf_arr[2].AWSIZE;
    assign mcu_dma_s_axi_if.awburst                = axi_interconnect.sintf_arr[2].AWBURST;
    assign mcu_dma_s_axi_if.awlock                 = axi_interconnect.sintf_arr[2].AWLOCK;
    assign mcu_dma_s_axi_if.awuser                 = axi_interconnect.sintf_arr[2].AWUSER;
    assign axi_interconnect.sintf_arr[2].AWREADY = mcu_dma_s_axi_if.awready;
    assign mcu_dma_s_axi_if.wvalid                 = axi_interconnect.sintf_arr[2].WVALID;
    assign mcu_dma_s_axi_if.wdata                  = axi_interconnect.sintf_arr[2].WDATA >> (mcu_dma_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign mcu_dma_s_axi_if.wstrb                  = axi_interconnect.sintf_arr[2].WSTRB >> (mcu_dma_s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign mcu_dma_s_axi_if.wlast                  = axi_interconnect.sintf_arr[2].WLAST;
    assign axi_interconnect.sintf_arr[2].WREADY  = mcu_dma_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[2].BVALID  = mcu_dma_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[2].BRESP   = mcu_dma_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[2].BID     = mcu_dma_s_axi_if.bid;
    assign mcu_dma_s_axi_if.bready                 = axi_interconnect.sintf_arr[2].BREADY;
    assign mcu_dma_s_axi_if.arvalid                = axi_interconnect.sintf_arr[2].ARVALID;
    assign mcu_dma_s_axi_if.araddr                 = axi_interconnect.sintf_arr[2].ARADDR;
    assign mcu_dma_s_axi_if.arid                   = axi_interconnect.sintf_arr[2].ARID;
    assign mcu_dma_s_axi_if.arlen                  = axi_interconnect.sintf_arr[2].ARLEN;
    assign mcu_dma_s_axi_if.arsize                 = axi_interconnect.sintf_arr[2].ARSIZE;
    assign mcu_dma_s_axi_if.arburst                = axi_interconnect.sintf_arr[2].ARBURST;
    assign mcu_dma_s_axi_if.arlock                 = axi_interconnect.sintf_arr[2].ARLOCK;
    assign mcu_dma_s_axi_if.aruser                 = axi_interconnect.sintf_arr[2].ARUSER;
    assign axi_interconnect.sintf_arr[2].ARREADY = mcu_dma_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[2].RVALID  = mcu_dma_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[2].RDATA   = 64'(mcu_dma_s_axi_if.rdata) << (mcu_dma_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[2].RRESP   = mcu_dma_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[2].RID     = mcu_dma_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[2].RLAST   = mcu_dma_s_axi_if.rlast;
    assign mcu_dma_s_axi_if.rready                 = axi_interconnect.sintf_arr[2].RREADY;

    //Interconnect 3 - CPTRA soc axi if
    assign cptra_core_s_axi_if.awvalid           = axi_interconnect.sintf_arr[3].AWVALID;
    assign cptra_core_s_axi_if.awaddr            = axi_interconnect.sintf_arr[3].AWADDR;
    assign cptra_core_s_axi_if.awid              = axi_interconnect.sintf_arr[3].AWID;
    assign cptra_core_s_axi_if.awlen             = axi_interconnect.sintf_arr[3].AWLEN;
    assign cptra_core_s_axi_if.awsize            = axi_interconnect.sintf_arr[3].AWSIZE;
    assign cptra_core_s_axi_if.awburst           = axi_interconnect.sintf_arr[3].AWBURST;
    assign cptra_core_s_axi_if.awlock            = axi_interconnect.sintf_arr[3].AWLOCK;
    assign cptra_core_s_axi_if.awuser            = axi_interconnect.sintf_arr[3].AWUSER;
    assign axi_interconnect.sintf_arr[3].AWREADY = cptra_core_s_axi_if.awready;
    assign cptra_core_s_axi_if.wvalid            = axi_interconnect.sintf_arr[3].WVALID;
    assign cptra_core_s_axi_if.wdata             = axi_interconnect.sintf_arr[3].WDATA >> (cptra_core_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign cptra_core_s_axi_if.wstrb             = axi_interconnect.sintf_arr[3].WSTRB >> (cptra_core_s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign cptra_core_s_axi_if.wlast             = axi_interconnect.sintf_arr[3].WLAST;
    assign axi_interconnect.sintf_arr[3].WREADY  = cptra_core_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[3].BVALID  = cptra_core_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[3].BRESP   = cptra_core_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[3].BID     = cptra_core_s_axi_if.bid;
    assign cptra_core_s_axi_if.bready            = axi_interconnect.sintf_arr[3].BREADY;
    assign cptra_core_s_axi_if.arvalid           = axi_interconnect.sintf_arr[3].ARVALID;
    assign cptra_core_s_axi_if.araddr            = axi_interconnect.sintf_arr[3].ARADDR;
    assign cptra_core_s_axi_if.arid              = axi_interconnect.sintf_arr[3].ARID;
    assign cptra_core_s_axi_if.arlen             = axi_interconnect.sintf_arr[3].ARLEN;
    assign cptra_core_s_axi_if.arsize            = axi_interconnect.sintf_arr[3].ARSIZE;
    assign cptra_core_s_axi_if.arburst           = axi_interconnect.sintf_arr[3].ARBURST;
    assign cptra_core_s_axi_if.arlock            = axi_interconnect.sintf_arr[3].ARLOCK;
    assign cptra_core_s_axi_if.aruser            = axi_interconnect.sintf_arr[3].ARUSER;
    assign axi_interconnect.sintf_arr[3].ARREADY = cptra_core_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[3].RVALID  = cptra_core_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[3].RDATA   = 64'(cptra_core_s_axi_if.rdata) << (cptra_core_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[3].RRESP   = cptra_core_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[3].RID     = cptra_core_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[3].RLAST   = cptra_core_s_axi_if.rlast;
    assign cptra_core_s_axi_if.rready            = axi_interconnect.sintf_arr[3].RREADY;

    //Interconnect MGR 3 - cptra dma
    assign axi_interconnect.mintf_arr[3].AWVALID = cptra_core_m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[3].AWADDR  = cptra_core_m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[3].AWID    = cptra_core_m_axi_if.awid;
    assign axi_interconnect.mintf_arr[3].AWLEN   = cptra_core_m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[3].AWSIZE  = cptra_core_m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[3].AWBURST = cptra_core_m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[3].AWLOCK  = cptra_core_m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[3].AWUSER  = cptra_core_m_axi_if.awuser;
    assign cptra_core_m_axi_if.awready           = axi_interconnect.mintf_arr[3].AWREADY;
    assign axi_interconnect.mintf_arr[3].WVALID  = cptra_core_m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[3].WDATA   = cptra_core_m_axi_if.wdata << (cptra_core_m_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[3].WSTRB   = cptra_core_m_axi_if.wstrb << (cptra_core_m_axi_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[3].WLAST   = cptra_core_m_axi_if.wlast;
    assign cptra_core_m_axi_if.wready            = axi_interconnect.mintf_arr[3].WREADY;
    assign cptra_core_m_axi_if.bvalid            = axi_interconnect.mintf_arr[3].BVALID;
    assign cptra_core_m_axi_if.bresp             = axi_interconnect.mintf_arr[3].BRESP;
    assign cptra_core_m_axi_if.bid               = axi_interconnect.mintf_arr[3].BID;
    assign axi_interconnect.mintf_arr[3].BREADY  = cptra_core_m_axi_if.bready;
    assign axi_interconnect.mintf_arr[3].ARVALID = cptra_core_m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[3].ARADDR  = cptra_core_m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[3].ARID    = cptra_core_m_axi_if.arid;
    assign axi_interconnect.mintf_arr[3].ARLEN   = cptra_core_m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[3].ARSIZE  = cptra_core_m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[3].ARBURST = cptra_core_m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[3].ARLOCK  = cptra_core_m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[3].ARUSER  = cptra_core_m_axi_if.aruser;
    assign cptra_core_m_axi_if.arready           = axi_interconnect.mintf_arr[3].ARREADY;
    assign cptra_core_m_axi_if.rvalid            = axi_interconnect.mintf_arr[3].RVALID;
    assign cptra_core_m_axi_if.rdata             = axi_interconnect.mintf_arr[3].RDATA >> (cptra_core_m_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign cptra_core_m_axi_if.rresp             = axi_interconnect.mintf_arr[3].RRESP;
    assign cptra_core_m_axi_if.rid               = axi_interconnect.mintf_arr[3].RID;
    assign cptra_core_m_axi_if.rlast             = axi_interconnect.mintf_arr[3].RLAST;
    assign axi_interconnect.mintf_arr[3].RREADY  = cptra_core_m_axi_if.rready;

    //Interconnect 4 - master bfm
    assign axi_interconnect.mintf_arr[4].AWVALID  = m_axi_bfm_if.awvalid;
    assign axi_interconnect.mintf_arr[4].AWADDR   = m_axi_bfm_if.awaddr;
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
    assign m_axi_bfm_if.wready                    = axi_interconnect.mintf_arr[4].WREADY;
    assign m_axi_bfm_if.bvalid                    = axi_interconnect.mintf_arr[4].BVALID;
    assign m_axi_bfm_if.bresp                     = axi_interconnect.mintf_arr[4].BRESP;
    assign m_axi_bfm_if.bid                       = axi_interconnect.mintf_arr[4].BID;
    assign axi_interconnect.mintf_arr[4].BREADY   = m_axi_bfm_if.bready;
    assign axi_interconnect.mintf_arr[4].ARVALID  = m_axi_bfm_if.arvalid;
    assign axi_interconnect.mintf_arr[4].ARADDR   = m_axi_bfm_if.araddr;
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
    assign axi_interconnect.mintf_arr[4].RREADY   = m_axi_bfm_if.rready;

    assign mci_s_axi_if.awvalid                      = axi_interconnect.sintf_arr[4].AWVALID;
    assign mci_s_axi_if.awaddr                       = axi_interconnect.sintf_arr[4].AWADDR;
    assign mci_s_axi_if.awid                         = axi_interconnect.sintf_arr[4].AWID;
    assign mci_s_axi_if.awlen                        = axi_interconnect.sintf_arr[4].AWLEN;
    assign mci_s_axi_if.awsize                       = axi_interconnect.sintf_arr[4].AWSIZE;
    assign mci_s_axi_if.awburst                      = axi_interconnect.sintf_arr[4].AWBURST;
    assign mci_s_axi_if.awlock                       = axi_interconnect.sintf_arr[4].AWLOCK;
    assign mci_s_axi_if.awuser                       = axi_interconnect.sintf_arr[4].AWUSER;
    assign axi_interconnect.sintf_arr[4].AWREADY = mci_s_axi_if.awready;
    assign mci_s_axi_if.wvalid                       = axi_interconnect.sintf_arr[4].WVALID;
    assign mci_s_axi_if.wdata                        = axi_interconnect.sintf_arr[4].WDATA >> (mci_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign mci_s_axi_if.wstrb                        = axi_interconnect.sintf_arr[4].WSTRB >> (mci_s_axi_if_wr_is_upper_dw_latched ? 4  : 0);
    assign mci_s_axi_if.wlast                        = axi_interconnect.sintf_arr[4].WLAST;
    assign axi_interconnect.sintf_arr[4].WREADY      = mci_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[4].BVALID      = mci_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[4].BRESP       = mci_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[4].BID         = mci_s_axi_if.bid;
    assign mci_s_axi_if.bready                       = axi_interconnect.sintf_arr[4].BREADY;
    assign mci_s_axi_if.arvalid                      = axi_interconnect.sintf_arr[4].ARVALID;
    assign mci_s_axi_if.araddr                       = axi_interconnect.sintf_arr[4].ARADDR;
    assign mci_s_axi_if.arid                         = axi_interconnect.sintf_arr[4].ARID;
    assign mci_s_axi_if.arlen                        = axi_interconnect.sintf_arr[4].ARLEN;
    assign mci_s_axi_if.arsize                       = axi_interconnect.sintf_arr[4].ARSIZE;
    assign mci_s_axi_if.arburst                      = axi_interconnect.sintf_arr[4].ARBURST;
    assign mci_s_axi_if.arlock                       = axi_interconnect.sintf_arr[4].ARLOCK;
    assign mci_s_axi_if.aruser                       = axi_interconnect.sintf_arr[4].ARUSER;
    assign axi_interconnect.sintf_arr[4].ARREADY       = mci_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[4].RVALID        = mci_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[4].RDATA         = 64'(mci_s_axi_if.rdata) << (mci_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[4].RRESP         = mci_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[4].RID           = mci_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[4].RLAST         = mci_s_axi_if.rlast;
    assign mci_s_axi_if.rready                         = axi_interconnect.sintf_arr[4].RREADY;

    //Interconnect 5
    assign core_axi_wr_req.awaddr = axi_interconnect.sintf_arr[5].AWADDR;
    assign core_axi_wr_req.awburst = axi_interconnect.sintf_arr[5].AWBURST;
    assign core_axi_wr_req.awsize = axi_interconnect.sintf_arr[5].AWSIZE;
    assign core_axi_wr_req.awlen = axi_interconnect.sintf_arr[5].AWLEN;
    assign core_axi_wr_req.awuser = axi_interconnect.sintf_arr[5].AWUSER;
    assign core_axi_wr_req.awid = axi_interconnect.sintf_arr[5].AWID;
    assign core_axi_wr_req.awlock = axi_interconnect.sintf_arr[5].AWLOCK;
    assign core_axi_wr_req.awvalid = axi_interconnect.sintf_arr[5].AWVALID;
    assign core_axi_wr_req.wdata = axi_interconnect.sintf_arr[5].WDATA >> (fuse_core_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign core_axi_wr_req.wstrb = axi_interconnect.sintf_arr[5].WSTRB >> (fuse_core_axi_wr_is_upper_dw_latched ? 4 : 0);
    assign core_axi_wr_req.wlast = axi_interconnect.sintf_arr[5].WLAST;
    assign core_axi_wr_req.wvalid = axi_interconnect.sintf_arr[5].WVALID;
    assign core_axi_wr_req.bready = axi_interconnect.sintf_arr[5].BREADY;
    assign axi_interconnect.sintf_arr[5].AWREADY = core_axi_wr_rsp.awready;
    assign axi_interconnect.sintf_arr[5].WREADY = core_axi_wr_rsp.wready;
    assign axi_interconnect.sintf_arr[5].BRESP = core_axi_wr_rsp.bresp;
    assign axi_interconnect.sintf_arr[5].BID = core_axi_wr_rsp.bid;
    assign axi_interconnect.sintf_arr[5].BVALID = core_axi_wr_rsp.bvalid;
    assign core_axi_rd_req.araddr = axi_interconnect.sintf_arr[5].ARADDR;
    assign core_axi_rd_req.arburst = axi_interconnect.sintf_arr[5].ARBURST;
    assign core_axi_rd_req.arsize = axi_interconnect.sintf_arr[5].ARSIZE;
    assign core_axi_rd_req.arlen = axi_interconnect.sintf_arr[5].ARLEN;
    assign core_axi_rd_req.aruser = axi_interconnect.sintf_arr[5].ARUSER;
    assign core_axi_rd_req.arid = axi_interconnect.sintf_arr[5].ARID;
    assign core_axi_rd_req.arlock = axi_interconnect.sintf_arr[5].ARLOCK;
    assign core_axi_rd_req.arvalid = axi_interconnect.sintf_arr[5].ARVALID;
    assign core_axi_rd_req.rready = axi_interconnect.sintf_arr[5].RREADY;
    assign axi_interconnect.sintf_arr[5].ARREADY = core_axi_rd_rsp.arready;
    assign axi_interconnect.sintf_arr[5].RDATA = 64'(core_axi_rd_rsp.rdata) << (fuse_core_axi_rd_is_upper_dw_latched ? 32 : 0);;
    assign axi_interconnect.sintf_arr[5].RRESP = core_axi_rd_rsp.rresp;
    assign axi_interconnect.sintf_arr[5].RID = core_axi_rd_rsp.rid;
    assign axi_interconnect.sintf_arr[5].RLAST = core_axi_rd_rsp.rlast;
    assign axi_interconnect.sintf_arr[5].RVALID = core_axi_rd_rsp.rvalid;

    //Interconnect 6
    assign axi_interconnect.sintf_arr[6].AWREADY = '0;
    assign axi_interconnect.sintf_arr[6].WREADY = '0;
    assign axi_interconnect.sintf_arr[6].BRESP = '0;
    assign axi_interconnect.sintf_arr[6].BID = '0;
    assign axi_interconnect.sintf_arr[6].BVALID = '0;
    assign axi_interconnect.sintf_arr[6].ARREADY = '0;
    assign axi_interconnect.sintf_arr[6].RDATA = '0;
    assign axi_interconnect.sintf_arr[6].RRESP = '0;
    assign axi_interconnect.sintf_arr[6].RID = '0;
    assign axi_interconnect.sintf_arr[6].RLAST = '0;
    assign axi_interconnect.sintf_arr[6].RVALID = '0;

    //Interconnect 7 - LCC
    assign lc_axi_wr_req.awvalid = axi_interconnect.sintf_arr[7].AWVALID;
    assign lc_axi_wr_req.awaddr = axi_interconnect.sintf_arr[7].AWADDR;
    assign lc_axi_wr_req.awid = axi_interconnect.sintf_arr[7].AWID;
    assign lc_axi_wr_req.awlen = axi_interconnect.sintf_arr[7].AWLEN;
    assign lc_axi_wr_req.awsize = axi_interconnect.sintf_arr[7].AWSIZE;
    assign lc_axi_wr_req.awburst = axi_interconnect.sintf_arr[7].AWBURST;
    assign lc_axi_wr_req.awlock = axi_interconnect.sintf_arr[7].AWLOCK;
    assign lc_axi_wr_req.awuser = axi_interconnect.sintf_arr[7].AWUSER;
    assign axi_interconnect.sintf_arr[7].AWREADY = lc_axi_wr_rsp.awready;
    assign lc_axi_wr_req.wvalid = axi_interconnect.sintf_arr[7].WVALID;
    assign lc_axi_wr_req.wdata = axi_interconnect.sintf_arr[7].WDATA >> (lc_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign lc_axi_wr_req.wstrb = axi_interconnect.sintf_arr[7].WSTRB >> (lc_axi_wr_is_upper_dw_latched ? 4 : 0);
    assign lc_axi_wr_req.wlast = axi_interconnect.sintf_arr[7].WLAST;
    assign axi_interconnect.sintf_arr[7].WREADY = lc_axi_wr_rsp.wready;
    assign axi_interconnect.sintf_arr[7].BRESP = lc_axi_wr_rsp.bresp;
    assign axi_interconnect.sintf_arr[7].BID = lc_axi_wr_rsp.bid;
    assign axi_interconnect.sintf_arr[7].BVALID = lc_axi_wr_rsp.bvalid;
    assign lc_axi_wr_req.bready = axi_interconnect.sintf_arr[7].BREADY;
    assign lc_axi_rd_req.arvalid = axi_interconnect.sintf_arr[7].ARVALID;
    assign lc_axi_rd_req.araddr = axi_interconnect.sintf_arr[7].ARADDR;
    assign lc_axi_rd_req.arid = axi_interconnect.sintf_arr[7].ARID;
    assign lc_axi_rd_req.arlen = axi_interconnect.sintf_arr[7].ARLEN;
    assign lc_axi_rd_req.arsize = axi_interconnect.sintf_arr[7].ARSIZE;
    assign lc_axi_rd_req.arburst = axi_interconnect.sintf_arr[7].ARBURST;
    assign lc_axi_rd_req.arlock = axi_interconnect.sintf_arr[7].ARLOCK;
    assign lc_axi_rd_req.aruser = axi_interconnect.sintf_arr[7].ARUSER;
    assign axi_interconnect.sintf_arr[7].ARREADY = lc_axi_rd_rsp.arready;
    assign axi_interconnect.sintf_arr[7].RDATA = 64'(lc_axi_rd_rsp.rdata) << (lc_axi_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[7].RRESP = lc_axi_rd_rsp.rresp;
    assign axi_interconnect.sintf_arr[7].RID = lc_axi_rd_rsp.rid;
    assign axi_interconnect.sintf_arr[7].RLAST = lc_axi_rd_rsp.rlast;
    assign axi_interconnect.sintf_arr[7].RVALID = lc_axi_rd_rsp.rvalid;
    assign lc_axi_rd_req.rready = axi_interconnect.sintf_arr[7].RREADY;

    //Interconnect 8 - I3C
    assign i3c_s_axi_if.awvalid                    = axi_interconnect.sintf_arr[8].AWVALID;
    assign i3c_s_axi_if.awaddr                     = axi_interconnect.sintf_arr[8].AWADDR;
    assign i3c_s_axi_if.awid                       = axi_interconnect.sintf_arr[8].AWID;
    assign i3c_s_axi_if.awlen                      = axi_interconnect.sintf_arr[8].AWLEN;
    assign i3c_s_axi_if.awsize                     = axi_interconnect.sintf_arr[8].AWSIZE;
    assign i3c_s_axi_if.awburst                    = axi_interconnect.sintf_arr[8].AWBURST;
    assign i3c_s_axi_if.awlock                     = axi_interconnect.sintf_arr[8].AWLOCK;
    assign i3c_s_axi_if.awuser                     = axi_interconnect.sintf_arr[8].AWUSER;
    assign axi_interconnect.sintf_arr[8].AWREADY = i3c_s_axi_if.awready;
    assign i3c_s_axi_if.wvalid                     = axi_interconnect.sintf_arr[8].WVALID;
    assign i3c_s_axi_if.wdata                      = axi_interconnect.sintf_arr[8].WDATA >> (i3c_s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign i3c_s_axi_if.wstrb                      = axi_interconnect.sintf_arr[8].WSTRB >> (i3c_s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign i3c_s_axi_if.wlast                      = axi_interconnect.sintf_arr[8].WLAST;
    assign axi_interconnect.sintf_arr[8].WREADY  = i3c_s_axi_if.wready;
    assign axi_interconnect.sintf_arr[8].BVALID  = i3c_s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[8].BRESP   = i3c_s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[8].BID     = i3c_s_axi_if.bid;
    assign i3c_s_axi_if.bready                     = axi_interconnect.sintf_arr[8].BREADY;
    assign i3c_s_axi_if.arvalid                    = axi_interconnect.sintf_arr[8].ARVALID;
    assign i3c_s_axi_if.araddr                     = axi_interconnect.sintf_arr[8].ARADDR;
    assign i3c_s_axi_if.arid                       = axi_interconnect.sintf_arr[8].ARID;
    assign i3c_s_axi_if.arlen                      = axi_interconnect.sintf_arr[8].ARLEN;
    assign i3c_s_axi_if.arsize                     = axi_interconnect.sintf_arr[8].ARSIZE;
    assign i3c_s_axi_if.arburst                    = axi_interconnect.sintf_arr[8].ARBURST;
    assign i3c_s_axi_if.arlock                     = axi_interconnect.sintf_arr[8].ARLOCK;
    assign i3c_s_axi_if.aruser                     = axi_interconnect.sintf_arr[8].ARUSER;
    assign axi_interconnect.sintf_arr[8].ARREADY = i3c_s_axi_if.arready;
    assign axi_interconnect.sintf_arr[8].RVALID  = i3c_s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[8].RDATA   = 64'(i3c_s_axi_if.rdata) << (i3c_s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[8].RRESP   = i3c_s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[8].RID     = i3c_s_axi_if.rid;
    assign axi_interconnect.sintf_arr[8].RLAST   = i3c_s_axi_if.rlast;
    assign i3c_s_axi_if.rready                     = axi_interconnect.sintf_arr[8].RREADY;

    always_comb begin
        mcu_lsu_m_axi_if.awuser                                              = 32'hFFFF_FFFF;
        mcu_lsu_m_axi_if.aruser                                              = 32'hFFFF_FFFF;
        mcu_lsu_m_axi_if.arid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
        mcu_lsu_m_axi_if.awid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
        mcu_lsu_m_axi_if.aruser[aaxi_pkg::AAXI_ARUSER_WIDTH-1:0]             = '1;
        mcu_lsu_m_axi_if.awuser[aaxi_pkg::AAXI_AWUSER_WIDTH-1:0]             = '1;
        mcu_lsu_m_axi_if.araddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        mcu_lsu_m_axi_if.awaddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        mcu_ifu_m_axi_if.arid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
        mcu_ifu_m_axi_if.awid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
        mcu_ifu_m_axi_if.araddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        mcu_ifu_m_axi_if.awaddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        mcu_dma_s_axi_if.rid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
        mcu_dma_s_axi_if.bid[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
        mcu_dma_s_axi_if.araddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        mcu_dma_s_axi_if.awaddr[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
    end

    mci_mcu_sram_if mci_mcu_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );

    mci_mcu_sram_if mci_mbox0_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );
    
    mci_mcu_sram_if mci_mbox1_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );

    //=================== BEGIN CALIPTRA_TOP_TB ========================

    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;
    logic                       BootFSM_BrkPoint;
    logic                       scan_mode;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key;
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0]     cptra_csr_hmac_key;
    
    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    //jtag interface
    logic                      cptra_core_jtag_tck;    // JTAG clk
    logic                      cptra_core_jtag_tms;    // JTAG TMS
    logic                      cptra_core_jtag_tdi;    // JTAG tdi
    logic                      cptra_core_jtag_trst_n; // JTAG Reset
    logic                      cptra_core_jtag_tdo;    // JTAG TDO
    logic                      cptra_core_jtag_tdoEn;  // JTAG TDO enable

    logic ready_for_fuses;
    logic ready_for_mb_processing;
    logic mailbox_data_avail;
    logic cptra_core_mbox_sram_cs;
    logic cptra_core_mbox_sram_we;
    logic [CPTRA_MBOX_ADDR_W:0] cptra_core_mbox_sram_addr;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_core_mbox_sram_wdata;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_core_mbox_sram_rdata;

    logic cptra_core_imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] cptra_core_imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] cptra_core_imem_rdata;


    ras_test_ctrl_t ras_test_ctrl;
    logic [63:0] cptra_core_generic_input_wires;
    logic        cptra_core_etrng_req;
    logic  [3:0] cptra_core_itrng_data;
    logic        cptra_core_itrng_valid;

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

    logic cptra_soc_bfm_rst_b;


    caliptra_top_tb_soc_bfm #(
        .SKIP_BRINGUP(1)
    ) soc_bfm_inst (
        .core_clk        (core_clk        ),

        .cptra_pwrgood   (cptra_pwrgood   ),
        .cptra_rst_b     (cptra_soc_bfm_rst_b     ),

        .BootFSM_BrkPoint(BootFSM_BrkPoint),
        .cycleCnt        (cycleCnt        ),


        .cptra_obf_key     (cptra_obf_key     ),
        .cptra_csr_hmac_key(cptra_csr_hmac_key),

        .cptra_uds_rand  (cptra_uds_rand  ),
        .cptra_fe_rand   (cptra_fe_rand   ),
        .cptra_obf_key_tb(cptra_obf_key_tb),

        .m_axi_bfm_if(m_axi_bfm_if),

        .ready_for_fuses         (ready_for_fuses         ),
        .ready_for_mb_processing (ready_for_mb_processing ),
        .mailbox_data_avail      (mailbox_data_avail      ),

        .ras_test_ctrl(ras_test_ctrl),

        .generic_input_wires(cptra_core_generic_input_wires),

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
    ) jtagdpi (
        .clk_i          (core_clk),
        .rst_ni         (cptra_rst_b),
        .jtag_tck       (cptra_jtag_tck),
        .jtag_tms       (cptra_jtag_tms),
        .jtag_tdi       (cptra_jtag_tdi),
        .jtag_tdo       (cptra_jtag_tdo),
        .jtag_trst_n    (cptra_jtag_trst_n),
        .jtag_srst_n    ()
    );



`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
    physical_rng physical_rng (
        .clk    (core_clk),
        .enable (cptra_core_etrng_req),
        .data   (cptra_core_itrng_data),
        .valid  (cptra_core_itrng_valid)
    );
`endif

    //=========================================================================-
    // Services for SRAM exports, STDOUT, etc
    //=========================================================================-
    caliptra_top_tb_services #(
        .UVM_TB(0)
    ) tb_services_i (
        .clk(core_clk),

        .cptra_rst_b(cptra_rst_b),

        // Caliptra Memory Export Interface
        .el2_mem_export (cptra_core_el2_mem_export.veer_sram_sink),

        //SRAM interface for mbox
        .mbox_sram_cs   (cptra_core_mbox_sram_cs   ),
        .mbox_sram_we   (cptra_core_mbox_sram_we   ),
        .mbox_sram_addr (cptra_core_mbox_sram_addr ),
        .mbox_sram_wdata(cptra_core_mbox_sram_wdata),
        .mbox_sram_rdata(cptra_core_mbox_sram_rdata),

        //SRAM interface for imem
        .imem_cs   (cptra_core_imem_cs   ),
        .imem_addr (cptra_core_imem_addr ),
        .imem_rdata(cptra_core_imem_rdata),

        // Security State
        .security_state(), // TODO: Remove this since we do not need it anymore, thanks to MCI

        //Scan mode
        .scan_mode(scan_mode),

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

    //=========================================================================-
    // AXI MEM instance : IMEM
    //=========================================================================-
    //axi_slv #(.TAGW(`css_mcu0_RV_LSU_BUS_TAG)) imem(

    axi_slv #(.TAGW(8)) imem(

        .aclk           (core_clk),
        .rst_l          (rst_l),

        .arvalid        (axi_interconnect.sintf_arr[0].ARVALID),
        .arready        (axi_interconnect.sintf_arr[0].ARREADY),
        .araddr         (axi_interconnect.sintf_arr[0].ARADDR[31:0]),
        .arid           (axi_interconnect.sintf_arr[0].ARID),
        .arlen          (axi_interconnect.sintf_arr[0].ARLEN),
        .arburst        (axi_interconnect.sintf_arr[0].ARBURST),
        .arsize         (axi_interconnect.sintf_arr[0].ARSIZE),

        .rvalid         (axi_interconnect.sintf_arr[0].RVALID),
        .rready         (axi_interconnect.sintf_arr[0].RREADY),
        .rdata          (axi_interconnect.sintf_arr[0].RDATA),
        .rresp          (axi_interconnect.sintf_arr[0].RRESP),
        .rid            (axi_interconnect.sintf_arr[0].RID),
        .rlast          (axi_interconnect.sintf_arr[0].RLAST),

        .awvalid        (axi_interconnect.sintf_arr[0].AWVALID),
        .awready        (axi_interconnect.sintf_arr[0].AWREADY),
        .awaddr         (axi_interconnect.sintf_arr[0].AWADDR[31:0]),
        .awid           (axi_interconnect.sintf_arr[0].AWID),
        .awlen          (axi_interconnect.sintf_arr[0].AWLEN),
        .awburst        (axi_interconnect.sintf_arr[0].AWBURST),
        .awsize         (axi_interconnect.sintf_arr[0].AWSIZE),

        .wdata          (axi_interconnect.sintf_arr[0].WDATA),
        .wstrb          (axi_interconnect.sintf_arr[0].WSTRB),
        .wvalid         (axi_interconnect.sintf_arr[0].WVALID),
        .wready         (axi_interconnect.sintf_arr[0].WREADY),

        .bvalid         (axi_interconnect.sintf_arr[0].BVALID),
        .bready         (axi_interconnect.sintf_arr[0].BREADY),
        .bresp          (axi_interconnect.sintf_arr[0].BRESP),
        .bid            (axi_interconnect.sintf_arr[0].BID)

    );
    assign axi_interconnect.sintf_arr[0].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    assign axi_interconnect.sintf_arr[0].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;

    //-- Slave port 1 free to use. Moved LMEM to MCI
    assign axi_interconnect.sintf_arr[1].AWREADY = 1'b1;
    assign axi_interconnect.sintf_arr[1].WREADY  = 1'b1;
    assign axi_interconnect.sintf_arr[1].BVALID  = 1'b0;
    assign axi_interconnect.sintf_arr[1].ARREADY = 1'b1;
    assign axi_interconnect.sintf_arr[1].RVALID  = 1'b0;

    mci_sram #(
        .DEPTH     (18'h3_FFFF), // 1M
        .DATA_WIDTH(39),
        .ADDR_WIDTH(32)
   ) lmem (
       .clk_i   (core_clk),
   
       .cs_i    (mci_mcu_sram_req_if.req.cs),
       .we_i    (mci_mcu_sram_req_if.req.we),
       .addr_i  ({14'h0, mci_mcu_sram_req_if.req.addr, 2'b0}),
       .wdata_i (mci_mcu_sram_req_if.req.wdata),
       .rdata_o (mci_mcu_sram_req_if.resp.rdata)
   );

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
   logic [$bits(otp_ctrl_pkg::otp_lc_data_t)-1:0] otp_lc_data_tb;
   logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_clk_byp_ack_tb;
   assign lc_otp_vendor_test_o_tb = otp_ctrl_pkg::lc_otp_vendor_test_req_t'(caliptra_ss_dut.u_lc_ctrl.lc_otp_vendor_test_o);
   assign lc_otp_vendor_test_i_tb = otp_ctrl_pkg::lc_otp_vendor_test_rsp_t'(caliptra_ss_dut.u_otp_ctrl.lc_otp_vendor_test_o);
   assign lc_otp_program_i_tb = otp_ctrl_pkg::lc_otp_program_rsp_t'(caliptra_ss_dut.u_otp_ctrl.lc_otp_program_o);

   assign lc_creator_seed_sw_rw_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_creator_seed_sw_rw_en_o);
   assign lc_owner_seed_sw_rw_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_owner_seed_sw_rw_en_o);
   assign lc_seed_hw_rd_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_seed_hw_rd_en_o);
   assign lc_escalate_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_escalate_en_o);
   assign lc_check_byp_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_check_byp_en_o);
   assign lc_clk_byp_ack_tb = lc_ctrl_pkg::lc_tx_t'(u_lc_ctrl_bfm.lc_clk_byp_ack_i);
   //--------------------------------------------------------------------------------------------
   // These are going to be connected to SoC later on
   logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_cpu_en_tb;
   assign lc_cpu_en_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_cpu_en_o);
   //--------------------------------------------------------------------------------------------

   //--------------------------------------------------------------------------------------------
   // These are driven by the lc ctrl bfm
   logic [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_clk_byp_req_tb;
   assign lc_clk_byp_req_tb = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_clk_byp_req_o);

   logic [$bits(pwrmgr_pkg::pwr_lc_req_t)-1:0] pwr_lc_i_tb;
   logic [$bits(pwrmgr_pkg::pwr_lc_rsp_t)-1:0] pwr_lc_o_tb;
   // Assignments for Power Manager Interface
   assign pwr_lc_i_tb = pwrmgr_pkg::pwr_lc_req_t'(u_lc_ctrl_bfm.pwr_lc_i);
   assign pwr_lc_o_tb = pwrmgr_pkg::pwr_lc_rsp_t'(caliptra_ss_dut.u_lc_ctrl.pwr_lc_o);

   logic [3:0]  to_bfm_lc_flash_rma_req_o;
   assign to_bfm_lc_flash_rma_req_o = lc_ctrl_pkg::lc_tx_t'(caliptra_ss_dut.u_lc_ctrl.lc_flash_rma_req_o);

   logic [lc_ctrl_reg_pkg::NumAlerts-1:0] lc_alerts_o;

   logic esc_scrap_state0;
   logic esc_scrap_state1;

   // Scan Interface
   logic lc_ctrl_scan_rst_ni_tb;
   logic [$bits(caliptra_prim_mubi_pkg::mubi4_t)-1:0] lc_ctrl_scanmode_i_tb;
   assign lc_ctrl_scanmode_i_tb = caliptra_prim_mubi_pkg::mubi4_t'(u_lc_ctrl_bfm.lc_ctrl_scanmode_i);

    lc_ctrl_bfm u_lc_ctrl_bfm (
        .clk(core_clk),
        .reset_n(rst_l),


        .lc_axi_rd_req(lc_axi_rd_req),
        .lc_axi_rd_rsp(lc_axi_rd_rsp),
        .fake_reset(fake_reset),
        .Allow_RMA_on_PPD(Allow_RMA_on_PPD),


        // Scan Interface
        .lc_ctrl_scan_rst_ni(lc_ctrl_scan_rst_ni_tb),
        .lc_ctrl_scanmode_i(),

        // Alert Handler Interface
        .lc_alerts_o(lc_alerts_o),

        // Escalation State Interface
        .esc_scrap_state0(esc_scrap_state0),
        .esc_scrap_state1(esc_scrap_state1),


        // OTP hack
        .otp_lc_data_o(otp_lc_data_tb),
        .from_otp_lc_data_i(from_otp_to_lcc_program_i),

        // Power manager interface
        .pwr_lc_i(),
        .pwr_lc_o(pwrmgr_pkg::pwr_lc_rsp_t'(pwr_lc_o_tb)),
        .cptra_pwrgood(cptra_pwrgood),

        // Clock manager interface
        .lc_clk_byp_req_o(lc_ctrl_pkg::lc_tx_t'(lc_clk_byp_req_tb)),
        .lc_clk_byp_ack_i()
    );

    //--------------------------------------------------------------------------------------------

    assign lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(caliptra_ss_dut.u_lc_ctrl.pwr_lc_o.lc_done);
    assign lcc_init_req.lc_init = mci_to_lcc_init_req; 


    fuse_ctrl_bfm u_fuse_ctrl_bfm (
        .core_clk            (core_clk            ),
        .cptra_pwrgood       (cptra_pwrgood       ),
        .fc_partition_init   (pwr_otp_init_i      ),
        .lc_dft_en_i         (),
        .lc_escalate_en_i    (),
        .lc_check_byp_en_i   (),
        .otp_lc_data_o (otp_ctrl_pkg::otp_lc_data_t'(otp_lc_data_tb)),
        .fuse_ctrl_rdy       (fuse_ctrl_rdy       )
    );


//instantiate caliptra ss top module
    caliptra_ss_top
    caliptra_ss_dut (
        .cptra_ss_clk(core_clk),
        .cptra_ss_pwrgood(1), //fixme
        .cptra_ss_rst_b(rst_l),
    
        //SoC AXI Interface
        .cptra_core_s_axi_if,
    
        // AXI Manager INF
        .cptra_core_m_axi_if,
    
        //SoC AXI Interface
        .mci_s_axi_if,
    
        // AXI Manager INF
        .mci_m_axi_if,
    
        .mcu_lsu_m_axi_if,
        .mcu_ifu_m_axi_if,
        .mcu_dma_s_axi_if,
        .i3c_s_axi_if,
    
        .lc_axi_wr_req,
        .lc_axi_wr_rsp,
        .lc_axi_rd_req,
        .lc_axi_rd_rsp,
    
        .core_axi_wr_req,
        .core_axi_wr_rsp,
        .core_axi_rd_req,
        .core_axi_rd_rsp,
    
        //--------------------
        //caliptra core signals
        //--------------------
        .cptra_obf_key,
        .cptra_csr_hmac_key,  
        //Caliptra JTAG Interface
        .cptra_core_jtag_tck,    // JTAG clk
        .cptra_core_jtag_tms,    // JTAG TMS
        .cptra_core_jtag_tdi,    // JTAG tdi
        .cptra_core_jtag_trst_n, // JTAG Reset
        .cptra_core_jtag_tdo,    // JTAG TDO
        .cptra_core_jtag_tdoEn,  // JTAG TDO enable
    
        // Caliptra Memory Export Interface
        .cptra_core_el2_mem_export,
    
        //SRAM interface for mbox
        .cptra_core_mbox_sram_cs,
        .cptra_core_mbox_sram_we,
        .cptra_core_mbox_sram_addr,
        .cptra_core_mbox_sram_wdata,
        .cptra_core_mbox_sram_rdata,
    
        //SRAM interface for imem
        .cptra_core_imem_cs,
        .cptra_core_imem_addr,
        .cptra_core_imem_rdata,
        
        .ready_for_fuses,
        .ready_for_mb_processing,
    
        .mailbox_data_avail,
    
        .BootFSM_BrkPoint,
    
        //SoC Interrupts
        .cptra_error_fatal,
        .cptra_error_non_fatal,
    
        // TRNG Interface
        `ifdef CALIPTRA_INTERNAL_TRNG
        // External Request
        .cptra_core_etrng_req,
        // Physical Source for Internal TRNG
        .cptra_core_itrng_data,
        .cptra_core_itrng_valid,
        `endif
    
        .cptra_core_generic_input_wires,
        .cptra_core_generic_output_wires(),
    
        .scan_mode,
    
        //MCU
        .mci_mcu_sram_req_if,
        .mci_mbox0_sram_req_if,
    
        .mci_mbox1_sram_req_if,
    
        .css_mcu0_el2_mem_export,
    
        .Allow_RMA_on_PPD,
        .fake_reset,
    
        .lc_ctrl_scan_rst_ni(lc_ctrl_scan_rst_ni_tb),
        .lc_ctrl_scanmode_i(lc_ctrl_scanmode_i_tb),
    
    
        .otp_lc_data(otp_lc_data_tb),
        .lc_clk_byp_ack(lc_clk_byp_ack_tb),
        .lc_alerts_o,
    
        .esc_scrap_state0,
        .esc_scrap_state1,
    
        .SOC_DFT_EN,
        .SOC_HW_DEBUG_EN,
    
        `ifdef VERILATOR
        .mem_signature_begin,
        .mem_signature_end,
        .mem_mailbox,
        `endif // VERILATOR
        // I3C Interface
        `ifdef VERILATOR
        .scl_i,
        .sda_i,
        .scl_o,
        .sda_o,
        .sel_od_pp_o
        `else
        .i3c_scl_io,
        .i3c_sda_io
        `endif
    );
    


task preload_iccm;
    bit[31:0] data;
    bit[31:0] addr, eaddr, saddr;

    /*
    addresses:
     0xfffffff0 - ICCM start address to load
     0xfffffff4 - ICCM end address to load
    */
    `ifndef VERILATOR
    init_iccm();
    `endif
    addr = 'hffff_fff0;
    saddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
    if ( (saddr < `css_mcu0_RV_ICCM_SADR) || (saddr > `css_mcu0_RV_ICCM_EADR)) return;
    `ifndef MCU_RV_ICCM_ENABLE
        $display("********************************************************");
        $display("ICCM preload: there is no ICCM in VeeR, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    addr += 4;
    eaddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
    $display("ICCM pre-load from %h to %h", saddr, eaddr);

    for(addr= saddr; addr <= eaddr; addr+=4) begin
        data = {imem.mem[addr+3],imem.mem[addr+2],imem.mem[addr+1],imem.mem[addr]};
        slam_iccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end

endtask


// task preload_dccm;
//     bit[31:0] data;
//     bit[31:0] addr, saddr, eaddr;

//     /*
//     addresses:
//      0xffff_fff8 - DCCM start address to load
//      0xffff_fffc - DCCM end address to load
//     */

//     addr = 'hffff_fff8;
//     saddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
//     if (saddr < `css_mcu0_RV_DCCM_SADR || saddr > `css_mcu0_RV_DCCM_EADR) return;
//     `ifndef MCU_RV_DCCM_ENABLE
//         $display("********************************************************");
//         $display("DCCM preload: there is no DCCM in VeeR, terminating !!!");
//         $display("********************************************************");
//         $finish;
//     `endif
//     addr += 4;
//     eaddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
//     $display("DCCM pre-load from %h to %h", saddr, eaddr);

//     for(addr=saddr; addr <= eaddr; addr+=4) begin
//         data = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
//         slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
//     end
// endtask



`ifdef VERILATOR
`define MCU_DRAM(bk) css_mcu0_dccm_enable.dccm_loop[bk].ram.ram_core
`define MCU_IRAM(bk) Gen_iccm_enable.iccm_loop[bk].iccm_bank.ram_core
`else
`define MCU_DRAM(bk) css_mcu0_dccm_enable.dccm_loop[bk].dccm.dccm_bank.ram_core
`define MCU_IRAM(bk) Gen_iccm_enable.iccm_loop[bk].iccm.iccm_bank.ram_core
`endif





task slam_iccm_ram( input[31:0] addr, input[38:0] data);
    int bank, idx;

    bank = get_iccm_bank(addr, idx);
    `ifdef css_mcu0_RV_ICCM_ENABLE
    case(bank) // {
      0: `MCU_IRAM(0)[idx] = data;
      1: `MCU_IRAM(1)[idx] = data;
     `ifdef css_mcu0_RV_ICCM_NUM_BANKS_4
      2: `MCU_IRAM(2)[idx] = data;
      3: `MCU_IRAM(3)[idx] = data;
     `endif
     `ifdef css_mcu0_RV_ICCM_NUM_BANKS_8
      2: `MCU_IRAM(2)[idx] = data;
      3: `MCU_IRAM(3)[idx] = data;
      4: `MCU_IRAM(4)[idx] = data;
      5: `MCU_IRAM(5)[idx] = data;
      6: `MCU_IRAM(6)[idx] = data;
      7: `MCU_IRAM(7)[idx] = data;
     `endif

     `ifdef MCU_RV_ICCM_NUM_BANKS_16
      2: `MCU_IRAM(2)[idx] = data;
      3: `MCU_IRAM(3)[idx] = data;
      4: `MCU_IRAM(4)[idx] = data;
      5: `MCU_IRAM(5)[idx] = data;
      6: `MCU_IRAM(6)[idx] = data;
      7: `MCU_IRAM(7)[idx] = data;
      8: `MCU_IRAM(8)[idx] = data;
      9: `MCU_IRAM(9)[idx] = data;
      10: `MCU_IRAM(10)[idx] = data;
      11: `MCU_IRAM(11)[idx] = data;
      12: `MCU_IRAM(12)[idx] = data;
      13: `MCU_IRAM(13)[idx] = data;
      14: `MCU_IRAM(14)[idx] = data;
      15: `MCU_IRAM(15)[idx] = data;
     `endif
    endcase // }
    `endif
endtask

task init_iccm;
    `ifdef css_mcu0_RV_ICCM_ENABLE
        `MCU_IRAM(0) = '{default:39'h0};
        `MCU_IRAM(1) = '{default:39'h0};
    `ifdef css_mcu0_RV_ICCM_NUM_BANKS_4
        `MCU_IRAM(2) = '{default:39'h0};
        `MCU_IRAM(3) = '{default:39'h0};
    `endif
    `ifdef css_mcu0_RV_ICCM_NUM_BANKS_8
        `MCU_IRAM(4) = '{default:39'h0};
        `MCU_IRAM(5) = '{default:39'h0};
        `MCU_IRAM(6) = '{default:39'h0};
        `MCU_IRAM(7) = '{default:39'h0};
    `endif

    `ifdef css_mcu0_RV_ICCM_NUM_BANKS_16
        `MCU_IRAM(4) = '{default:39'h0};
        `MCU_IRAM(5) = '{default:39'h0};
        `MCU_IRAM(6) = '{default:39'h0};
        `MCU_IRAM(7) = '{default:39'h0};
        `MCU_IRAM(8) = '{default:39'h0};
        `MCU_IRAM(9) = '{default:39'h0};
        `MCU_IRAM(10) = '{default:39'h0};
        `MCU_IRAM(11) = '{default:39'h0};
        `MCU_IRAM(12) = '{default:39'h0};
        `MCU_IRAM(13) = '{default:39'h0};
        `MCU_IRAM(14) = '{default:39'h0};
        `MCU_IRAM(15) = '{default:39'h0};
     `endif
    `endif
endtask


function[6:0] riscv_ecc32(input[31:0] data);
    reg[6:0] synd;
    synd[0] = ^(data & 32'h56aa_ad5b);
    synd[1] = ^(data & 32'h9b33_366d);
    synd[2] = ^(data & 32'he3c3_c78e);
    synd[3] = ^(data & 32'h03fc_07f0);
    synd[4] = ^(data & 32'h03ff_f800);
    synd[5] = ^(data & 32'hfc00_0000);
    synd[6] = ^{data, synd[5:0]};
    return synd;
endfunction

function int get_dccm_bank(input[31:0] addr,  output int bank_idx);
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif css_mcu0_RV_DCCM_NUM_BANKS_4
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif css_mcu0_RV_DCCM_NUM_BANKS_8
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:5]);
        return int'( addr[4:2]);
    `endif
endfunction

function int get_iccm_bank(input[31:0] addr,  output int bank_idx);
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif css_mcu0_RV_ICCM_NUM_BANKS_4
        bank_idx = int'(addr[`css_mcu0_RV_ICCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif css_mcu0_RV_ICCM_NUM_BANKS_8
        bank_idx = int'(addr[`css_mcu0_RV_ICCM_BITS-1:5]);
        return int'( addr[4:2]);
    `elsif css_mcu0_RV_ICCM_NUM_BANKS_16
        bank_idx = int'(addr[`css_mcu0_RV_ICCM_BITS-1:6]);
        return int'( addr[5:2]);
    `endif
endfunction

task dump_signature ();
        integer fp, i;

        $display("Dumping memory signature (0x%08X - 0x%08X)...",
            mem_signature_begin,
            mem_signature_end
        );

        fp = $fopen("veer.signature", "w");
        for (i=mem_signature_begin; i<mem_signature_end; i=i+4) begin

            // From DCCM
    `ifdef css_mcu0_RV_DCCM_ENABLE
            if (i >= `css_mcu0_RV_DCCM_SADR && i < `css_mcu0_RV_DCCM_EADR) begin
                bit[38:0] data;
                int bank, indx;
                bank = get_dccm_bank(i, indx);

                case (bank)
                0: data = `MCU_DRAM(0)[indx];
                1: data = `MCU_DRAM(1)[indx];
                `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
                2: data = `MCU_DRAM(2)[indx];
                3: data = `MCU_DRAM(3)[indx];
                `endif
                `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
                2: data = `MCU_DRAM(2)[indx];
                3: data = `MCU_DRAM(3)[indx];
                4: data = `MCU_DRAM(4)[indx];
                5: data = `MCU_DRAM(5)[indx];
                6: data = `MCU_DRAM(6)[indx];
                7: data = `MCU_DRAM(7)[indx];
                `endif
                endcase

                $fwrite(fp, "%08X\n", data[31:0]);
            end else
    `endif
            // From RAM
            begin
                $fwrite(fp, "%02X%02X%02X%02X\n",
                    lmem.mem[i+3],
                    lmem.mem[i+2],
                    lmem.mem[i+1],
                    lmem.mem[i+0]
                );
            end
        end

        $fclose(fp);
endtask



// -- DCCM PRELOAD
caliptra_sram #(
     .DEPTH     (16384        ), // 128KiB
     .DATA_WIDTH(64           ),
     .ADDR_WIDTH($clog2(16384))

) css_mcu0_dummy_dccm_preloader (
    .clk_i   (core_clk),

    .cs_i    (        ),
    .we_i    (        ),
    .addr_i  (        ),
    .wdata_i (        ),
    .rdata_o (        )
);

task static init_css_mcu0_dccm;
    `ifdef css_mcu0_RV_DCCM_ENABLE
        `MCU_DRAM(0) = '{default:39'h0};
        `MCU_DRAM(1) = '{default:39'h0};
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
        `MCU_DRAM(2) = '{default:39'h0};
        `MCU_DRAM(3) = '{default:39'h0};
    `endif
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
        `MCU_DRAM(4) = '{default:39'h0};
        `MCU_DRAM(5) = '{default:39'h0};
        `MCU_DRAM(6) = '{default:39'h0};
        `MCU_DRAM(7) = '{default:39'h0};
    `endif
    `endif
endtask

task slam_dccm_ram(input [31:0] addr, input[38:0] data);
    int bank, indx;
    bank = get_dccm_bank(addr, indx);
    `ifdef css_mcu0_RV_DCCM_ENABLE
    case(bank)
    0: `MCU_DRAM(0)[indx] = data;
    1: `MCU_DRAM(1)[indx] = data;
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_4
    2: `MCU_DRAM(2)[indx] = data;
    3: `MCU_DRAM(3)[indx] = data;
    `endif
    `ifdef css_mcu0_RV_DCCM_NUM_BANKS_8
    2: `MCU_DRAM(2)[indx] = data;
    3: `MCU_DRAM(3)[indx] = data;
    4: `MCU_DRAM(4)[indx] = data;
    5: `MCU_DRAM(5)[indx] = data;
    6: `MCU_DRAM(6)[indx] = data;
    7: `MCU_DRAM(7)[indx] = data;
    `endif
    endcase
    `endif
    //$display("Writing bank %0d indx=%0d A=%h, D=%h",bank, indx, addr, data);
endtask

task static preload_css_mcu0_dccm;
    bit[31:0] data;
    bit[31:0] addr, saddr, eaddr;

    `ifndef VERILATOR
    init_css_mcu0_dccm();
    `endif
    saddr = `css_mcu0_RV_DCCM_SADR;
    if (saddr < `css_mcu0_RV_DCCM_SADR || saddr > `css_mcu0_RV_DCCM_EADR) return;
    `ifndef css_mcu0_RV_DCCM_ENABLE
        $display("********************************************************");
        $display("DCCM preload: there is no DCCM in VeeR, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    eaddr = `css_mcu0_RV_DCCM_EADR;
    $display("CSS MCU0 DCCM pre-load from %h to %h", saddr, eaddr);

    for(addr=saddr; addr <= eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h3}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h2}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h1}],
                css_mcu0_dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h0}]};
        slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end
    $display("CSS MCU0 DCCM pre-load completed");

endtask



//////////////////////////////////////////////////////
// DCCM
//
if (pt.DCCM_ENABLE == 1) begin: css_mcu0_dccm_enable
    `define MCU_LOCAL_DCCM_RAM_TEST_PORTS   .TEST1   (1'b0   ), \
                                            .RME     (1'b0   ), \
                                            .RM      (4'b0000), \
                                            .LS      (1'b0   ), \
                                            .DS      (1'b0   ), \
                                            .SD      (1'b0   ), \
                                            .TEST_RNM(1'b0   ), \
                                            .BC1     (1'b0   ), \
                                            .BC2     (1'b0   ), \

    logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0] dccm_wdata_bitflip;
    int ii;
    localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank
    // 8 Banks, 16KB each (2048 x 72)
    always_ff @(css_mcu0_el2_mem_export.clk) begin : inject_dccm_ecc_error
        // if (~error_injection_mode.dccm_single_bit_error && ~error_injection_mode.dccm_double_bit_error) begin
        //     dccm_wdata_bitflip <= '{default:0};
        // end else if (css_mcu0_el2_mem_export.dccm_clken & css_mcu0_el2_mem_export.dccm_wren_bank) begin
        //     for (ii=0; ii<pt.DCCM_NUM_BANKS; ii++) begin: dccm_bitflip_injection_loop
        //         dccm_wdata_bitflip[ii] <= get_bitflip_mask(error_injection_mode.dccm_double_bit_error);
        //     end
        // end
        dccm_wdata_bitflip <= '{default:0};
    end
    for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop

        assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0] = {css_mcu0_el2_mem_export.dccm_wr_ecc_bank[i], css_mcu0_el2_mem_export.dccm_wr_data_bank[i]} ^ dccm_wdata_bitflip[i];
        assign css_mcu0_el2_mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][31:0];
        assign css_mcu0_el2_mem_export.dccm_bank_ecc[i] = dccm_bank_fdout[i][38:32];

    `ifdef VERILATOR

            el2_ram #(DCCM_INDEX_DEPTH,39)  ram (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
    `else

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
	 	 	 	 css_mcu0_ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
	 	 	 	 css_mcu0_ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
	 	 	 	 css_mcu0_ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
	 	 	 	 css_mcu0_ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
	 	 	 	 css_mcu0_ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
	 	 	 	 css_mcu0_ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
	 	 	 	 css_mcu0_ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
	 	 	 	 css_mcu0_ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
	 	 	 	 css_mcu0_ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
	 	 	 	 css_mcu0_ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(css_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(css_mcu0_el2_mem_export.clk),
                                    .WE(css_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(css_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
    `endif
    end : dccm_loop
end :css_mcu0_dccm_enable

//////////////////////////////////////////////////////
// ICCM
//
if (pt.ICCM_ENABLE) begin : Gen_iccm_enable

logic [pt.ICCM_NUM_BANKS-1:0] [38:0] iccm_wdata_bitflip;
int jj;
always_ff @(css_mcu0_el2_mem_export.clk) begin : inject_iccm_ecc_error
    if (~error_injection_mode.iccm_single_bit_error && ~error_injection_mode.iccm_double_bit_error) begin
        iccm_wdata_bitflip <= '{default:0};
    end else if (css_mcu0_el2_mem_export.iccm_clken & css_mcu0_el2_mem_export.iccm_wren_bank) begin
        for (jj=0; jj<pt.ICCM_NUM_BANKS; jj++) begin: iccm_bitflip_injection_loop
            iccm_wdata_bitflip[jj] <= get_bitflip_mask(error_injection_mode.iccm_double_bit_error);
        end
    end
end
for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin: iccm_loop
    // -- new --- assign iccm_bank_wr_fdata[i][31:0] = css_mcu0_el2_mem_export.iccm_bank_wr_data[i];
    // -- new --- assign iccm_bank_wr_fdata[i][38:32] = css_mcu0_el2_mem_export.iccm_bank_wr_ecc[i];
    // -- new --- assign css_mcu0_el2_mem_export.iccm_bank_dout[i] = iccm_bank_fdout[i][31:0];
    // -- new --- assign css_mcu0_el2_mem_export.iccm_bank_ecc[i] = iccm_bank_fdout[i][38:32];
    //assign css_mcu0_el2_mem_export.iccm_bank_wr_data[i] = iccm_bank_wr_fdata[i][31:0];
    //assign css_mcu0_el2_mem_export.iccm_bank_wr_ecc[i] = iccm_bank_wr_fdata[i][37:32];
    //assign iccm_bank_fdout[i] = {css_mcu0_el2_mem_export.iccm_bank_ecc[i], css_mcu0_el2_mem_export.iccm_bank_dout[i]};

    `ifdef VERILATOR

    el2_ram #(.depth(1<<pt.ICCM_INDEX_BITS), .width(39)) iccm_bank (
                                        // Primary ports
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
    `else

        if (pt.ICCM_INDEX_BITS == 6 ) begin : iccm
	 	 	 	 css_mcu0_ram_64x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm

    else if (pt.ICCM_INDEX_BITS == 7 ) begin : iccm
	 	 	 	 css_mcu0_ram_128x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm

        else if (pt.ICCM_INDEX_BITS == 8 ) begin : iccm
	 	 	 	 css_mcu0_ram_256x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 9 ) begin : iccm
	 	 	 	 css_mcu0_ram_512x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 10 ) begin : iccm
	 	 	 	 css_mcu0_ram_1024x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 11 ) begin : iccm
	 	 	 	 css_mcu0_ram_2048x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 12 ) begin : iccm
	 	 	 	 css_mcu0_ram_4096x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 13 ) begin : iccm
	 	 	 	 css_mcu0_ram_8192x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else if (pt.ICCM_INDEX_BITS == 14 ) begin : iccm
	 	 	 	 css_mcu0_ram_16384x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
        else begin : iccm
	 	 	 	 css_mcu0_ram_32768x39 iccm_bank (
                                        // Primary ports
                                        .CLK(css_mcu0_el2_mem_export.clk),
                                        .ME(css_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(css_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(css_mcu0_el2_mem_export.iccm_addr_bank[i]),
                                        .D(iccm_bank_wr_fdata[i][38:0]),
                                        .Q(iccm_bank_fdout[i][38:0]),
                                        .ROP ( ),
                                        // These are used by SoC
                                        .TEST1    (1'b0   ),
                                        .RME      (1'b0   ),
                                        .RM       (4'b0000),
                                        .LS       (1'b0   ),
                                        .DS       (1'b0   ),
                                        .SD       (1'b0   ) ,
                                        .TEST_RNM (1'b0   ),
                                        .BC1      (1'b0   ),
                                        .BC2      (1'b0   )

                                        );
        end // block: iccm
`endif
end : iccm_loop
end : Gen_iccm_enable

`include "icache_macros.svh"

// ICACHE DATA
 if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_0
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
      for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
      if (pt.ICACHE_ECC) begin : ECC1
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM(8192,71,i,k)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM(4096,71,i,k)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM(2048,71,i,k)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM(1024,71,i,k)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM(512,71,i,k)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM(256,71,i,k)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM(128,71,i,k)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM(64,71,i,k)
         end
      end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM(8192,68,i,k)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM(4096,68,i,k)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM(2048,68,i,k)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM(1024,68,i,k)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM(512,68,i,k)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM(256,68,i,k)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM(128,68,i,k)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM(64,68,i,k)
         end
      end // else: !if(pt.ICACHE_ECC)
      end // block: BANKS_WAY
   end // block: WAYS

 end // block: PACKED_0

 // WAY PACKED
 else begin : PACKED_10

 // generate IC DATA PACKED SRAMS for 2/4 ways
  for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
     if (pt.ICACHE_ECC) begin : ECC1
        // SRAMS with ECC (single/double detect; no correct)
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,284,71,k)    // 64b data + 7b ecc
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,142,71,k)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,142,71,k)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,142,71,k)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,142,71,k)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,142,71,k)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,142,71,k)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,142,71,k)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,284,71,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,142,71,k)
           end // block: WAYS
        end // block: size_64
       end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        // SRAMs with parity
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,272,68,k)    // 64b data + 4b parity
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,136,68,k)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,136,68,k)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,136,68,k)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,136,68,k)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,136,68,k)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,136,68,k)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,136,68,k)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,272,68,k)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,136,68,k)
           end // block: WAYS
        end // block: size_64
     end // block: ECC0
     end // block: BANKS_WAY
 end // block: PACKED_10


// ICACHE TAG
if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_11
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                 `EL2_IC_TAG_SRAM(32,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 32)
        if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                 `EL2_IC_TAG_SRAM(64,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 64)
        if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                 `EL2_IC_TAG_SRAM(128,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 128)
        if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                 `EL2_IC_TAG_SRAM(256,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 256)
        if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                 `EL2_IC_TAG_SRAM(512,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 512)
        if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                 `EL2_IC_TAG_SRAM(1024,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 1024)
        if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                 `EL2_IC_TAG_SRAM(2048,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 2048)
        if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                 `EL2_IC_TAG_SRAM(4096,26,i)
        end // if (pt.ICACHE_TAG_DEPTH == 4096)
   end // block: WAYS
 end // block: PACKED_11

 else begin : PACKED_1
    if (pt.ICACHE_ECC) begin  : ECC1
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,104)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,52)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,104)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,52)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,104)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,52)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,104)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,52)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,104)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,52)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,104)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,52)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,104)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,52)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,104)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,52)
        end // block: WAYS
      end // block: size_4096
   end // block: ECC1

   else  begin : ECC0
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,88)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,44)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,88)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,44)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,88)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,44)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,44)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,44)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,44)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,44)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,44)
        end // block: WAYS
      end // block: size_4096
   end // block: ECC0
end // block: PACKED_1
// end ICACHE TAG

/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */

endmodule
