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
    import tb_top_pkg::*;
#(
    `include "css_mcu0_el2_param.vh"
) (
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
    bit          [31:0]         mem_mailbox         = 32'hD0580000;
`endif
    logic                       rst_l;
    logic                       porst_l;
    logic [pt.PIC_TOTAL_INT:1]  ext_int;
    logic                       nmi_int;
    logic                       timer_int;
    logic                       soft_int;

    logic        [31:0]         reset_vector;
    logic        [31:0]         nmi_vector;
    logic        [31:1]         jtag_id;

    logic        [31:0]         ic_haddr        ;
    logic        [2:0]          ic_hburst       ;
    logic                       ic_hmastlock    ;
    logic        [3:0]          ic_hprot        ;
    logic        [2:0]          ic_hsize        ;
    logic        [1:0]          ic_htrans       ;
    logic                       ic_hwrite       ;
    logic        [63:0]         ic_hrdata       ;
    logic                       ic_hready       ;
    logic                       ic_hresp        ;

    logic        [31:0]         lsu_haddr       ;
    logic        [2:0]          lsu_hburst      ;
    logic                       lsu_hmastlock   ;
    logic        [3:0]          lsu_hprot       ;
    logic        [2:0]          lsu_hsize       ;
    logic        [1:0]          lsu_htrans      ;
    logic                       lsu_hwrite      ;
    logic        [63:0]         lsu_hrdata      ;
    logic        [63:0]         lsu_hwdata      ;
    logic                       lsu_hready      ;
    logic                       lsu_hresp        ;

    logic        [31:0]         sb_haddr        ;
    logic        [2:0]          sb_hburst       ;
    logic                       sb_hmastlock    ;
    logic        [3:0]          sb_hprot        ;
    logic        [2:0]          sb_hsize        ;
    logic        [1:0]          sb_htrans       ;
    logic                       sb_hwrite       ;

    logic        [63:0]         sb_hrdata       ;
    logic        [63:0]         sb_hwdata       ;
    logic                       sb_hready       ;
    logic                       sb_hresp        ;

//    `ifdef I3C_USE_AHB
//        logic        [31:0]         i3c_haddr;
//        logic        [2:0]          i3c_hburst;
//        logic                       i3c_hmastlock;
//        logic        [3:0]          i3c_hprot;
//        logic        [2:0]          i3c_hsize;
//        logic        [1:0]          i3c_htrans;
//        logic                       i3c_hwrite;
//        logic        [63:0]         i3c_hrdata;
//        logic        [63:0]         i3c_hwdata;
//        logic                       i3c_hready;
//        logic                       i3c_hreadyout;
//        logic                       i3c_hresp;
//    `endif

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
    el2_mem_if                  caliptra_el2_mem_export ();        

    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_wr_fdata;
    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_fdout;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

    logic fuse_ctrl_rdy;
    
    tb_top_pkg::veer_sram_error_injection_mode_t error_injection_mode;

    `define MCU_DEC rvtop_wrapper.rvtop.veer.dec


    assign mailbox_write    = lmem.awvalid && (lmem.awaddr == mem_mailbox) && rst_l;
    assign mailbox_data     = lmem.wdata;

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
                    ext_int[mailbox_data[15:8]] <= 1'b0;
            end
            if (mailbox_data[7:0] == 8'h81) begin
                if (mailbox_data[15:8] > 0 && mailbox_data[15:8] < pt.PIC_TOTAL_INT)
                    ext_int[mailbox_data[15:8]] <= 1'b1;
            end
            if (mailbox_data[7:0] == 8'h82) begin
                nmi_int   <= nmi_int   & ~mailbox_data[8];
                timer_int <= timer_int & ~mailbox_data[9];
                soft_int  <= soft_int  & ~mailbox_data[10];
            end
            if (mailbox_data[7:0] == 8'h83) begin
                nmi_int   <= nmi_int   |  mailbox_data[8];
                timer_int <= timer_int |  mailbox_data[9];
                soft_int  <= soft_int  |  mailbox_data[10];
            end
        end
        if(mailbox_write && (mailbox_data[7:0] == 8'h90)) begin
            ext_int   <= {pt.PIC_TOTAL_INT-1{1'b0}};
            nmi_int   <= 1'b0;
            timer_int <= 1'b0;
            soft_int  <= 1'b0;
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
            caliptra_ss_top.gpr[0][`MCU_DEC.dec_nonblock_load_waddr] = `MCU_DEC.lsu_nonblock_load_data;
        end
        if(`MCU_DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h                ; nbD\n", cycleCnt, abi_reg[`MCU_DEC.div_waddr_wb], `MCU_DEC.exu_div_result);
            caliptra_ss_top.gpr[0][`MCU_DEC.div_waddr_wb] = `MCU_DEC.exu_div_result;
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

        ext_int     = {pt.PIC_TOTAL_INT-1{1'b0}};
        nmi_int     = 0;
        timer_int   = 0;
        soft_int    = 0;

    // tie offs
        jtag_id[31:28] = 4'b1;
        jtag_id[27:12] = '0;
        jtag_id[11:1]  = 11'h45;
        reset_vector = `css_mcu0_RV_RESET_VEC;
        nmi_vector   = 32'hee000000;

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
        forever  core_clk = #5 ~core_clk;
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
    logic                      cptra_jtag_tck;    // JTAG clk
    logic                      cptra_jtag_tms;    // JTAG TMS
    logic                      cptra_jtag_tdi;    // JTAG tdi
    logic                      cptra_jtag_trst_n; // JTAG Reset
    logic                      cptra_jtag_tdo;    // JTAG TDO
    logic                      cptra_jtag_tdoEn;  // JTAG TDO enable

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH - 3),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) m_axi_bfm_if (.clk(core_clk), .rst_n(cptra_rst_b));

    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) m_axi_if (.clk(core_clk), .rst_n(cptra_rst_b));

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) s_axi_if (.clk(core_clk), .rst_n(cptra_rst_b));

//        axi_if #(
//            .AW(AXI_SRAM_ADDR_WIDTH),
//            .DW(CPTRA_AXI_DMA_DATA_WIDTH),
//            .IW(CPTRA_AXI_DMA_ID_WIDTH + 3),
//            .UW(CPTRA_AXI_DMA_USER_WIDTH)
//        ) axi_sram_if (.clk(core_clk), .rst_n(cptra_rst_b));

    logic ready_for_fuses;
    logic ready_for_mb_processing;
    logic mailbox_data_avail;
    logic mbox_sram_cs;
    logic mbox_sram_we;
    logic [14:0] mbox_sram_addr;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    //device lifecycle
    security_state_t security_state;

    ras_test_ctrl_t ras_test_ctrl;
    logic [63:0] generic_input_wires;
    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

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
        .SKIP_BRINGUP(1),
        .SKIP_FUSE_CTRL(0)
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

        .generic_input_wires(generic_input_wires),

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

    //=========================================================================-
    // DUT instance
    //=========================================================================-
    caliptra_top caliptra_top_dut (
        .cptra_pwrgood              (cptra_pwrgood),
        .cptra_rst_b                (cptra_rst_b),
        .clk                        (core_clk),

        .cptra_obf_key              (cptra_obf_key     ),
        .cptra_csr_hmac_key         (cptra_csr_hmac_key),

        .jtag_tck   (cptra_jtag_tck   ),
        .jtag_tdi   (cptra_jtag_tdi   ),
        .jtag_tms   (cptra_jtag_tms   ),
        .jtag_trst_n(cptra_jtag_trst_n),
        .jtag_tdo   (cptra_jtag_tdo   ),
        .jtag_tdoEn (cptra_jtag_tdoEn ),
        
        //SoC AXI Interface
        .s_axi_w_if(s_axi_if.w_sub),
        .s_axi_r_if(s_axi_if.r_sub),

        //AXI DMA Interface
        .m_axi_w_if(m_axi_if.w_mgr),
        .m_axi_r_if(m_axi_if.r_mgr),

        .el2_mem_export(caliptra_el2_mem_export.veer_sram_src),

        .ready_for_fuses(ready_for_fuses),
        .ready_for_mb_processing(ready_for_mb_processing),
        .ready_for_runtime(),

        .mbox_sram_cs(mbox_sram_cs),
        .mbox_sram_we(mbox_sram_we),
        .mbox_sram_addr(mbox_sram_addr),
        .mbox_sram_wdata(mbox_sram_wdata),
        .mbox_sram_rdata(mbox_sram_rdata),
            
        .imem_cs(imem_cs),
        .imem_addr(imem_addr),
        .imem_rdata(imem_rdata),

        .mailbox_data_avail(mailbox_data_avail),
        .mailbox_flow_done(),
        .BootFSM_BrkPoint(BootFSM_BrkPoint),

        .recovery_data_avail(1'b1/*TODO*/),
        .recovery_image_activated(1'b0/*TODO*/),

        //SoC Interrupts
        .cptra_error_fatal    (cptra_error_fatal    ),
        .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
        .etrng_req             (etrng_req),
        .itrng_data            (itrng_data),
        .itrng_valid           (itrng_valid),
`else
        .etrng_req             (),
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
        .ss_dbg_manuf_enable(),
        .ss_soc_dbg_unlock_level(),

        // Subsystem mode firmware execution control
        .ss_generic_fw_exec_ctrl(),

        .generic_input_wires(generic_input_wires),
        .generic_output_wires(),

        .security_state(security_state),
        .scan_mode     (scan_mode)
    );


`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
    physical_rng physical_rng (
        .clk    (core_clk),
        .enable (etrng_req),
        .data   (itrng_data),
        .valid  (itrng_valid)
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
        .el2_mem_export (caliptra_el2_mem_export.veer_sram_sink),

        //SRAM interface for mbox
        .mbox_sram_cs   (mbox_sram_cs   ),
        .mbox_sram_we   (mbox_sram_we   ),
        .mbox_sram_addr (mbox_sram_addr ),
        .mbox_sram_wdata(mbox_sram_wdata),
        .mbox_sram_rdata(mbox_sram_rdata),

        //SRAM interface for imem
        .imem_cs   (imem_cs   ),
        .imem_addr (imem_addr ),
        .imem_rdata(imem_rdata),

        // Security State
        .security_state(security_state),

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

//        // Fake "MCU" SRAM block
//        caliptra_axi_sram #(
//            .AW(AXI_SRAM_ADDR_WIDTH),
//            .DW(CPTRA_AXI_DMA_DATA_WIDTH),
//            .UW(CPTRA_AXI_DMA_USER_WIDTH),
//            .IW(CPTRA_AXI_DMA_ID_WIDTH + 3),
//            .EX_EN(0)
//        ) i_axi_sram (
//            .clk(core_clk),
//            .rst_n(cptra_rst_b),
//
//            // AXI INF
//            .s_axi_w_if(axi_sram_if.w_sub),
//            .s_axi_r_if(axi_sram_if.r_sub)
//        );
//        `ifdef VERILATOR
//        initial i_axi_sram.i_sram.ram = '{default:'{default:8'h00}};
//        `else
//        initial i_axi_sram.i_sram.ram = '{default:8'h00};
//        `endif

    caliptra_top_sva sva();

    //=================== END CALIPTRA_TOP_TB ========================

    logic s_axi_if_rd_is_upper_dw_latched;
    logic s_axi_if_wr_is_upper_dw_latched;
    // AXI Interconnect connections
    assign s_axi_if.awvalid                      = axi_interconnect.sintf_arr[3].AWVALID;
    assign s_axi_if.awaddr                       = axi_interconnect.sintf_arr[3].AWADDR;
    assign s_axi_if.awid                         = axi_interconnect.sintf_arr[3].AWID;
    assign s_axi_if.awlen                        = axi_interconnect.sintf_arr[3].AWLEN;
    assign s_axi_if.awsize                       = axi_interconnect.sintf_arr[3].AWSIZE;
    assign s_axi_if.awburst                      = axi_interconnect.sintf_arr[3].AWBURST;
    assign s_axi_if.awlock                       = axi_interconnect.sintf_arr[3].AWLOCK;
    assign s_axi_if.awuser                       = axi_interconnect.sintf_arr[3].AWUSER;
    assign axi_interconnect.sintf_arr[3].AWREADY = s_axi_if.awready;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            s_axi_if_wr_is_upper_dw_latched <= 0;
        else if (s_axi_if.awvalid && s_axi_if.awready)
            s_axi_if_wr_is_upper_dw_latched <= s_axi_if.awaddr[2] && (s_axi_if.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT, (s_axi_if.awvalid && s_axi_if.awready) -> (s_axi_if.awsize < 3), core_clk, !rst_l)

    assign s_axi_if.wvalid                       = axi_interconnect.sintf_arr[3].WVALID;
    assign s_axi_if.wdata                        = axi_interconnect.sintf_arr[3].WDATA >> (s_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign s_axi_if.wstrb                        = axi_interconnect.sintf_arr[3].WSTRB >> (s_axi_if_wr_is_upper_dw_latched ? 4 : 0);
    assign s_axi_if.wlast                        = axi_interconnect.sintf_arr[3].WLAST;

    assign axi_interconnect.sintf_arr[3].WREADY  = s_axi_if.wready;

    assign axi_interconnect.sintf_arr[3].BVALID  = s_axi_if.bvalid;
    assign axi_interconnect.sintf_arr[3].BRESP   = s_axi_if.bresp;
    assign axi_interconnect.sintf_arr[3].BID     = s_axi_if.bid;
    assign s_axi_if.bready                       = axi_interconnect.sintf_arr[3].BREADY;

    assign s_axi_if.arvalid                      = axi_interconnect.sintf_arr[3].ARVALID;
    assign s_axi_if.araddr                       = axi_interconnect.sintf_arr[3].ARADDR;
    assign s_axi_if.arid                         = axi_interconnect.sintf_arr[3].ARID;
    assign s_axi_if.arlen                        = axi_interconnect.sintf_arr[3].ARLEN;
    assign s_axi_if.arsize                       = axi_interconnect.sintf_arr[3].ARSIZE;
    assign s_axi_if.arburst                      = axi_interconnect.sintf_arr[3].ARBURST;
    assign s_axi_if.arlock                       = axi_interconnect.sintf_arr[3].ARLOCK;
    assign s_axi_if.aruser                       = axi_interconnect.sintf_arr[3].ARUSER;
    assign axi_interconnect.sintf_arr[3].ARREADY = s_axi_if.arready;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            s_axi_if_rd_is_upper_dw_latched <= 0;
        else if (s_axi_if.arvalid && s_axi_if.arready)
            s_axi_if_rd_is_upper_dw_latched <= s_axi_if.araddr[2] && (s_axi_if.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT, (s_axi_if.arvalid && s_axi_if.arready) -> (s_axi_if.arsize < 3), core_clk, !rst_l)

    assign axi_interconnect.sintf_arr[3].RVALID  = s_axi_if.rvalid;
    assign axi_interconnect.sintf_arr[3].RDATA   = 64'(s_axi_if.rdata) << (s_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[3].RRESP   = s_axi_if.rresp;
    assign axi_interconnect.sintf_arr[3].RID     = s_axi_if.rid;
    assign axi_interconnect.sintf_arr[3].RLAST   = s_axi_if.rlast;
    assign s_axi_if.rready                       = axi_interconnect.sintf_arr[3].RREADY;

    // -- CALIPTRA SRAM 
//        // AXI Interconnect connections
//        assign axi_sram_if.awvalid                     = axi_interconnect.sintf_arr[4].AWVALID;
//        assign axi_sram_if.awaddr                      = axi_interconnect.sintf_arr[4].AWADDR;
//        assign axi_sram_if.awid                        = axi_interconnect.sintf_arr[4].AWID;
//        assign axi_sram_if.awlen                       = axi_interconnect.sintf_arr[4].AWLEN;
//        assign axi_sram_if.awsize                      = axi_interconnect.sintf_arr[4].AWSIZE;
//        assign axi_sram_if.awburst                     = axi_interconnect.sintf_arr[4].AWBURST;
//        assign axi_sram_if.awlock                      = axi_interconnect.sintf_arr[4].AWLOCK;
//        assign axi_sram_if.awuser                      = axi_interconnect.sintf_arr[4].AWUSER;
//        assign axi_interconnect.sintf_arr[4].AWREADY   = axi_sram_if.awready;
//
//        assign axi_sram_if.wvalid                      = axi_interconnect.sintf_arr[4].WVALID;
//        assign axi_sram_if.wdata                       = axi_interconnect.sintf_arr[4].WDATA;
//        assign axi_sram_if.wstrb                       = axi_interconnect.sintf_arr[4].WSTRB;
//        assign axi_sram_if.wlast                       = axi_interconnect.sintf_arr[4].WLAST;
//        assign axi_interconnect.sintf_arr[4].WREADY    = axi_sram_if.wready;
//
//        assign axi_interconnect.sintf_arr[4].BVALID    = axi_sram_if.bvalid;
//        assign axi_interconnect.sintf_arr[4].BRESP     = axi_sram_if.bresp;
//        assign axi_interconnect.sintf_arr[4].BID       = axi_sram_if.bid;
//        assign axi_sram_if.bready                      = axi_interconnect.sintf_arr[4].BREADY;
//
//        assign axi_sram_if.arvalid                     = axi_interconnect.sintf_arr[4].ARVALID;
//        assign axi_sram_if.araddr                      = axi_interconnect.sintf_arr[4].ARADDR;
//        assign axi_sram_if.arid                        = axi_interconnect.sintf_arr[4].ARID;
//        assign axi_sram_if.arlen                       = axi_interconnect.sintf_arr[4].ARLEN;
//        assign axi_sram_if.arsize                      = axi_interconnect.sintf_arr[4].ARSIZE;
//        assign axi_sram_if.arburst                     = axi_interconnect.sintf_arr[4].ARBURST;
//        assign axi_sram_if.arlock                      = axi_interconnect.sintf_arr[4].ARLOCK;
//        assign axi_sram_if.aruser                      = axi_interconnect.sintf_arr[4].ARUSER;
//        assign axi_interconnect.sintf_arr[4].ARREADY   = axi_sram_if.arready;
//
//        assign axi_interconnect.sintf_arr[4].RVALID    = axi_sram_if.rvalid;
//        assign axi_interconnect.sintf_arr[4].RDATA     = axi_sram_if.rdata;
//        assign axi_interconnect.sintf_arr[4].RRESP     = axi_sram_if.rresp;
//        assign axi_interconnect.sintf_arr[4].RID       = axi_sram_if.rid;
//        assign axi_interconnect.sintf_arr[4].RLAST     = axi_sram_if.rlast;
//        assign axi_sram_if.rready                      = axi_interconnect.sintf_arr[4].RREADY;
        


    // AXI Interconnect connections
    assign axi_interconnect.mintf_arr[2].AWVALID = '0;
    assign axi_interconnect.mintf_arr[2].AWADDR  = '0;
    assign axi_interconnect.mintf_arr[2].AWID    = '0;
    assign axi_interconnect.mintf_arr[2].AWLEN   = '0;
    assign axi_interconnect.mintf_arr[2].AWSIZE  = '0;
    assign axi_interconnect.mintf_arr[2].AWBURST = '0;
    assign axi_interconnect.mintf_arr[2].AWLOCK  = '0;
    assign axi_interconnect.mintf_arr[2].AWUSER  = '0;
//        assign something.awready    = axi_interconnect.mintf_arr[2].AWREADY;
    
    assign axi_interconnect.mintf_arr[2].WVALID = '0;
    assign axi_interconnect.mintf_arr[2].WDATA  = '0;
    assign axi_interconnect.mintf_arr[2].WSTRB  = '0;
    assign axi_interconnect.mintf_arr[2].WLAST  = '0;
//        assign something.wready    = axi_interconnect.mintf_arr[2].WREADY;
        
//        assign something.bvalid = axi_interconnect.mintf_arr[2].BVALID;
//        assign something.bresp  = axi_interconnect.mintf_arr[2].BRESP;
//        assign something.bid    = axi_interconnect.mintf_arr[2].BID;
    assign axi_interconnect.mintf_arr[2].BREADY = '0;

    assign axi_interconnect.mintf_arr[2].ARVALID = '0;
    assign axi_interconnect.mintf_arr[2].ARADDR  = '0;
    assign axi_interconnect.mintf_arr[2].ARID    = '0;
    assign axi_interconnect.mintf_arr[2].ARLEN   = '0;
    assign axi_interconnect.mintf_arr[2].ARSIZE  = '0;
    assign axi_interconnect.mintf_arr[2].ARBURST = '0;
    assign axi_interconnect.mintf_arr[2].ARLOCK  = '0;
    assign axi_interconnect.mintf_arr[2].ARUSER  = '0;
//        assign something.arready    = axi_interconnect.mintf_arr[2].ARREADY;
        
//        assign something.rvalid = axi_interconnect.mintf_arr[2].RVALID;
//        assign something.rdata  = axi_interconnect.mintf_arr[2].RDATA;
//        assign something.rresp  = axi_interconnect.mintf_arr[2].RRESP;
//        assign something.rid    = axi_interconnect.mintf_arr[2].RID;
//        assign something.rlast  = axi_interconnect.mintf_arr[2].RLAST;
    assign axi_interconnect.mintf_arr[2].RREADY = '0;

    // AXI Interconnect connections
    logic m_axi_if_rd_is_upper_dw_latched;
    logic m_axi_if_wr_is_upper_dw_latched;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            m_axi_if_wr_is_upper_dw_latched <= 0;
        else if (m_axi_if.awvalid && m_axi_if.awready)
            m_axi_if_wr_is_upper_dw_latched <= m_axi_if.awaddr[2] && (m_axi_if.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_DMA_WR_32BIT, (m_axi_if.awvalid && m_axi_if.awready) -> (m_axi_if.awsize < 3), core_clk, !rst_l)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            m_axi_if_rd_is_upper_dw_latched <= 0;
        else if (m_axi_if.arvalid && m_axi_if.arready)
            m_axi_if_rd_is_upper_dw_latched <= m_axi_if.araddr[2] && (m_axi_if.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_DMA_RD_32BIT, (m_axi_if.arvalid && m_axi_if.arready) -> (m_axi_if.arsize < 3), core_clk, !rst_l)
    
    // AXI Interconnect connections
    logic m_axi_bfm_if_rd_is_upper_dw_latched;
    logic m_axi_bfm_if_wr_is_upper_dw_latched;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            m_axi_bfm_if_wr_is_upper_dw_latched <= 0;
        else if (m_axi_bfm_if.awvalid && m_axi_bfm_if.awready)
            m_axi_bfm_if_wr_is_upper_dw_latched <= m_axi_bfm_if.awaddr[2] && (m_axi_bfm_if.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_DMA_WR_32BIT, (m_axi_bfm_if.awvalid && m_axi_bfm_if.awready) -> (m_axi_bfm_if.awsize < 3), core_clk, !rst_l)
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            m_axi_bfm_if_rd_is_upper_dw_latched <= 0;
        else if (m_axi_bfm_if.arvalid && m_axi_bfm_if.arready)
            m_axi_bfm_if_rd_is_upper_dw_latched <= m_axi_bfm_if.araddr[2] && (m_axi_bfm_if.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_DMA_RD_32BIT, (m_axi_bfm_if.arvalid && m_axi_bfm_if.arready) -> (m_axi_bfm_if.arsize < 3), core_clk, !rst_l)
    
    assign axi_interconnect.mintf_arr[3].AWVALID = m_axi_if.awvalid;
    assign axi_interconnect.mintf_arr[3].AWADDR  = m_axi_if.awaddr;
    assign axi_interconnect.mintf_arr[3].AWID    = m_axi_if.awid;
    assign axi_interconnect.mintf_arr[3].AWLEN   = m_axi_if.awlen;
    assign axi_interconnect.mintf_arr[3].AWSIZE  = m_axi_if.awsize;
    assign axi_interconnect.mintf_arr[3].AWBURST = m_axi_if.awburst;
    assign axi_interconnect.mintf_arr[3].AWLOCK  = m_axi_if.awlock;
    assign axi_interconnect.mintf_arr[3].AWUSER  = m_axi_if.awuser;
    assign m_axi_if.awready                      = axi_interconnect.mintf_arr[3].AWREADY;

    assign axi_interconnect.mintf_arr[3].WVALID  = m_axi_if.wvalid;
    assign axi_interconnect.mintf_arr[3].WDATA   = m_axi_if.wdata << (m_axi_if_wr_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.mintf_arr[3].WSTRB   = m_axi_if.wstrb << (m_axi_if_wr_is_upper_dw_latched ?  4 : 0);
    assign axi_interconnect.mintf_arr[3].WLAST   = m_axi_if.wlast;
    assign m_axi_if.wready                       = axi_interconnect.mintf_arr[3].WREADY;

    assign m_axi_if.bvalid                       = axi_interconnect.mintf_arr[3].BVALID;
    assign m_axi_if.bresp                        = axi_interconnect.mintf_arr[3].BRESP;
    assign m_axi_if.bid                          = axi_interconnect.mintf_arr[3].BID;
    assign axi_interconnect.mintf_arr[3].BREADY  = m_axi_if.bready;

    assign axi_interconnect.mintf_arr[3].ARVALID = m_axi_if.arvalid;
    assign axi_interconnect.mintf_arr[3].ARADDR  = m_axi_if.araddr;
    assign axi_interconnect.mintf_arr[3].ARID    = m_axi_if.arid;
    assign axi_interconnect.mintf_arr[3].ARLEN   = m_axi_if.arlen;
    assign axi_interconnect.mintf_arr[3].ARSIZE  = m_axi_if.arsize;
    assign axi_interconnect.mintf_arr[3].ARBURST = m_axi_if.arburst;
    assign axi_interconnect.mintf_arr[3].ARLOCK  = m_axi_if.arlock;
    assign axi_interconnect.mintf_arr[3].ARUSER  = m_axi_if.aruser;
    assign m_axi_if.arready                      = axi_interconnect.mintf_arr[3].ARREADY;

    assign m_axi_if.rvalid                       = axi_interconnect.mintf_arr[3].RVALID;
    assign m_axi_if.rdata                        = axi_interconnect.mintf_arr[3].RDATA >> (m_axi_if_rd_is_upper_dw_latched ? 32 : 0);
    assign m_axi_if.rresp                        = axi_interconnect.mintf_arr[3].RRESP;
    assign m_axi_if.rid                          = axi_interconnect.mintf_arr[3].RID;
    assign m_axi_if.rlast                        = axi_interconnect.mintf_arr[3].RLAST;
    assign axi_interconnect.mintf_arr[3].RREADY  = m_axi_if.rready;

    // AXI Interconnect connections
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

    logic [pt.LSU_BUS_TAG-1:0] fixme_lsu_axi_arid_req;
    logic [pt.LSU_BUS_TAG-1:0] fixme_lsu_axi_arid_req_r [pt.LSU_BUS_TAG];
    logic [pt.LSU_BUS_TAG-1:0] fixme_lsu_axi_awid_req;
    logic [pt.LSU_BUS_TAG-1:0] fixme_lsu_axi_awid_req_r [pt.LSU_BUS_TAG];
    assign axi_interconnect.mintf_arr[0].ARID[pt.LSU_BUS_TAG-1:0] = pt.LSU_BUS_TAG'(0);
    assign axi_interconnect.mintf_arr[0].AWID[pt.LSU_BUS_TAG-1:0] = pt.LSU_BUS_TAG'(0);
    //=========================================================================-
    // RTL instance
    //=========================================================================-
    mcu_top rvtop_wrapper (
        .rst_l                  ( rst_l         ),
        .dbg_rst_l              ( porst_l       ),
        .clk                    ( core_clk      ),
        .rst_vec                ( reset_vector[31:1]),
        .nmi_int                ( nmi_int       ),
        .nmi_vec                ( nmi_vector[31:1]),
        .jtag_id                ( jtag_id[31:1]),



        //-------------------------- LSU AXI signals--------------------------
        // // AXI Write Channels

        .lsu_axi_awvalid        (axi_interconnect.mintf_arr[0].AWVALID),
        .lsu_axi_awready        (axi_interconnect.mintf_arr[0].AWREADY),
        .lsu_axi_awid           (fixme_lsu_axi_awid_req), /*FIXME*/
        .lsu_axi_awaddr         (axi_interconnect.mintf_arr[0].AWADDR[31:0]),
        .lsu_axi_awregion       (axi_interconnect.mintf_arr[0].AWREGION),
        .lsu_axi_awlen          (axi_interconnect.mintf_arr[0].AWLEN),
        .lsu_axi_awsize         (axi_interconnect.mintf_arr[0].AWSIZE),
        .lsu_axi_awburst        (axi_interconnect.mintf_arr[0].AWBURST),
        .lsu_axi_awlock         (axi_interconnect.mintf_arr[0].AWLOCK[0]),
        .lsu_axi_awcache        (axi_interconnect.mintf_arr[0].AWCACHE),
        .lsu_axi_awprot         (axi_interconnect.mintf_arr[0].AWPROT),
        .lsu_axi_awqos          (axi_interconnect.mintf_arr[0].AWQOS),

        .lsu_axi_wvalid         (axi_interconnect.mintf_arr[0].WVALID),
        .lsu_axi_wready         (axi_interconnect.mintf_arr[0].WREADY),
        .lsu_axi_wdata          (axi_interconnect.mintf_arr[0].WDATA),
        .lsu_axi_wstrb          (axi_interconnect.mintf_arr[0].WSTRB),
        .lsu_axi_wlast          (axi_interconnect.mintf_arr[0].WLAST),

        .lsu_axi_bvalid         (axi_interconnect.mintf_arr[0].BVALID),
        .lsu_axi_bready         (axi_interconnect.mintf_arr[0].BREADY),
        .lsu_axi_bresp          (axi_interconnect.mintf_arr[0].BRESP),
        .lsu_axi_bid            (fixme_lsu_axi_awid_req_r[0]/*axi_interconnect.mintf_arr[0].BID[pt.LSU_BUS_TAG-1:0]*/), /*FIXME*/

        .lsu_axi_arvalid        (axi_interconnect.mintf_arr[0].ARVALID),
        .lsu_axi_arready        (axi_interconnect.mintf_arr[0].ARREADY),
        .lsu_axi_arid           (fixme_lsu_axi_arid_req), /*FIXME*/
        .lsu_axi_araddr         (axi_interconnect.mintf_arr[0].ARADDR[31:0]),
        .lsu_axi_arregion       (axi_interconnect.mintf_arr[0].ARREGION),
        .lsu_axi_arlen          (axi_interconnect.mintf_arr[0].ARLEN),
        .lsu_axi_arsize         (axi_interconnect.mintf_arr[0].ARSIZE),
        .lsu_axi_arburst        (axi_interconnect.mintf_arr[0].ARBURST),
        .lsu_axi_arlock         (axi_interconnect.mintf_arr[0].ARLOCK[0]),
        .lsu_axi_arcache        (axi_interconnect.mintf_arr[0].ARCACHE),
        .lsu_axi_arprot         (axi_interconnect.mintf_arr[0].ARPROT),
        .lsu_axi_arqos          (axi_interconnect.mintf_arr[0].ARQOS),

        .lsu_axi_rvalid         (axi_interconnect.mintf_arr[0].RVALID),
        .lsu_axi_rready         (axi_interconnect.mintf_arr[0].RREADY),
        .lsu_axi_rid            (fixme_lsu_axi_arid_req_r[0]/*axi_interconnect.mintf_arr[0].RID[pt.LSU_BUS_TAG-1:0]*/), /*FIXME*/
        .lsu_axi_rdata          (axi_interconnect.mintf_arr[0].RDATA),
        .lsu_axi_rresp          (axi_interconnect.mintf_arr[0].RRESP),
        .lsu_axi_rlast          (axi_interconnect.mintf_arr[0].RLAST),

        //-------------------------- IFU AXI signals--------------------------
        // AXI Write Channels

        .ifu_axi_awvalid        ( axi_interconnect.mintf_arr[1].AWVALID ),
        .ifu_axi_awready        ( axi_interconnect.mintf_arr[1].AWREADY ),
        .ifu_axi_awid           ( axi_interconnect.mintf_arr[1].AWID[pt.IFU_BUS_TAG-1:0]    ),
        .ifu_axi_awaddr         ( axi_interconnect.mintf_arr[1].AWADDR[31:0]  ),
        .ifu_axi_awregion       ( axi_interconnect.mintf_arr[1].AWREGION),
        .ifu_axi_awlen          ( axi_interconnect.mintf_arr[1].AWLEN   ),
        .ifu_axi_awsize         ( axi_interconnect.mintf_arr[1].AWSIZE  ),
        .ifu_axi_awburst        ( axi_interconnect.mintf_arr[1].AWBURST ),
        .ifu_axi_awlock         ( axi_interconnect.mintf_arr[1].AWLOCK[0]  ),
        .ifu_axi_awcache        ( axi_interconnect.mintf_arr[1].AWCACHE ),
        .ifu_axi_awprot         ( axi_interconnect.mintf_arr[1].AWPROT  ),
        .ifu_axi_awqos          ( axi_interconnect.mintf_arr[1].AWQOS   ),

        .ifu_axi_wvalid         ( axi_interconnect.mintf_arr[1].WVALID  ),
        .ifu_axi_wready         ( axi_interconnect.mintf_arr[1].WREADY  ),
        .ifu_axi_wdata          ( axi_interconnect.mintf_arr[1].WDATA   ),
        .ifu_axi_wstrb          ( axi_interconnect.mintf_arr[1].WSTRB   ),
        .ifu_axi_wlast          ( axi_interconnect.mintf_arr[1].WLAST   ),

        .ifu_axi_bvalid         ( axi_interconnect.mintf_arr[1].BVALID  ),
        .ifu_axi_bready         ( axi_interconnect.mintf_arr[1].BREADY  ),
        .ifu_axi_bresp          ( axi_interconnect.mintf_arr[1].BRESP   ),
        .ifu_axi_bid            ( axi_interconnect.mintf_arr[1].BID[pt.IFU_BUS_TAG-1:0]     ),

        .ifu_axi_arvalid        ( axi_interconnect.mintf_arr[1].ARVALID ),
        .ifu_axi_arready        ( axi_interconnect.mintf_arr[1].ARREADY ),
        .ifu_axi_arid           ( axi_interconnect.mintf_arr[1].ARID[pt.IFU_BUS_TAG-1:0]    ),
        .ifu_axi_araddr         ( axi_interconnect.mintf_arr[1].ARADDR[31:0]  ),
        .ifu_axi_arlen          ( axi_interconnect.mintf_arr[1].ARLEN   ),
        .ifu_axi_arsize         ( axi_interconnect.mintf_arr[1].ARSIZE  ),
        .ifu_axi_arburst        ( axi_interconnect.mintf_arr[1].ARBURST ),
        .ifu_axi_arlock         ( axi_interconnect.mintf_arr[1].ARLOCK[0]  ),
        .ifu_axi_arcache        ( axi_interconnect.mintf_arr[1].ARCACHE ),
        .ifu_axi_arprot         ( axi_interconnect.mintf_arr[1].ARPROT  ),
        .ifu_axi_arqos          ( axi_interconnect.mintf_arr[1].ARQOS   ),
        .ifu_axi_arregion       ( axi_interconnect.mintf_arr[1].ARREGION),

        .ifu_axi_rvalid         ( axi_interconnect.mintf_arr[1].RVALID  ),
        .ifu_axi_rready         ( axi_interconnect.mintf_arr[1].RREADY  ),
        .ifu_axi_rid            ( axi_interconnect.mintf_arr[1].RID[pt.IFU_BUS_TAG-1:0]     ),
        .ifu_axi_rdata          ( axi_interconnect.mintf_arr[1].RDATA   ),
        .ifu_axi_rresp          ( axi_interconnect.mintf_arr[1].RRESP   ),
        .ifu_axi_rlast          ( axi_interconnect.mintf_arr[1].RLAST   ),

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
        .dma_axi_awvalid        (axi_interconnect.sintf_arr[2].AWVALID),
        .dma_axi_awready        (axi_interconnect.sintf_arr[2].AWREADY),
        .dma_axi_awid           (axi_interconnect.sintf_arr[2].AWID[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_awaddr         (axi_interconnect.sintf_arr[2].AWADDR[31:0]),
        .dma_axi_awsize         (axi_interconnect.sintf_arr[2].AWSIZE),
        .dma_axi_awprot         (axi_interconnect.sintf_arr[2].AWPROT),
        .dma_axi_awlen          (axi_interconnect.sintf_arr[2].AWLEN),
        .dma_axi_awburst        (axi_interconnect.sintf_arr[2].AWBURST),

        .dma_axi_wvalid         (axi_interconnect.sintf_arr[2].WVALID),
        .dma_axi_wready         (axi_interconnect.sintf_arr[2].WREADY),
        .dma_axi_wdata          (axi_interconnect.sintf_arr[2].WDATA),
        .dma_axi_wstrb          (axi_interconnect.sintf_arr[2].WSTRB),
        .dma_axi_wlast          (axi_interconnect.sintf_arr[2].WLAST),

        .dma_axi_bvalid         (axi_interconnect.sintf_arr[2].BVALID),
        .dma_axi_bready         (axi_interconnect.sintf_arr[2].BREADY),
        .dma_axi_bresp          (axi_interconnect.sintf_arr[2].BRESP),
        .dma_axi_bid            (axi_interconnect.sintf_arr[2].BID[pt.DMA_BUS_TAG-1:0]),

        .dma_axi_arvalid        (axi_interconnect.sintf_arr[2].ARVALID),
        .dma_axi_arready        (axi_interconnect.sintf_arr[2].ARREADY),
        .dma_axi_arid           (axi_interconnect.sintf_arr[2].ARID[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_araddr         (axi_interconnect.sintf_arr[2].ARADDR[31:0]),
        .dma_axi_arsize         (axi_interconnect.sintf_arr[2].ARSIZE),
        .dma_axi_arprot         (axi_interconnect.sintf_arr[2].ARPROT),
        .dma_axi_arlen          (axi_interconnect.sintf_arr[2].ARLEN),
        .dma_axi_arburst        (axi_interconnect.sintf_arr[2].ARBURST),

        .dma_axi_rvalid         (axi_interconnect.sintf_arr[2].RVALID),
        .dma_axi_rready         (axi_interconnect.sintf_arr[2].RREADY),
        .dma_axi_rid            (axi_interconnect.sintf_arr[2].RID[pt.DMA_BUS_TAG-1:0]),
        .dma_axi_rdata          (axi_interconnect.sintf_arr[2].RDATA),
        .dma_axi_rresp          (axi_interconnect.sintf_arr[2].RRESP),
        .dma_axi_rlast          (axi_interconnect.sintf_arr[2].RLAST),

        .timer_int              ( timer_int ),
        .soft_int               ( soft_int ),
        .extintsrc_req          ( ext_int ),

        .lsu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .ifu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
        .dbg_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
        .dma_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

        .trace_rv_i_insn_ip     (trace_rv_i_insn_ip),
        .trace_rv_i_address_ip  (trace_rv_i_address_ip),
        .trace_rv_i_valid_ip    (trace_rv_i_valid_ip),
        .trace_rv_i_exception_ip(trace_rv_i_exception_ip),
        .trace_rv_i_ecause_ip   (trace_rv_i_ecause_ip),
        .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip),
        .trace_rv_i_tval_ip     (trace_rv_i_tval_ip),

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

        .iccm_ecc_single_error  (),
        .iccm_ecc_double_error  (),
        .dccm_ecc_single_error  (),
        .dccm_ecc_double_error  (),

    // remove mems DFT pins for opensource
        .ic_data_ext_in_pkt     ('0),
        .ic_tag_ext_in_pkt      ('0),

        .core_id                ('0),
        .scan_mode              ( 1'b0 ),         // To enable scan mode
        .mbist_mode             ( 1'b0 ),        // to enable mbist

        .dmi_uncore_enable      (),
        .dmi_uncore_en          (),
        .dmi_uncore_wr_en       (),
        .dmi_uncore_addr        (),
        .dmi_uncore_wdata       (),
        .dmi_uncore_rdata       ()

    );

    // assign axi_interconnect.mintf_arr[0].AWUSER                                              = 32'hFFFF_FFFF;
    // assign axi_interconnect.mintf_arr[0].ARUSER                                              = 32'hFFFF_FFFF;
    // assign axi_interconnect.mintf_arr[0].ARID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
    // assign axi_interconnect.mintf_arr[0].AWID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
    // assign axi_interconnect.mintf_arr[0].ARUSER[aaxi_pkg::AAXI_ARUSER_WIDTH-1:0]             = '1;
    // assign axi_interconnect.mintf_arr[0].AWUSER[aaxi_pkg::AAXI_AWUSER_WIDTH-1:0]             = '1;
    // assign axi_interconnect.mintf_arr[0].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    // assign axi_interconnect.mintf_arr[0].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    // assign axi_interconnect.mintf_arr[1].ARID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
    // assign axi_interconnect.mintf_arr[1].AWID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
    // assign axi_interconnect.mintf_arr[1].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    // assign axi_interconnect.mintf_arr[1].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    // assign axi_interconnect.sintf_arr[2].RID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
    // assign axi_interconnect.sintf_arr[2].BID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
    // assign axi_interconnect.sintf_arr[2].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    // assign axi_interconnect.sintf_arr[2].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    always_comb begin
        axi_interconnect.mintf_arr[0].AWUSER                                              = 32'hFFFF_FFFF;
        axi_interconnect.mintf_arr[0].ARUSER                                              = 32'hFFFF_FFFF;
        axi_interconnect.mintf_arr[0].ARID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
        axi_interconnect.mintf_arr[0].AWID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.LSU_BUS_TAG] = '0;
        axi_interconnect.mintf_arr[0].ARUSER[aaxi_pkg::AAXI_ARUSER_WIDTH-1:0]             = '1;
        axi_interconnect.mintf_arr[0].AWUSER[aaxi_pkg::AAXI_AWUSER_WIDTH-1:0]             = '1;
        axi_interconnect.mintf_arr[0].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        axi_interconnect.mintf_arr[0].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        axi_interconnect.mintf_arr[1].ARID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
        axi_interconnect.mintf_arr[1].AWID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.IFU_BUS_TAG] = '0;
        axi_interconnect.mintf_arr[1].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        axi_interconnect.mintf_arr[1].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        axi_interconnect.sintf_arr[2].RID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
        axi_interconnect.sintf_arr[2].BID[aaxi_pkg::AAXI_INTC_ID_WIDTH-1:pt.DMA_BUS_TAG]  = '0;
        axi_interconnect.sintf_arr[2].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
        axi_interconnect.sintf_arr[2].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]              = 32'h0;
    end
    

    // FIXME This hacky FIFO is to ensure the same AXI ID is used throughout a mailbox transfer.
    //       We need an ability to deterministically use the same AXI ID from the VeeR executable
    int ar_count;
    int aw_count;
    bit ar_hshake;
    bit r_hshake;
    bit aw_hshake;
    bit b_hshake;
    int r_ii, w_ii;
    always_comb begin
        ar_hshake = axi_interconnect.mintf_arr[0].ARVALID && axi_interconnect.mintf_arr[0].ARREADY;
        r_hshake  = axi_interconnect.mintf_arr[0].RVALID && axi_interconnect.mintf_arr[0].RREADY;
        aw_hshake = axi_interconnect.mintf_arr[0].AWVALID && axi_interconnect.mintf_arr[0].AWREADY;
        b_hshake  = axi_interconnect.mintf_arr[0].BVALID && axi_interconnect.mintf_arr[0].BREADY;
    end
    always_ff@(posedge core_clk or negedge rst_l) begin
        if (!rst_l) begin
            fixme_lsu_axi_arid_req_r <= '{default:0};
            fixme_lsu_axi_awid_req_r <= '{default:0};
            ar_count <= 0;
            aw_count <= 0;
        end
        else begin
            case ({ar_hshake,r_hshake}) inside
                2'b00: begin
                    fixme_lsu_axi_arid_req_r <= fixme_lsu_axi_arid_req_r;
                    ar_count <= ar_count;
                end
                2'b01: begin
                    `CALIPTRA_ASSERT(FIXME_R, ar_count > 0, core_clk, !rst_l)
                    for (r_ii = 0; r_ii < pt.LSU_BUS_TAG-1; r_ii++) begin
                        if (r_ii < ar_count-1)       fixme_lsu_axi_arid_req_r[r_ii] <= fixme_lsu_axi_arid_req_r[r_ii+1]; // Shift down
                        else if (r_ii >= ar_count-1) fixme_lsu_axi_arid_req_r[r_ii] <= '0;
                    end
                    if (ar_count == pt.LSU_BUS_TAG) fixme_lsu_axi_arid_req_r[pt.LSU_BUS_TAG-1] <= '0;
                    ar_count <= ar_count - 1;
                end
                2'b10: begin
                    for (r_ii = 0; r_ii < pt.LSU_BUS_TAG-1; r_ii++) begin
                        if (r_ii < ar_count)       fixme_lsu_axi_arid_req_r[r_ii] <= fixme_lsu_axi_arid_req_r[r_ii];
                        else if (r_ii == ar_count) fixme_lsu_axi_arid_req_r[r_ii] <= fixme_lsu_axi_arid_req;
                        else if (r_ii > ar_count)  fixme_lsu_axi_arid_req_r[r_ii] <= '0;
                    end
                    if (ar_count == pt.LSU_BUS_TAG-1) fixme_lsu_axi_arid_req_r[pt.LSU_BUS_TAG-1] <= fixme_lsu_axi_arid_req;
                    ar_count <= ar_count + 1;
                end
                2'b11: begin
                    `CALIPTRA_ASSERT(FIXME_AR, ar_count > 0, core_clk, !rst_l)
                    for (r_ii = 0; r_ii < pt.LSU_BUS_TAG-1; r_ii++) begin
                        if (r_ii < ar_count-1)       fixme_lsu_axi_arid_req_r[r_ii] <= fixme_lsu_axi_arid_req_r[r_ii+1]; // Shift down
                        else if (r_ii == ar_count-1) fixme_lsu_axi_arid_req_r[r_ii] <= fixme_lsu_axi_arid_req;
                        else if (r_ii >= ar_count)   fixme_lsu_axi_arid_req_r[r_ii] <= '0;
                    end
                    if (ar_count == pt.LSU_BUS_TAG) fixme_lsu_axi_arid_req_r[pt.LSU_BUS_TAG-1] <= fixme_lsu_axi_arid_req;
                    ar_count <= ar_count;
                end
            endcase
            case ({aw_hshake,b_hshake}) inside
                2'b00: begin
                    fixme_lsu_axi_awid_req_r <= fixme_lsu_axi_awid_req_r;
                    aw_count <= aw_count;
                end
                2'b01: begin
                    `CALIPTRA_ASSERT(FIXME_B, aw_count > 0, core_clk, !rst_l)
                    for (w_ii = 0; w_ii < pt.LSU_BUS_TAG-1; w_ii++) begin
                        if (w_ii < aw_count-1)       fixme_lsu_axi_awid_req_r[w_ii] <= fixme_lsu_axi_awid_req_r[w_ii+1]; // Shift down
                        else if (w_ii >= aw_count-1) fixme_lsu_axi_awid_req_r[w_ii] <= '0;
                    end
                    if (aw_count == pt.LSU_BUS_TAG) fixme_lsu_axi_awid_req_r[pt.LSU_BUS_TAG-1] <= '0;
                    aw_count <= aw_count - 1;
                end
                2'b10: begin
                    for (w_ii = 0; w_ii < pt.LSU_BUS_TAG-1; w_ii++) begin
                        if (w_ii < aw_count)       fixme_lsu_axi_awid_req_r[w_ii] <= fixme_lsu_axi_awid_req_r[w_ii];
                        else if (w_ii == aw_count) fixme_lsu_axi_awid_req_r[w_ii] <= fixme_lsu_axi_awid_req;
                        else if (w_ii > aw_count)  fixme_lsu_axi_awid_req_r[w_ii] <= '0;
                    end
                    if (aw_count == pt.LSU_BUS_TAG-1) fixme_lsu_axi_awid_req_r[pt.LSU_BUS_TAG-1] <= fixme_lsu_axi_awid_req;
                    aw_count <= aw_count + 1;
                end
                2'b11: begin
                    `CALIPTRA_ASSERT(FIXME_AW, aw_count > 0, core_clk, !rst_l)
                    for (w_ii = 0; w_ii < pt.LSU_BUS_TAG-1; w_ii++) begin
                        if (w_ii < aw_count-1)       fixme_lsu_axi_awid_req_r[w_ii] <= fixme_lsu_axi_awid_req_r[w_ii+1]; // Shift down
                        else if (w_ii == aw_count-1) fixme_lsu_axi_awid_req_r[w_ii] <= fixme_lsu_axi_awid_req;
                        else if (w_ii >= aw_count)   fixme_lsu_axi_awid_req_r[w_ii] <= '0;
                    end
                    if (aw_count == pt.LSU_BUS_TAG) fixme_lsu_axi_awid_req_r[pt.LSU_BUS_TAG-1] <= fixme_lsu_axi_awid_req;
                    aw_count <= aw_count;
                end
            endcase
        end
    end

    //=========================================================================-
    // I3C-Core Instance
    //=========================================================================-
    logic i3c_axi_rd_is_upper_dw_latched; // FIXME
    logic i3c_axi_wr_is_upper_dw_latched; // FIXME
    logic [31:0] i3c_axi_rdata_32; // FIXME
    logic [31:0] i3c_axi_wdata_32; // FIXME
    logic [3:0]  i3c_axi_wstrb_4; // FIXME

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
        .clk_i (core_clk),
        .rst_ni(rst_l   ),

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
        .arvalid_i  (axi_interconnect.sintf_arr[4].ARVALID),
        .arready_o  (axi_interconnect.sintf_arr[4].ARREADY),
        .arid_i     (axi_interconnect.sintf_arr[4].ARID),
        .araddr_i   (axi_interconnect.sintf_arr[4].ARADDR[`AXI_ADDR_WIDTH:0]),
        .arsize_i   (axi_interconnect.sintf_arr[4].ARSIZE),
        .aruser_i   (axi_interconnect.sintf_arr[4].ARUSER),
        .arlen_i    (axi_interconnect.sintf_arr[4].ARLEN),
        .arburst_i  (axi_interconnect.sintf_arr[4].ARBURST),
        .arlock_i   (axi_interconnect.sintf_arr[4].ARLOCK[0]),
        .rvalid_o   (axi_interconnect.sintf_arr[4].RVALID),
        .rready_i   (axi_interconnect.sintf_arr[4].RREADY),
        .rid_o      (axi_interconnect.sintf_arr[4].RID),
        .rdata_o    (i3c_axi_rdata_32),
        .rresp_o    (axi_interconnect.sintf_arr[4].RRESP),
        .rlast_o    (axi_interconnect.sintf_arr[4].RLAST),
        .awvalid_i  (axi_interconnect.sintf_arr[4].AWVALID),
        .awready_o  (axi_interconnect.sintf_arr[4].AWREADY),
        .awid_i     (axi_interconnect.sintf_arr[4].AWID),
        .awaddr_i   (axi_interconnect.sintf_arr[4].AWADDR[`AXI_ADDR_WIDTH:0]),
        .awsize_i   (axi_interconnect.sintf_arr[4].AWSIZE),
        .awuser_i   (axi_interconnect.sintf_arr[4].AWUSER),
        .awlen_i    (axi_interconnect.sintf_arr[4].AWLEN),
        .awburst_i  (axi_interconnect.sintf_arr[4].AWBURST),
        .awlock_i   (axi_interconnect.sintf_arr[4].AWLOCK[0]),
        .wvalid_i   (axi_interconnect.sintf_arr[4].WVALID),
        .wready_o   (axi_interconnect.sintf_arr[4].WREADY),
        .wdata_i    (i3c_axi_wdata_32),
        .wstrb_i    (i3c_axi_wstrb_4),
        .wlast_i    (axi_interconnect.sintf_arr[4].WLAST),
        .bvalid_o   (axi_interconnect.sintf_arr[4].BVALID),
        .bready_i   (axi_interconnect.sintf_arr[4].BREADY),
        .bresp_o    (axi_interconnect.sintf_arr[4].BRESP),
        .bid_o      (axi_interconnect.sintf_arr[4].BID),
`endif
`ifdef VERILATOR
        .scl_i(scl_i),
        .sda_i(sda_i),
        .scl_o(scl_o),
        .sda_o(sda_o),
        .sel_od_pp_o(sel_od_pp_o)
`else
        .i3c_scl_io(i3c_scl_io),
        .i3c_sda_io(i3c_sda_io)
`endif
    );

    // FIXME data width conversion hack
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            i3c_axi_wr_is_upper_dw_latched <= 0;
        else if (axi_interconnect.sintf_arr[4].AWVALID && axi_interconnect.sintf_arr[4].AWREADY)
            i3c_axi_wr_is_upper_dw_latched <= axi_interconnect.sintf_arr[4].AWADDR[2] && (axi_interconnect.sintf_arr[4].AWSIZE < 3);
    `CALIPTRA_ASSERT(I3C_AXI_WR_32BIT, (axi_interconnect.sintf_arr[4].AWVALID && axi_interconnect.sintf_arr[4].AWREADY) -> (axi_interconnect.sintf_arr[4].AWSIZE < 3), core_clk, !rst_l)
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            i3c_axi_rd_is_upper_dw_latched <= 0;
        else if (axi_interconnect.sintf_arr[4].ARVALID && axi_interconnect.sintf_arr[4].ARREADY)
            i3c_axi_rd_is_upper_dw_latched <= axi_interconnect.sintf_arr[4].ARADDR[2] && (axi_interconnect.sintf_arr[4].ARSIZE < 3);
    `CALIPTRA_ASSERT(I3C_AXI_RD_32BIT, (axi_interconnect.sintf_arr[4].ARVALID && axi_interconnect.sintf_arr[4].ARREADY) -> (axi_interconnect.sintf_arr[4].ARSIZE < 3), core_clk, !rst_l)
    assign axi_interconnect.sintf_arr[4].RDATA = 64'(i3c_axi_rdata_32) << (i3c_axi_rd_is_upper_dw_latched ? 32 : 0);
    assign i3c_axi_wdata_32                    = axi_interconnect.sintf_arr[4].WDATA >> (i3c_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign i3c_axi_wstrb_4                     = axi_interconnect.sintf_arr[4].WSTRB >> (i3c_axi_wr_is_upper_dw_latched ? 4  : 0);


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

    // defparam lmem.TAGW =`css_mcu0_RV_LSU_BUS_TAG;


    //=========================================================================-
    // AXI MEM instance : LMEM
    // Addtional 3 required for QVIP Interconnect
    // `css_mcu0_RV_LSU_BUS_TAG + 3
    //=========================================================================-
    //axi_slv #(.TAGW(`css_mcu0_RV_LSU_BUS_TAG)) lmem(

    axi_slv #(.TAGW(8)) lmem(
        .aclk(core_clk),
        .rst_l(rst_l),

        .arvalid        (axi_interconnect.sintf_arr[1].ARVALID),
        .arready        (axi_interconnect.sintf_arr[1].ARREADY),
        .araddr         (axi_interconnect.sintf_arr[1].ARADDR[31:0]),
        .arid           (axi_interconnect.sintf_arr[1].ARID),
        .arlen          (axi_interconnect.sintf_arr[1].ARLEN),
        .arburst        (axi_interconnect.sintf_arr[1].ARBURST),
        .arsize         (axi_interconnect.sintf_arr[1].ARSIZE),

        .rvalid         (axi_interconnect.sintf_arr[1].RVALID),
        .rready         (axi_interconnect.sintf_arr[1].RREADY),
        .rdata          (axi_interconnect.sintf_arr[1].RDATA),
        .rresp          (axi_interconnect.sintf_arr[1].RRESP),
        .rid            (axi_interconnect.sintf_arr[1].RID),
        .rlast          (axi_interconnect.sintf_arr[1].RLAST),

        .awvalid        (axi_interconnect.sintf_arr[1].AWVALID),
        .awready        (axi_interconnect.sintf_arr[1].AWREADY),
        .awaddr         (axi_interconnect.sintf_arr[1].AWADDR[31:0]),
        .awid           (axi_interconnect.sintf_arr[1].AWID),
        .awlen          (axi_interconnect.sintf_arr[1].AWLEN),
        .awburst        (axi_interconnect.sintf_arr[1].AWBURST),
        .awsize         (axi_interconnect.sintf_arr[1].AWSIZE),

        .wdata          (axi_interconnect.sintf_arr[1].WDATA),
        .wstrb          (axi_interconnect.sintf_arr[1].WSTRB),
        .wvalid         (axi_interconnect.sintf_arr[1].WVALID),
        .wready         (axi_interconnect.sintf_arr[1].WREADY),

        .bvalid         (axi_interconnect.sintf_arr[1].BVALID),
        .bready         (axi_interconnect.sintf_arr[1].BREADY),
        .bresp          (axi_interconnect.sintf_arr[1].BRESP),
        .bid            (axi_interconnect.sintf_arr[1].BID)

    );
    assign axi_interconnect.sintf_arr[1].ARADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;
    assign axi_interconnect.sintf_arr[1].AWADDR[aaxi_pkg::AAXI_ADDR_WIDTH-1:32]           = 32'h0;

    //=========================================================================-
    // Life-cycle Controller Instance : 
    // 
    //=========================================================================-

    logic caliptra_ss_lc_axi_rd_is_upper_dw_latched;
    logic caliptra_ss_lc_axi_wr_is_upper_dw_latched;

    axi_struct_pkg::axi_wr_req_t caliptra_ss_lc_axi_wr_req;
    axi_struct_pkg::axi_wr_rsp_t caliptra_ss_lc_axi_wr_rsp;
    axi_struct_pkg::axi_rd_req_t caliptra_ss_lc_axi_rd_req;
    axi_struct_pkg::axi_rd_rsp_t caliptra_ss_lc_axi_rd_rsp;

    assign caliptra_ss_lc_axi_wr_req.awvalid = axi_interconnect.sintf_arr[7].AWVALID;
    assign caliptra_ss_lc_axi_wr_req.awaddr = axi_interconnect.sintf_arr[7].AWADDR;
    assign caliptra_ss_lc_axi_wr_req.awid = axi_interconnect.sintf_arr[7].AWID;
    assign caliptra_ss_lc_axi_wr_req.awlen = axi_interconnect.sintf_arr[7].AWLEN;
    assign caliptra_ss_lc_axi_wr_req.awsize = axi_interconnect.sintf_arr[7].AWSIZE;
    assign caliptra_ss_lc_axi_wr_req.awburst = axi_interconnect.sintf_arr[7].AWBURST;
    assign caliptra_ss_lc_axi_wr_req.awlock = axi_interconnect.sintf_arr[7].AWLOCK;
    assign caliptra_ss_lc_axi_wr_req.awuser = axi_interconnect.sintf_arr[7].AWUSER;
    assign axi_interconnect.sintf_arr[7].AWREADY = caliptra_ss_lc_axi_wr_rsp.awready;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            caliptra_ss_lc_axi_wr_is_upper_dw_latched <= 0;
        else if (caliptra_ss_lc_axi_wr_req.awvalid && caliptra_ss_lc_axi_wr_rsp.awready)
            caliptra_ss_lc_axi_wr_is_upper_dw_latched <= caliptra_ss_lc_axi_wr_req.awaddr[2] && (caliptra_ss_lc_axi_wr_req.awsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_WR_32BIT, (caliptra_ss_lc_axi_wr_req.awvalid && caliptra_ss_lc_axi_wr_rsp.awready) -> (caliptra_ss_lc_axi_wr_req.awsize < 3), core_clk, !rst_l)


    assign caliptra_ss_lc_axi_wr_req.wvalid = axi_interconnect.sintf_arr[7].WVALID;
    assign caliptra_ss_lc_axi_wr_req.wdata = axi_interconnect.sintf_arr[7].WDATA >> (caliptra_ss_lc_axi_wr_is_upper_dw_latched ? 32 : 0);
    assign caliptra_ss_lc_axi_wr_req.wstrb = axi_interconnect.sintf_arr[7].WSTRB >> (caliptra_ss_lc_axi_wr_is_upper_dw_latched ? 4 : 0);
    assign caliptra_ss_lc_axi_wr_req.wlast = axi_interconnect.sintf_arr[7].WLAST;

    assign axi_interconnect.sintf_arr[7].WREADY = caliptra_ss_lc_axi_wr_rsp.wready;

    assign axi_interconnect.sintf_arr[7].BRESP = caliptra_ss_lc_axi_wr_rsp.bresp;
    assign axi_interconnect.sintf_arr[7].BID = caliptra_ss_lc_axi_wr_rsp.bid;
    assign axi_interconnect.sintf_arr[7].BVALID = caliptra_ss_lc_axi_wr_rsp.bvalid;
    assign caliptra_ss_lc_axi_wr_req.bready = axi_interconnect.sintf_arr[7].BREADY;

    assign caliptra_ss_lc_axi_rd_req.arvalid = axi_interconnect.sintf_arr[7].ARVALID;
    assign caliptra_ss_lc_axi_rd_req.araddr = axi_interconnect.sintf_arr[7].ARADDR;
    assign caliptra_ss_lc_axi_rd_req.arid = axi_interconnect.sintf_arr[7].ARID;
    assign caliptra_ss_lc_axi_rd_req.arlen = axi_interconnect.sintf_arr[7].ARLEN;
    assign caliptra_ss_lc_axi_rd_req.arsize = axi_interconnect.sintf_arr[7].ARSIZE;
    assign caliptra_ss_lc_axi_rd_req.arburst = axi_interconnect.sintf_arr[7].ARBURST;
    assign caliptra_ss_lc_axi_rd_req.arlock = axi_interconnect.sintf_arr[7].ARLOCK;
    assign caliptra_ss_lc_axi_rd_req.aruser = axi_interconnect.sintf_arr[7].ARUSER;
    assign axi_interconnect.sintf_arr[7].ARREADY = caliptra_ss_lc_axi_rd_rsp.arready;
    // FIXME this is a gross hack for data width conversion
    always@(posedge core_clk or negedge rst_l)
        if (!rst_l)
            caliptra_ss_lc_axi_rd_is_upper_dw_latched <= 0;
        else if (caliptra_ss_lc_axi_rd_req.arvalid && caliptra_ss_lc_axi_rd_rsp.arready)
            caliptra_ss_lc_axi_rd_is_upper_dw_latched <= caliptra_ss_lc_axi_rd_req.araddr[2] && (caliptra_ss_lc_axi_rd_req.arsize < 3);
    `CALIPTRA_ASSERT(CPTRA_AXI_RD_32BIT, (caliptra_ss_lc_axi_rd_req.arvalid && caliptra_ss_lc_axi_rd_rsp.arready) -> (caliptra_ss_lc_axi_rd_req.arsize < 3), core_clk, !rst_l)

    assign axi_interconnect.sintf_arr[7].RDATA = 64'(caliptra_ss_lc_axi_rd_rsp.rdata) << (caliptra_ss_lc_axi_rd_is_upper_dw_latched ? 32 : 0);
    assign axi_interconnect.sintf_arr[7].RRESP = caliptra_ss_lc_axi_rd_rsp.rresp;
    assign axi_interconnect.sintf_arr[7].RID = caliptra_ss_lc_axi_rd_rsp.rid;
    assign axi_interconnect.sintf_arr[7].RLAST = caliptra_ss_lc_axi_rd_rsp.rlast;
    assign axi_interconnect.sintf_arr[7].RVALID = caliptra_ss_lc_axi_rd_rsp.rvalid;
    assign caliptra_ss_lc_axi_rd_req.rready = axi_interconnect.sintf_arr[7].RREADY;


    //--------------------------------------------------------------------------------------------
    // These are alert handler signals. We do not want them for the initial integrations
    // TL-UL Interface
    logic [$bits(tlul_pkg::tl_h2d_t)-1:0] caliptra_ss_lc_ctrl_dmi_tl_h2d_tb;
    logic [$bits(tlul_pkg::tl_d2h_t)-1:0] caliptra_ss_lc_ctrl_dmi_tl_d2h_tb;
    assign caliptra_ss_lc_ctrl_dmi_tl_d2h_tb = tlul_pkg::tl_d2h_t'(u_caliptra_ss_lc_ctrl.dmi_tl_o);
    assign caliptra_ss_lc_ctrl_dmi_tl_h2d_tb = tlul_pkg::tl_h2d_t'(u_caliptra_ss_lc_ctrl_bfm.caliptra_ss_lc_ctrl_dmi_tl_h2d);

    // Scan Interface
    logic caliptra_ss_lc_ctrl_scan_rst_ni_tb;
    logic [$bits(caliptra_prim_mubi_pkg::mubi4_t)-1:0] caliptra_ss_lc_ctrl_scanmode_i_tb;
    assign caliptra_ss_lc_ctrl_scanmode_i_tb = caliptra_prim_mubi_pkg::mubi4_t'(u_caliptra_ss_lc_ctrl_bfm.caliptra_ss_lc_ctrl_scanmode_i);

    // Alert Handler Interface
    logic [$bits(caliptra_prim_alert_pkg::alert_rx_t)-1:0] [caliptra_ss_lc_ctrl_reg_pkg::NumAlerts-1:0] caliptra_ss_lc_ctrl_alert_rx_tb;
    assign caliptra_ss_lc_ctrl_alert_rx_tb = caliptra_prim_alert_pkg::alert_rx_t'(u_caliptra_ss_lc_ctrl_bfm.caliptra_ss_lc_ctrl_alert_rx);
    logic [$bits(caliptra_prim_alert_pkg::alert_tx_t)-1:0] [caliptra_ss_lc_ctrl_reg_pkg::NumAlerts-1:0] caliptra_ss_lc_ctrl_alert_tx_tb;
    assign caliptra_ss_lc_ctrl_alert_tx_tb = caliptra_prim_alert_pkg::alert_tx_t'(u_caliptra_ss_lc_ctrl.alert_tx_o);
    
    // Escape State Interface
    logic [$bits(caliptra_prim_esc_pkg::esc_rx_t)-1:0] esc_scrap_state0_tx_tb;
    logic [$bits(caliptra_prim_esc_pkg::esc_tx_t)-1:0] esc_scrap_state0_rx_tb;
    logic [$bits(caliptra_prim_esc_pkg::esc_rx_t)-1:0] esc_scrap_state1_tx_tb;
    logic [$bits(caliptra_prim_esc_pkg::esc_tx_t)-1:0] esc_scrap_state1_rx_tb;

    assign esc_scrap_state0_tx_tb = caliptra_prim_esc_pkg::esc_rx_t'(u_caliptra_ss_lc_ctrl_bfm.esc_scrap_state0_tx_i);
    assign esc_scrap_state0_rx_tb = caliptra_prim_esc_pkg::esc_tx_t'(u_caliptra_ss_lc_ctrl.esc_scrap_state0_rx_o);
    assign esc_scrap_state1_tx_tb = caliptra_prim_esc_pkg::esc_rx_t'(u_caliptra_ss_lc_ctrl_bfm.esc_scrap_state1_tx_i);
    assign esc_scrap_state1_rx_tb = caliptra_prim_esc_pkg::esc_tx_t'(u_caliptra_ss_lc_ctrl.esc_scrap_state1_rx_o);
    //--------------------------------------------------------------------------------------------


    //--------------------------------------------------------------------------------------------
    // These are shared signals between fuse controller and lc controller
    logic [$bits(otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_req_t)-1:0] caliptra_ss_lc_otp_vendor_test_o_tb;
    logic [$bits(otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_rsp_t)-1:0] caliptra_ss_lc_otp_vendor_test_i_tb;
    logic [$bits(otp_ctrl_pkg::caliptra_ss_lc_otp_program_req_t)-1:0] caliptra_ss_lc_otp_program_o_tb;
    logic [$bits(otp_ctrl_pkg::caliptra_ss_lc_otp_program_rsp_t)-1:0] caliptra_ss_lc_otp_program_i_tb;

    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_creator_seed_sw_rw_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_owner_seed_sw_rw_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_seed_hw_rd_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_dft_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_escalate_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_check_byp_en_tb;
    logic [$bits(otp_ctrl_pkg::otp_caliptra_ss_lc_data_t)-1:0] otp_caliptra_ss_lc_data_tb;

    assign caliptra_ss_lc_otp_vendor_test_o_tb = otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_req_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_otp_vendor_test_o);
    assign caliptra_ss_lc_otp_vendor_test_i_tb = otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_rsp_t'(u_otp_ctrl.caliptra_ss_lc_otp_vendor_test_o);


    assign caliptra_ss_lc_otp_program_o_tb = otp_ctrl_pkg::caliptra_ss_lc_otp_program_req_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_otp_program_o);
    assign caliptra_ss_lc_otp_program_i_tb = otp_ctrl_pkg::caliptra_ss_lc_otp_program_rsp_t'(u_otp_ctrl.caliptra_ss_lc_otp_program_o);

    assign caliptra_ss_lc_creator_seed_sw_rw_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_creator_seed_sw_rw_en_o);
    assign caliptra_ss_lc_owner_seed_sw_rw_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_owner_seed_sw_rw_en_o);
    assign caliptra_ss_lc_seed_hw_rd_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_seed_hw_rd_en_o);
    assign caliptra_ss_lc_dft_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_dft_en_o);
    assign caliptra_ss_lc_escalate_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_escalate_en_o);
    assign caliptra_ss_lc_check_byp_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_check_byp_en_o);

    // TODO: This port is hacked in LCC's BFM in order to have provisioned tokens
    //assign otp_caliptra_ss_lc_data_tb = otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(u_otp_ctrl.otp_caliptra_ss_lc_data_o);
    assign otp_caliptra_ss_lc_data_tb = otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(u_caliptra_ss_lc_ctrl_bfm.otp_caliptra_ss_lc_data_o);

    //--------------------------------------------------------------------------------------------

    //--------------------------------------------------------------------------------------------
    // These are going to be connected to SoC later on
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_nvm_debug_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_hw_debug_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_cpu_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_iso_part_sw_rd_en_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_iso_part_sw_wr_en_tb;
    // Assignments for unused signals
    assign caliptra_ss_lc_nvm_debug_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_nvm_debug_en_o);
    assign caliptra_ss_lc_hw_debug_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_hw_debug_en_o);
    assign caliptra_ss_lc_cpu_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_cpu_en_o);
    assign caliptra_ss_lc_iso_part_sw_rd_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_iso_part_sw_rd_en_o);
    assign caliptra_ss_lc_iso_part_sw_wr_en_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_iso_part_sw_wr_en_o);
    //--------------------------------------------------------------------------------------------

    //--------------------------------------------------------------------------------------------
    // These are driven by the lc ctrl bfm
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_clk_byp_req_tb;
    logic [$bits(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t)-1:0] caliptra_ss_lc_clk_byp_ack_tb;
    assign caliptra_ss_lc_clk_byp_req_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_clk_byp_req_o);
    assign caliptra_ss_lc_clk_byp_ack_tb = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl_bfm.caliptra_ss_lc_clk_byp_ack_i);

    logic [$bits(pwrmgr_pkg::pwr_caliptra_ss_lc_req_t)-1:0] pwr_caliptra_ss_lc_i_tb;
    logic [$bits(pwrmgr_pkg::pwr_caliptra_ss_lc_rsp_t)-1:0] pwr_caliptra_ss_lc_o_tb;
    // Assignments for Power Manager Interface
    assign pwr_caliptra_ss_lc_i_tb = pwrmgr_pkg::pwr_caliptra_ss_lc_req_t'(u_caliptra_ss_lc_ctrl_bfm.pwr_caliptra_ss_lc_i);
    assign pwr_caliptra_ss_lc_o_tb = pwrmgr_pkg::pwr_caliptra_ss_lc_rsp_t'(u_caliptra_ss_lc_ctrl.pwr_caliptra_ss_lc_o);
    logic pwr_otp_init_i;



    logic [7:0] caliptra_ss_lc_flash_rma_ack_tb;
    logic [7:0] from_bfm_caliptra_ss_lc_flash_rma_ack;
    assign caliptra_ss_lc_flash_rma_ack_tb = from_bfm_caliptra_ss_lc_flash_rma_ack;

    logic RMA_strap;
    logic fake_reset;

    logic [3:0]  to_bfm_caliptra_ss_lc_flash_rma_req_o;
    assign to_bfm_caliptra_ss_lc_flash_rma_req_o = caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(u_caliptra_ss_lc_ctrl.caliptra_ss_lc_flash_rma_req_o);

    

    caliptra_ss_lc_ctrl_bfm u_caliptra_ss_lc_ctrl_bfm (
        .clk(core_clk),
        .reset_n(rst_l),


        .caliptra_ss_lc_axi_rd_req(caliptra_ss_lc_axi_rd_req),
        .caliptra_ss_lc_axi_rd_rsp(caliptra_ss_lc_axi_rd_rsp),
        .fake_reset(fake_reset),
        .RMA_strap(RMA_strap),
        .from_bfm_caliptra_ss_lc_flash_rma_ack(from_bfm_caliptra_ss_lc_flash_rma_ack),
        .to_bfm_caliptra_ss_lc_flash_rma_req_o(to_bfm_caliptra_ss_lc_flash_rma_req_o),

        // TL-UL Interface
        .caliptra_ss_lc_ctrl_dmi_tl_h2d(),
        .caliptra_ss_lc_ctrl_dmi_tl_d2h(tlul_pkg::tl_d2h_t'(caliptra_ss_lc_ctrl_dmi_tl_d2h_tb)),

        // Scan Interface
        .caliptra_ss_lc_ctrl_scan_rst_ni(caliptra_ss_lc_ctrl_scan_rst_ni_tb),
        .caliptra_ss_lc_ctrl_scanmode_i(),

        // Alert Handler Interface
        .caliptra_ss_lc_ctrl_alert_rx(),
        .caliptra_ss_lc_ctrl_alert_tx(caliptra_prim_alert_pkg::alert_tx_t'(caliptra_ss_lc_ctrl_alert_tx_tb)),

        // OTP hack
        .otp_caliptra_ss_lc_data_o(),
        .from_otp_caliptra_ss_lc_data_i(otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(u_otp_ctrl.otp_caliptra_ss_lc_data_o)),

        // Escape State Interface
        .esc_scrap_state0_tx_i(),
        .esc_scrap_state0_rx_o(caliptra_prim_esc_pkg::esc_tx_t'(esc_scrap_state0_rx_tb)),
        .esc_scrap_state1_tx_i(),
        .esc_scrap_state1_rx_o(caliptra_prim_esc_pkg::esc_tx_t'(esc_scrap_state1_rx_tb)),

        // Power manager interface
        .pwr_caliptra_ss_lc_i(),
        .pwr_caliptra_ss_lc_o(pwrmgr_pkg::pwr_caliptra_ss_lc_rsp_t'(pwr_caliptra_ss_lc_o_tb)),
        .cptra_pwrgood(cptra_pwrgood),

        // Clock manager interface
        .caliptra_ss_lc_clk_byp_req_o(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_clk_byp_req_tb)),
        .caliptra_ss_lc_clk_byp_ack_i()
    );

    //--------------------------------------------------------------------------------------------



    caliptra_ss_lc_ctrl /*#(
            .AlertAsyncOn(AlertAsyncOn),
            .SiliconCreatorId(SiliconCreatorId),
            .ProductId(ProductId),
            .RevisionId(RevisionId),
            .IdcodeValue(IdcodeValue),
            .UseDmiInterface(UseDmiInterface),
            .RndCnstLcKeymgrDivInvalid(RndCnstLcKeymgrDivInvalid),
            .RndCnstLcKeymgrDivTestUnlocked(RndCnstLcKeymgrDivTestUnlocked),
            .RndCnstLcKeymgrDivDev(RndCnstLcKeymgrDivDev),
            .RndCnstLcKeymgrDivProduction(RndCnstLcKeymgrDivProduction),
            .RndCnstLcKeymgrDivRma(RndCnstLcKeymgrDivRma),
            .RndCnstInvalidTokens(RndCnstInvalidTokens),
            .SecVolatileRawUnlockEn(SecVolatileRawUnlockEn)
        ) */ u_caliptra_ss_lc_ctrl (
            .clk_i(core_clk),
            .rst_ni(rst_l & fake_reset),
            .RMA_strap(RMA_strap),
            .axi_wr_req(caliptra_ss_lc_axi_wr_req),
            .axi_wr_rsp(caliptra_ss_lc_axi_wr_rsp),
            .axi_rd_req(caliptra_ss_lc_axi_rd_req),
            .axi_rd_rsp(caliptra_ss_lc_axi_rd_rsp),

            .dmi_tl_i(tlul_pkg::tl_h2d_t'(caliptra_ss_lc_ctrl_dmi_tl_h2d_tb)),
            .dmi_tl_o(),
            .jtag_i('0),
            .jtag_o(),
            
            .scan_rst_ni(caliptra_ss_lc_ctrl_scan_rst_ni_tb),
            .scanmode_i(caliptra_prim_mubi_pkg::mubi4_t'(caliptra_ss_lc_ctrl_scanmode_i_tb)),

            // Alert Handler Interface
            .alert_rx_i(caliptra_prim_alert_pkg::alert_rx_t'(caliptra_ss_lc_ctrl_alert_rx_tb)),
            .alert_tx_o(),
            .esc_scrap_state0_tx_i(caliptra_prim_esc_pkg::esc_rx_t'(esc_scrap_state0_tx_tb)),
            .esc_scrap_state0_rx_o(),
            .esc_scrap_state1_tx_i(caliptra_prim_esc_pkg::esc_rx_t'(esc_scrap_state1_tx_tb)),
            .esc_scrap_state1_rx_o(),


            .pwr_caliptra_ss_lc_i(pwrmgr_pkg::pwr_caliptra_ss_lc_req_t'(pwr_caliptra_ss_lc_i_tb)),
            .pwr_caliptra_ss_lc_o(),


            .strap_en_override_o(),

            .caliptra_ss_lc_otp_vendor_test_o(),
            .caliptra_ss_lc_otp_vendor_test_i(otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_rsp_t'(caliptra_ss_lc_otp_vendor_test_i_tb)),
            .caliptra_ss_lc_otp_program_o(),
            .caliptra_ss_lc_otp_program_i(otp_ctrl_pkg::caliptra_ss_lc_otp_program_rsp_t'(caliptra_ss_lc_otp_program_i_tb)),

            .otp_caliptra_ss_lc_data_i(otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(otp_caliptra_ss_lc_data_tb)),
            .caliptra_ss_lc_dft_en_o(),
            .caliptra_ss_lc_creator_seed_sw_rw_en_o(),
            .caliptra_ss_lc_owner_seed_sw_rw_en_o(),
            .caliptra_ss_lc_seed_hw_rd_en_o(),            
            .caliptra_ss_lc_escalate_en_o(),
            .caliptra_ss_lc_check_byp_en_o(),



            .caliptra_ss_lc_nvm_debug_en_o(),
            .caliptra_ss_lc_hw_debug_en_o(),
            .caliptra_ss_lc_cpu_en_o(),
            .caliptra_ss_lc_iso_part_sw_rd_en_o(),
            .caliptra_ss_lc_iso_part_sw_wr_en_o(),



            .caliptra_ss_lc_keymgr_en_o(), // We do not use key manager
            .caliptra_ss_lc_clk_byp_req_o(),
            // .caliptra_ss_lc_clk_byp_ack_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_clk_byp_ack_tb)),
            .caliptra_ss_lc_clk_byp_ack_i(caliptra_ss_lc_clk_byp_ack_tb),
            .caliptra_ss_lc_flash_rma_seed_o(), // We do not use flash
            .caliptra_ss_lc_flash_rma_req_o(),
            .caliptra_ss_lc_flash_rma_ack_i(caliptra_ss_lc_flash_rma_ack_tb),
            .caliptra_ss_lc_keymgr_div_o(), // We do not use key manager
            .otp_device_id_i('0),
            .otp_manuf_state_i('0),
            .hw_rev_o()
        );


    //=========================================================================-
    // Fuse Controller Instance : 
    // 
    //=========================================================================-
    
    // logic otp_caliptra_ss_lc_data_o_valid;
    

    axi_struct_pkg::axi_wr_req_t core_axi_wr_req;
    axi_struct_pkg::axi_wr_rsp_t core_axi_wr_rsp;
    axi_struct_pkg::axi_rd_req_t core_axi_rd_req;
    axi_struct_pkg::axi_rd_rsp_t core_axi_rd_rsp;

    axi_struct_pkg::axi_wr_req_t prim_axi_wr_req;
    axi_struct_pkg::axi_wr_rsp_t prim_axi_wr_rsp;
    axi_struct_pkg::axi_rd_req_t prim_axi_rd_req;
    axi_struct_pkg::axi_rd_rsp_t prim_axi_rd_rsp;

    caliptra_prim_mubi_pkg::mubi4_t scanmode_mubi;
    
    otp_ctrl #(
        .MemInitFile ("/home/ws/caliptra/anjpar/caliptra_ws_1119/Caliptra/../chipsalliance/caliptra-ss/src/fuse_ctrl/data/otp-img.2048.vmem")
    ) u_otp_ctrl (
        .clk_i                      (core_clk),
        .rst_ni                     (rst_l & fake_reset),
        .clk_edn_i                  (),
        .rst_edn_ni                 (),
        .edn_o                      (),
        .edn_i                      (),

        .core_axi_wr_req            (core_axi_wr_req),
        .core_axi_wr_rsp            (core_axi_wr_rsp),
        .core_axi_rd_req            (core_axi_rd_req),
        .core_axi_rd_rsp            (core_axi_rd_rsp),
        
        .prim_axi_wr_req            (prim_axi_wr_req),
        .prim_axi_wr_rsp            (prim_axi_wr_rsp),
        .prim_axi_rd_req            (prim_axi_rd_req),
        .prim_axi_rd_rsp            (prim_axi_rd_rsp),

        .intr_otp_operation_done_o  (),
        .intr_otp_error_o           (),
        .alert_rx_i                 (),
        .alert_tx_o                 (),
        .obs_ctrl_i                 (),
        .otp_obs_o                  (),
        .otp_ast_pwr_seq_o          (),
        .otp_ast_pwr_seq_h_i        (),
        .pwr_otp_i                  (pwr_otp_init_i),
        .pwr_otp_o                  (),

        .caliptra_ss_lc_otp_vendor_test_i(otp_ctrl_pkg::caliptra_ss_lc_otp_vendor_test_req_t'(caliptra_ss_lc_otp_vendor_test_o_tb)),
        .caliptra_ss_lc_otp_vendor_test_o(),
        .caliptra_ss_lc_otp_program_i(otp_ctrl_pkg::caliptra_ss_lc_otp_program_req_t'(caliptra_ss_lc_otp_program_o_tb)),
        .caliptra_ss_lc_otp_program_o(),



    // .caliptra_ss_lc_creator_seed_sw_rw_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_creator_seed_sw_rw_en_tb)),
    // .caliptra_ss_lc_owner_seed_sw_rw_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_owner_seed_sw_rw_en_tb)),
    // .caliptra_ss_lc_seed_hw_rd_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_seed_hw_rd_en_tb)),
    // .caliptra_ss_lc_dft_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_dft_en_tb)),
    // .caliptra_ss_lc_escalate_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_escalate_en_tb)),
    // .caliptra_ss_lc_check_byp_en_i(caliptra_ss_lc_ctrl_pkg::caliptra_ss_lc_tx_t'(caliptra_ss_lc_check_byp_en_tb)),
    // .otp_caliptra_ss_lc_data_o(otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(otp_caliptra_ss_lc_data_tb)),
    

    .caliptra_ss_lc_creator_seed_sw_rw_en_i(caliptra_ss_lc_creator_seed_sw_rw_en_tb),
    .caliptra_ss_lc_owner_seed_sw_rw_en_i(caliptra_ss_lc_owner_seed_sw_rw_en_tb),
    .caliptra_ss_lc_seed_hw_rd_en_i(caliptra_ss_lc_seed_hw_rd_en_tb),
    .caliptra_ss_lc_dft_en_i(caliptra_ss_lc_dft_en_tb),
    .caliptra_ss_lc_escalate_en_i(caliptra_ss_lc_escalate_en_tb),
    .caliptra_ss_lc_check_byp_en_i(caliptra_ss_lc_check_byp_en_tb),
    .otp_caliptra_ss_lc_data_o(),


        .otp_keymgr_key_o           (),
        .flash_otp_key_i            (),
        .flash_otp_key_o            (),
        .sram_otp_key_i             (),
        .sram_otp_key_o             (),
        .otbn_otp_key_i             (),
        .otbn_otp_key_o             (),
        .otp_broadcast_o            (),
        .otp_ext_voltage_h_io       (),
        .scan_en_i                  (),
        .scan_rst_ni                (),
        .scanmode_i                 (scanmode_mubi),
        .cio_test_o                 (),
        .cio_test_en_o                   ()
	); 


    assign scanmode_mubi = scan_mode ? caliptra_prim_mubi_pkg::MuBi4True : caliptra_prim_mubi_pkg::MuBi4False;

    assign core_axi_wr_req.awaddr = axi_interconnect.sintf_arr[5].AWADDR;
    assign core_axi_wr_req.awburst = axi_interconnect.sintf_arr[5].AWBURST;
    assign core_axi_wr_req.awsize = axi_interconnect.sintf_arr[5].AWSIZE;
    assign core_axi_wr_req.awlen = axi_interconnect.sintf_arr[5].AWLEN;
    assign core_axi_wr_req.awuser = axi_interconnect.sintf_arr[5].AWUSER;
    assign core_axi_wr_req.awid = axi_interconnect.sintf_arr[5].AWID;
    assign core_axi_wr_req.awlock = axi_interconnect.sintf_arr[5].AWLOCK;
    assign core_axi_wr_req.awvalid = axi_interconnect.sintf_arr[5].AWVALID;
    assign core_axi_wr_req.wdata = axi_interconnect.sintf_arr[5].WDATA;
    assign core_axi_wr_req.wstrb = axi_interconnect.sintf_arr[5].WSTRB;
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
    assign axi_interconnect.sintf_arr[5].RDATA = core_axi_rd_rsp.rdata;
    assign axi_interconnect.sintf_arr[5].RRESP = core_axi_rd_rsp.rresp;
    assign axi_interconnect.sintf_arr[5].RID = core_axi_rd_rsp.rid;
    assign axi_interconnect.sintf_arr[5].RLAST = core_axi_rd_rsp.rlast;
    assign axi_interconnect.sintf_arr[5].RVALID = core_axi_rd_rsp.rvalid;

    assign prim_axi_wr_req.awaddr = axi_interconnect.sintf_arr[6].AWADDR;
    assign prim_axi_wr_req.awburst = axi_interconnect.sintf_arr[6].AWBURST;
    assign prim_axi_wr_req.awsize = axi_interconnect.sintf_arr[6].AWSIZE;
    assign prim_axi_wr_req.awlen = axi_interconnect.sintf_arr[6].AWLEN;
    assign prim_axi_wr_req.awuser = axi_interconnect.sintf_arr[6].AWUSER;
    assign prim_axi_wr_req.awid = axi_interconnect.sintf_arr[6].AWID;
    assign prim_axi_wr_req.awlock = axi_interconnect.sintf_arr[6].AWLOCK;
    assign prim_axi_wr_req.awvalid = axi_interconnect.sintf_arr[6].AWVALID;
    assign prim_axi_wr_req.wdata = axi_interconnect.sintf_arr[6].WDATA;
    assign prim_axi_wr_req.wstrb = axi_interconnect.sintf_arr[6].WSTRB;
    assign prim_axi_wr_req.wlast = axi_interconnect.sintf_arr[6].WLAST;
    assign prim_axi_wr_req.wvalid = axi_interconnect.sintf_arr[6].WVALID;
    assign prim_axi_wr_req.bready = axi_interconnect.sintf_arr[6].BREADY;

    assign axi_interconnect.sintf_arr[6].AWREADY = prim_axi_wr_rsp.awready;
    assign axi_interconnect.sintf_arr[6].WREADY = prim_axi_wr_rsp.wready;
    assign axi_interconnect.sintf_arr[6].BRESP = prim_axi_wr_rsp.bresp;
    assign axi_interconnect.sintf_arr[6].BID = prim_axi_wr_rsp.bid;
    assign axi_interconnect.sintf_arr[6].BVALID = prim_axi_wr_rsp.bvalid;

    assign prim_axi_rd_req.araddr = axi_interconnect.sintf_arr[6].ARADDR;
    assign prim_axi_rd_req.arburst = axi_interconnect.sintf_arr[6].ARBURST;
    assign prim_axi_rd_req.arsize = axi_interconnect.sintf_arr[6].ARSIZE;
    assign prim_axi_rd_req.arlen = axi_interconnect.sintf_arr[6].ARLEN;
    assign prim_axi_rd_req.aruser = axi_interconnect.sintf_arr[6].ARUSER;
    assign prim_axi_rd_req.arid = axi_interconnect.sintf_arr[6].ARID;
    assign prim_axi_rd_req.arlock = axi_interconnect.sintf_arr[6].ARLOCK;
    assign prim_axi_rd_req.arvalid = axi_interconnect.sintf_arr[6].ARVALID;
    assign prim_axi_rd_req.rready = axi_interconnect.sintf_arr[6].RREADY;

    assign axi_interconnect.sintf_arr[6].ARREADY = prim_axi_rd_rsp.arready;
    assign axi_interconnect.sintf_arr[6].RDATA = prim_axi_rd_rsp.rdata;
    assign axi_interconnect.sintf_arr[6].RRESP = prim_axi_rd_rsp.rresp;
    assign axi_interconnect.sintf_arr[6].RID = prim_axi_rd_rsp.rid;
    assign axi_interconnect.sintf_arr[6].RLAST = prim_axi_rd_rsp.rlast;
    assign axi_interconnect.sintf_arr[6].RVALID = prim_axi_rd_rsp.rvalid;

    fuse_ctrl_bfm u_fuse_ctrl_bfm (
        .core_clk            (core_clk            ),
        .cptra_pwrgood       (cptra_pwrgood       ),
        .fc_partition_init   (pwr_otp_init_i      ),
        .caliptra_ss_lc_dft_en_i         (),
        .caliptra_ss_lc_escalate_en_i    (),
        .caliptra_ss_lc_check_byp_en_i   (),
        .otp_caliptra_ss_lc_data_o (otp_ctrl_pkg::otp_caliptra_ss_lc_data_t'(otp_caliptra_ss_lc_data_tb)),
        .fuse_ctrl_rdy       (fuse_ctrl_rdy       )
    );

    // assign otp_caliptra_ss_lc_data_o_valid = otp_caliptra_ss_lc_data_o.valid;

    // assign fuse_ctrl_rdy = 1;
    // De-assert cptra_rst_b only after fuse_ctrl has initialized
    assign cptra_rst_b = rst_l;//fuse_ctrl_rdy ? cptra_soc_bfm_rst_b : 1'b0;

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
    `ifdef MCU_RV_ICCM_ENABLE
    case(bank) // {
      0: `MCU_IRAM(0)[idx] = data;
      1: `MCU_IRAM(1)[idx] = data;
     `ifdef MCU_RV_ICCM_NUM_BANKS_4
      2: `MCU_IRAM(2)[idx] = data;
      3: `MCU_IRAM(3)[idx] = data;
     `endif
     `ifdef MCU_RV_ICCM_NUM_BANKS_8
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
    `ifdef MCU_RV_ICCM_ENABLE
        `MCU_IRAM(0) = '{default:39'h0};
        `MCU_IRAM(1) = '{default:39'h0};
    `ifdef MCU_RV_ICCM_NUM_BANKS_4
        `MCU_IRAM(2) = '{default:39'h0};
        `MCU_IRAM(3) = '{default:39'h0};
    `endif
    `ifdef MCU_RV_ICCM_NUM_BANKS_8
        `MCU_IRAM(4) = '{default:39'h0};
        `MCU_IRAM(5) = '{default:39'h0};
        `MCU_IRAM(6) = '{default:39'h0};
        `MCU_IRAM(7) = '{default:39'h0};
    `endif

    `ifdef MCU_RV_ICCM_NUM_BANKS_16
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
    `ifdef MCU_RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`css_mcu0_RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif MCU_RV_ICCM_NUM_BANKS_4
        bank_idx = int'(addr[`css_mcu0_RV_ICCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif MCU_RV_ICCM_NUM_BANKS_8
        bank_idx = int'(addr[`css_mcu0_RV_ICCM_BITS-1:5]);
        return int'( addr[4:2]);
    `elsif MCU_RV_ICCM_NUM_BANKS_16
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
    `ifdef MCU_RV_DCCM_ENABLE
            if (i >= `css_mcu0_RV_DCCM_SADR && i < `css_mcu0_RV_DCCM_EADR) begin
                bit[38:0] data;
                int bank, indx;
                bank = get_dccm_bank(i, indx);

                case (bank)
                0: data = `MCU_DRAM(0)[indx];
                1: data = `MCU_DRAM(1)[indx];
                `ifdef MCU_RV_DCCM_NUM_BANKS_4
                2: data = `MCU_DRAM(2)[indx];
                3: data = `MCU_DRAM(3)[indx];
                `endif
                `ifdef MCU_RV_DCCM_NUM_BANKS_8
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

/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */

endmodule
