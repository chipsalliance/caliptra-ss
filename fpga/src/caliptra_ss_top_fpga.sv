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
//`default_nettype none

//`include "common_defines.sv"
//`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
//`include "caliptra_macros.svh"

`include "config_defines_mcu.svh"
`include "css_mcu0_common_defines.vh"
//import mcu_el2_pkg::*;

import mcu_fpga_realtime_regs_pkg::*;

`define CLP_OBF_UDS_DWORDS 16
`define CLP_OBF_FE_DWORDS  8

module caliptra_ss_top_fpga (
    input bit core_clk,

    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    output wire                      M_AXI_MCU_LSU_AWVALID,
    input  wire                      M_AXI_MCU_LSU_AWREADY,
    output wire [18:0]              M_AXI_MCU_LSU_AWID,
    output wire [              31:0] M_AXI_MCU_LSU_AWADDR,
    output wire [               3:0] M_AXI_MCU_LSU_AWREGION,
    output wire [               7:0] M_AXI_MCU_LSU_AWLEN,
    output wire [               2:0] M_AXI_MCU_LSU_AWSIZE,
    output wire [               1:0] M_AXI_MCU_LSU_AWBURST,
    output wire                      M_AXI_MCU_LSU_AWLOCK,
    output wire [               3:0] M_AXI_MCU_LSU_AWCACHE,
    output wire [               2:0] M_AXI_MCU_LSU_AWPROT,
    output wire [               3:0] M_AXI_MCU_LSU_AWQOS,

    output wire                      M_AXI_MCU_LSU_WVALID,
    input  wire                      M_AXI_MCU_LSU_WREADY,
    output wire [63:0]               M_AXI_MCU_LSU_WDATA,
    output wire [ 7:0]               M_AXI_MCU_LSU_WSTRB,
    output wire                      M_AXI_MCU_LSU_WLAST,

    input  wire                      M_AXI_MCU_LSU_BVALID,
    output wire                      M_AXI_MCU_LSU_BREADY,
    input  wire [               1:0] M_AXI_MCU_LSU_BRESP,
    input  wire [18:0]              M_AXI_MCU_LSU_BID,

    // AXI Read Channels
    output wire                      M_AXI_MCU_LSU_ARVALID,
    input  wire                      M_AXI_MCU_LSU_ARREADY,
    output wire [18:0]              M_AXI_MCU_LSU_ARID,
    output wire [              31:0] M_AXI_MCU_LSU_ARADDR,
    output wire [               3:0] M_AXI_MCU_LSU_ARREGION,
    output wire [               7:0] M_AXI_MCU_LSU_ARLEN,
    output wire [               2:0] M_AXI_MCU_LSU_ARSIZE,
    output wire [               1:0] M_AXI_MCU_LSU_ARBURST,
    output wire                      M_AXI_MCU_LSU_ARLOCK,
    output wire [               3:0] M_AXI_MCU_LSU_ARCACHE,
    output wire [               2:0] M_AXI_MCU_LSU_ARPROT,
    output wire [               3:0] M_AXI_MCU_LSU_ARQOS,

    input  wire                      M_AXI_MCU_LSU_RVALID,
    output wire                      M_AXI_MCU_LSU_RREADY,
    input  wire [18:0]              M_AXI_MCU_LSU_RID,
    input  wire [              63:0] M_AXI_MCU_LSU_RDATA,
    input  wire [               1:0] M_AXI_MCU_LSU_RRESP,
    input  wire                      M_AXI_MCU_LSU_RLAST,

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    output wire                      M_AXI_MCU_IFU_AWVALID,
    input  wire                      M_AXI_MCU_IFU_AWREADY,
    output wire [18:0]              M_AXI_MCU_IFU_AWID,
    output wire [              31:0] M_AXI_MCU_IFU_AWADDR,
    output wire [               3:0] M_AXI_MCU_IFU_AWREGION,
    output wire [               7:0] M_AXI_MCU_IFU_AWLEN,
    output wire [               2:0] M_AXI_MCU_IFU_AWSIZE,
    output wire [               1:0] M_AXI_MCU_IFU_AWBURST,
    output wire                      M_AXI_MCU_IFU_AWLOCK,
    output wire [               3:0] M_AXI_MCU_IFU_AWCACHE,
    output wire [               2:0] M_AXI_MCU_IFU_AWPROT,
    output wire [               3:0] M_AXI_MCU_IFU_AWQOS,

    output wire                      M_AXI_MCU_IFU_WVALID,
    input  wire                      M_AXI_MCU_IFU_WREADY,
    output wire [63:0]               M_AXI_MCU_IFU_WDATA,
    output wire [ 7:0]               M_AXI_MCU_IFU_WSTRB,
    output wire                      M_AXI_MCU_IFU_WLAST,

    input  wire                      M_AXI_MCU_IFU_BVALID,
    output wire                      M_AXI_MCU_IFU_BREADY,
    input  wire [               1:0] M_AXI_MCU_IFU_BRESP,
    input  wire [18:0]              M_AXI_MCU_IFU_BID,

    // AXI Read Channels
    output wire                      M_AXI_MCU_IFU_ARVALID,
    input  wire                      M_AXI_MCU_IFU_ARREADY,
    output wire [18:0]              M_AXI_MCU_IFU_ARID,
    output wire [              31:0] M_AXI_MCU_IFU_ARADDR,
    output wire [               3:0] M_AXI_MCU_IFU_ARREGION,
    output wire [               7:0] M_AXI_MCU_IFU_ARLEN,
    output wire [               2:0] M_AXI_MCU_IFU_ARSIZE,
    output wire [               1:0] M_AXI_MCU_IFU_ARBURST,
    output wire                      M_AXI_MCU_IFU_ARLOCK,
    output wire [               3:0] M_AXI_MCU_IFU_ARCACHE,
    output wire [               2:0] M_AXI_MCU_IFU_ARPROT,
    output wire [               3:0] M_AXI_MCU_IFU_ARQOS,

    input  wire                      M_AXI_MCU_IFU_RVALID,
    output wire                      M_AXI_MCU_IFU_RREADY,
    input  wire [18:0]              M_AXI_MCU_IFU_RID,
    input  wire [              63:0] M_AXI_MCU_IFU_RDATA,
    input  wire [               1:0] M_AXI_MCU_IFU_RRESP,
    input  wire                      M_AXI_MCU_IFU_RLAST,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    output wire                     sb_axi_awvalid,
    input  wire                     sb_axi_awready,
    output wire [18:0]             sb_axi_awid,
    output wire [             31:0] sb_axi_awaddr,
    output wire [              3:0] sb_axi_awregion,
    output wire [              7:0] sb_axi_awlen,
    output wire [              2:0] sb_axi_awsize,
    output wire [              1:0] sb_axi_awburst,
    output wire                     sb_axi_awlock,
    output wire [              3:0] sb_axi_awcache,
    output wire [              2:0] sb_axi_awprot,
    output wire [              3:0] sb_axi_awqos,

    output wire                     sb_axi_wvalid,
    input  wire                     sb_axi_wready,
    output wire [63:0]              sb_axi_wdata,
    output wire [ 7:0]              sb_axi_wstrb,
    output wire                     sb_axi_wlast,

    input  wire                     sb_axi_bvalid,
    output wire                     sb_axi_bready,
    input  wire [              1:0] sb_axi_bresp,
    input  wire [18:0]             sb_axi_bid,

    // AXI Read Channels
    output wire                     sb_axi_arvalid,
    input  wire                     sb_axi_arready,
    output wire [18:0]             sb_axi_arid,
    output wire [             31:0] sb_axi_araddr,
    output wire [              3:0] sb_axi_arregion,
    output wire [              7:0] sb_axi_arlen,
    output wire [              2:0] sb_axi_arsize,
    output wire [              1:0] sb_axi_arburst,
    output wire                     sb_axi_arlock,
    output wire [              3:0] sb_axi_arcache,
    output wire [              2:0] sb_axi_arprot,
    output wire [              3:0] sb_axi_arqos,

    input  wire                     sb_axi_rvalid,
    output wire                     sb_axi_rready,
    input  wire [18:0]             sb_axi_rid,
    input  wire [             63:0] sb_axi_rdata,
    input  wire [              1:0] sb_axi_rresp,
    input  wire                     sb_axi_rlast,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    input  wire                      S_AXI_MCU_DMA_AWVALID,
    output wire                      S_AXI_MCU_DMA_AWREADY,
    input  wire [18:0]              S_AXI_MCU_DMA_AWID,
    input  wire [              31:0] S_AXI_MCU_DMA_AWADDR,
    input  wire [               2:0] S_AXI_MCU_DMA_AWSIZE,
    input  wire [               2:0] S_AXI_MCU_DMA_AWPROT,
    input  wire [               7:0] S_AXI_MCU_DMA_AWLEN,
    input  wire [               1:0] S_AXI_MCU_DMA_AWBURST,


    input  wire                      S_AXI_MCU_DMA_WVALID,
    output wire                      S_AXI_MCU_DMA_WREADY,
    input  wire [63:0]               S_AXI_MCU_DMA_WDATA,
    input  wire [ 7:0]               S_AXI_MCU_DMA_WSTRB,
    input  wire                      S_AXI_MCU_DMA_WLAST,

    output wire                      S_AXI_MCU_DMA_BVALID,
    input  wire                      S_AXI_MCU_DMA_BREADY,
    output wire [               1:0] S_AXI_MCU_DMA_BRESP,
    output wire [18:0]              S_AXI_MCU_DMA_BID,

    // AXI Read CHANNELS
    input  wire                      S_AXI_MCU_DMA_ARVALID,
    output wire                      S_AXI_MCU_DMA_ARREADY,
    input  wire [18:0]              S_AXI_MCU_DMA_ARID,
    input  wire [              31:0] S_AXI_MCU_DMA_ARADDR,
    input  wire [               2:0] S_AXI_MCU_DMA_ARSIZE,
    input  wire [               2:0] S_AXI_MCU_DMA_ARPROT,
    input  wire [               7:0] S_AXI_MCU_DMA_ARLEN,
    input  wire [               1:0] S_AXI_MCU_DMA_ARBURST,

    output wire                      S_AXI_MCU_DMA_RVALID,
    input  wire                      S_AXI_MCU_DMA_RREADY,
    output wire [18:0]              S_AXI_MCU_DMA_RID,
    output wire [              63:0] S_AXI_MCU_DMA_RDATA,
    output wire [               1:0] S_AXI_MCU_DMA_RRESP,
    output wire                      S_AXI_MCU_DMA_RLAST,

    // FPGA Realtime register AXI Interface
    input	wire                      S_AXI_WRAPPER_ARESETN,
    input	wire                      S_AXI_WRAPPER_AWVALID,
    output	wire                      S_AXI_WRAPPER_AWREADY,
    input	wire [31:0]               S_AXI_WRAPPER_AWADDR,
    input	wire [2:0]                S_AXI_WRAPPER_AWPROT,
    input	wire                      S_AXI_WRAPPER_WVALID,
    output	wire                      S_AXI_WRAPPER_WREADY,
    input	wire [31:0]               S_AXI_WRAPPER_WDATA,
    input	wire [3:0]                S_AXI_WRAPPER_WSTRB,
    output	wire                      S_AXI_WRAPPER_BVALID,
    input	wire                      S_AXI_WRAPPER_BREADY,
    output	wire [1:0]                S_AXI_WRAPPER_BRESP,
    input	wire                      S_AXI_WRAPPER_ARVALID,
    output	wire                      S_AXI_WRAPPER_ARREADY,
    input	wire [31:0]               S_AXI_WRAPPER_ARADDR,
    input	wire [2:0]                S_AXI_WRAPPER_ARPROT,
    output	wire                      S_AXI_WRAPPER_RVALID,
    input	wire                      S_AXI_WRAPPER_RREADY,
    output	wire [31:0]               S_AXI_WRAPPER_RDATA,
    output	wire [1:0]                S_AXI_WRAPPER_RRESP,
    
    // I3C
    input	wire                      S_AXI_I3C_AWVALID,
    output	wire                      S_AXI_I3C_AWREADY,
    input	wire [31:0]               S_AXI_I3C_AWADDR,
    input	wire [2:0]                S_AXI_I3C_AWPROT,
    input	wire                      S_AXI_I3C_WVALID,
    output	wire                      S_AXI_I3C_WREADY,
    input	wire [63:0]               S_AXI_I3C_WDATA,
    input	wire [7:0]                S_AXI_I3C_WSTRB,
    output	wire                      S_AXI_I3C_BVALID,
    input	wire                      S_AXI_I3C_BREADY,
    output	wire [1:0]                S_AXI_I3C_BRESP,
    input	wire                      S_AXI_I3C_ARVALID,
    output	wire                      S_AXI_I3C_ARREADY,
    input	wire [31:0]               S_AXI_I3C_ARADDR,
    input	wire [2:0]                S_AXI_I3C_ARPROT,
    output	wire                      S_AXI_I3C_RVALID,
    input	wire                      S_AXI_I3C_RREADY,
    output	wire [63:0]               S_AXI_I3C_RDATA,
    output	wire [1:0]                S_AXI_I3C_RRESP,
    
    input wire [1:0] S_AXI_I3C_ARBURST,
    input wire [2:0] S_AXI_I3C_ARSIZE,
    input wire [7:0] S_AXI_I3C_ARLEN,
    input wire [31:0] S_AXI_I3C_ARUSER,
    input wire [18:0] S_AXI_I3C_ARID,
    input wire S_AXI_I3C_ARLOCK,
    output wire [18:0]           S_AXI_I3C_RID,
    output wire                   S_AXI_I3C_RLAST,
    input wire [             1:0] S_AXI_I3C_AWBURST,
    input wire [             2:0] S_AXI_I3C_AWSIZE,
    input wire [             7:0] S_AXI_I3C_AWLEN,
    input wire [31:0] S_AXI_I3C_AWUSER,
    input wire [18:0] S_AXI_I3C_AWID,
    input wire                    S_AXI_I3C_AWLOCK,
    input  wire                  S_AXI_I3C_WLAST,
    output wire [18:0] S_AXI_I3C_BID,

    // I3C
    output SDA_UP,
    output SDA_PUSH,
    output SDA_PULL,
    input  SDA,
    output SCL_UP,
    output SCL_PUSH,
    output SCL_PULL,
    input  SCL,

    // SS IMEM BRAM Interface
    input  logic ss_axi_bram_clk,
    input  logic ss_axi_bram_en,
    input  logic [3:0] ss_axi_bram_we,
    input  logic [15:0] ss_axi_bram_addr,
    input  logic [31:0] ss_axi_bram_din,
    output logic [31:0] ss_axi_bram_dout,
    input  logic ss_axi_bram_rst,

    // From Caliptra to MCU
    input logic mcu_sram_fw_exec_region_lock,
    input logic mailbox_data_avail,
    
    // FC to Caliptra 
    output logic uds_field_entrpy_valid,
    output logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed,
    output logic [`CLP_OBF_FE_DWORDS-1 : 0][31:0] cptra_obf_field_entropy,

    input  lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_ack_i,
    output lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_req_o,

    // Lifecycle controller
    input [31:0] S_AXI_LCC_awaddr,
    input [1:0] S_AXI_LCC_awburst,
    input [2:0] S_AXI_LCC_awsize,
    input [7:0] S_AXI_LCC_awlen,
    input [31:0] S_AXI_LCC_awuser,
    input [7:0] S_AXI_LCC_awid,
    input S_AXI_LCC_awlock,
    input S_AXI_LCC_awvalid,
    input [31:0] S_AXI_LCC_wdata,
    input [3:0] S_AXI_LCC_wstrb,
    input S_AXI_LCC_wlast,
    input S_AXI_LCC_wvalid,
    input S_AXI_LCC_bready,
    output S_AXI_LCC_awready,
    output S_AXI_LCC_wready,
    output [1:0]S_AXI_LCC_bresp,
    output [7:0]S_AXI_LCC_bid,
    output S_AXI_LCC_bvalid,
    input [31:0] S_AXI_LCC_araddr,
    input [1:0] S_AXI_LCC_arburst,
    input [2:0] S_AXI_LCC_arsize,
    input [7:0] S_AXI_LCC_arlen,
    input [31:0] S_AXI_LCC_aruser,
    input [7:0] S_AXI_LCC_arid,
    input S_AXI_LCC_arlock,
    input S_AXI_LCC_arvalid,
    input S_AXI_LCC_rready,
    output S_AXI_LCC_arready,
    output [31:0] S_AXI_LCC_rdata,
    output [1:0] S_AXI_LCC_rresp,
    output [7:0] S_AXI_LCC_rid,
    output S_AXI_LCC_rlast,
    output S_AXI_LCC_rvalid,

    // Fuse controller
    input [31:0] S_AXI_OTP_awaddr,
    input [1:0] S_AXI_OTP_awburst,
    input [2:0] S_AXI_OTP_awsize,
    input [7:0] S_AXI_OTP_awlen,
    input [31:0] S_AXI_OTP_awuser,
    input [7:0] S_AXI_OTP_awid,
    input S_AXI_OTP_awlock,
    input S_AXI_OTP_awvalid,
    input [31:0] S_AXI_OTP_wdata,
    input [3:0] S_AXI_OTP_wstrb,
    input S_AXI_OTP_wlast,
    input S_AXI_OTP_wvalid,
    input S_AXI_OTP_bready,
    output S_AXI_OTP_awready,
    output S_AXI_OTP_wready,
    output [1:0]S_AXI_OTP_bresp,
    output [7:0]S_AXI_OTP_bid,
    output S_AXI_OTP_bvalid,
    input [31:0] S_AXI_OTP_araddr,
    input [1:0] S_AXI_OTP_arburst,
    input [2:0] S_AXI_OTP_arsize,
    input [7:0] S_AXI_OTP_arlen,
    input [31:0] S_AXI_OTP_aruser,
    input [7:0] S_AXI_OTP_arid,
    input S_AXI_OTP_arlock,
    input S_AXI_OTP_arvalid,
    input S_AXI_OTP_rready,
    output S_AXI_OTP_arready,
    output [31:0] S_AXI_OTP_rdata,
    output [1:0] S_AXI_OTP_rresp,
    output [7:0] S_AXI_OTP_rid,
    output S_AXI_OTP_rlast,
    output S_AXI_OTP_rvalid,
    
// Caliptra SS Fuse Controller Interface (Fuse Macros)
    input  tlul_pkg::tl_h2d_t cptra_ss_fuse_macro_prim_tl_i,
    output tlul_pkg::tl_d2h_t cptra_ss_fuse_macro_prim_tl_o
);


    xpm_memory_spram #(
        .ADDR_WIDTH_A(32), // DECIMAL
        .AUTO_SLEEP_TIME(0),            // DECIMAL
        .BYTE_WRITE_WIDTH_A(32),        // DECIMAL
        .CASCADE_HEIGHT(0),             // DECIMAL
        .ECC_MODE("no_ecc"),            // String
        .MEMORY_INIT_FILE("none"),      // String
        .MEMORY_INIT_PARAM("0"),        // String
        .MEMORY_OPTIMIZATION("false"),  // String
        .MEMORY_PRIMITIVE("auto"),      // String
        .MEMORY_SIZE(64*1024*8),        // DECIMAL
        .MESSAGE_CONTROL(0),            // DECIMAL
        .READ_DATA_WIDTH_A(32),         // DECIMAL
        .READ_LATENCY_A(1),             // DECIMAL
        .READ_RESET_VALUE_A("0"),       // String
        .RST_MODE_A("SYNC"),            // String
        .SIM_ASSERT_CHK(0),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
        .USE_MEM_INIT(1),               // DECIMAL
        .USE_MEM_INIT_MMI(0),           // DECIMAL
        .WAKEUP_TIME("disable_sleep"),  // String
        .WRITE_DATA_WIDTH_A(32),        // DECIMAL
        .WRITE_MODE_A("no_change"),     // String
        .WRITE_PROTECT(1)               // DECIMAL
    )
    imem_inst1 (
        .dbiterra(),
        .douta(ss_axi_bram_dout),
        .sbiterra(),
        .addra(ss_axi_bram_addr),
        .clka(core_clk),
        .dina(ss_axi_bram_din),
        .ena(ss_axi_bram_en),
        .injectdbiterra(0),
        .injectsbiterra(0),
        .regcea(1),
        .rsta(ss_axi_bram_rst),
        .sleep(0),
        .wea(ss_axi_bram_we)
    );

    axi4lite_intf s_axil ();

    mcu_fpga_realtime_regs__in_t hwif_in;
    mcu_fpga_realtime_regs__out_t hwif_out;

    assign S_AXI_WRAPPER_AWREADY = s_axil.AWREADY;
    assign S_AXI_WRAPPER_WREADY = s_axil.WREADY;
    assign S_AXI_WRAPPER_BVALID = s_axil.BVALID;
    assign S_AXI_WRAPPER_BRESP = s_axil.BRESP;
    assign S_AXI_WRAPPER_ARREADY = s_axil.ARREADY;
    assign S_AXI_WRAPPER_RVALID = s_axil.RVALID;
    assign S_AXI_WRAPPER_RDATA = s_axil.RDATA;
    assign S_AXI_WRAPPER_RRESP = s_axil.RRESP;

    always_comb begin
        s_axil.AWVALID = S_AXI_WRAPPER_AWVALID;
        s_axil.AWADDR =  S_AXI_WRAPPER_AWADDR;
        s_axil.AWPROT =  S_AXI_WRAPPER_AWPROT;

        s_axil.WVALID =  S_AXI_WRAPPER_WVALID;
        s_axil.WDATA =   S_AXI_WRAPPER_WDATA;
        s_axil.WSTRB =   S_AXI_WRAPPER_WSTRB;

        s_axil.BREADY =  S_AXI_WRAPPER_BREADY;

        s_axil.ARVALID = S_AXI_WRAPPER_ARVALID;
        s_axil.ARADDR =  S_AXI_WRAPPER_ARADDR;
        s_axil.ARPROT =  S_AXI_WRAPPER_ARPROT;

        s_axil.RREADY =  S_AXI_WRAPPER_RREADY;
    end

    // Register Block
    mcu_fpga_realtime_regs regs (
        .clk(core_clk),
        .rst(~S_AXI_WRAPPER_ARESETN),

        .s_axil(s_axil),

        .hwif_in (hwif_in),
        .hwif_out(hwif_out)
    );

    // Log FIFO
    // Valid = !Empty
    logic log_fifo_empty;
    assign hwif_in.fifo_regs.log_fifo_data.char_valid.next = ~log_fifo_empty;
    assign hwif_in.fifo_regs.log_fifo_status.log_fifo_empty.next = log_fifo_empty;

    // When rd_swacc is asserted, use the value of "valid" from when it was sampled.
    reg log_fifo_valid_f;
    // Delay FIFO input wr_en by one cycle
    reg wr_swacc_f;
    always@(posedge core_clk) begin
        log_fifo_valid_f <= ~log_fifo_empty;
        wr_swacc_f <= hwif_out.fifo_regs.log_fifo_input.char.wr_swacc;
    end


   xpm_fifo_sync #(
      .CASCADE_HEIGHT(0),         // DECIMAL
      .DOUT_RESET_VALUE("0"),     // String
      .ECC_MODE("no_ecc"),        // String
      .FIFO_MEMORY_TYPE("block"), // String
      .FIFO_READ_LATENCY(0),      // DECIMAL
      .FIFO_WRITE_DEPTH(8192),    // DECIMAL
      .FULL_RESET_VALUE(0),       // DECIMAL
      .PROG_EMPTY_THRESH(10),     // DECIMAL
      .PROG_FULL_THRESH(7168),    // DECIMAL Currently unused
      .RD_DATA_COUNT_WIDTH(14),   // DECIMAL
      .READ_DATA_WIDTH(8),        // DECIMAL
      .READ_MODE("fwft"),         // String
      .SIM_ASSERT_CHK(0),         // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
      .USE_ADV_FEATURES("0000"),  // String
      .WAKEUP_TIME(0),            // DECIMAL
      .WRITE_DATA_WIDTH(8),       // DECIMAL
      .WR_DATA_COUNT_WIDTH(14)    // DECIMAL
   )
   log_fifo_inst (
      .almost_empty(),
      .almost_full(),
      .data_valid(),
      .dbiterr(),
      .dout(hwif_in.fifo_regs.log_fifo_data.next_char.next),
      .empty(log_fifo_empty),
      .full(hwif_in.fifo_regs.log_fifo_status.log_fifo_full.next),
      .overflow(),
      .prog_empty(),
      .prog_full(),
      .rd_data_count(),
      .rd_rst_busy(),
      .sbiterr(),
      .underflow(),
      .wr_ack(),
      .wr_data_count(),
      .wr_rst_busy(),
      .din(hwif_out.fifo_regs.log_fifo_input.char.value),
      .injectdbiterr(0),
      .injectsbiterr(0),
      .rd_en(log_fifo_valid_f & hwif_out.fifo_regs.log_fifo_data.next_char.rd_swacc),
      .rst(~S_AXI_WRAPPER_ARESETN),
      .sleep(0),
      .wr_clk(core_clk),
      .wr_en(wr_swacc_f)
   );

    // I3C
fpga_i3c_wrapper #(
    .AxiDataWidth(32),
    .AxiAddrWidth(32),
    .AxiUserWidth(32),
    .AxiIdWidth(19)
) i3c (
    .clk_i       (clk_cg),
    .rst_ni      (hwif_out.interface_regs.control.i3c_rst_n.value),

    .araddr_i(S_AXI_I3C_ARADDR),
    .arburst_i(S_AXI_I3C_ARBURST),
    .arsize_i(S_AXI_I3C_ARSIZE),
    .arlen_i(S_AXI_I3C_ARLEN),
    .aruser_i(S_AXI_I3C_ARUSER),
    .arid_i(S_AXI_I3C_ARID),
    .arlock_i(S_AXI_I3C_ARLOCK),
    .arvalid_i(S_AXI_I3C_ARVALID),
    .arready_o(S_AXI_I3C_ARREADY),

    .rdata_o(S_AXI_I3C_RDATA),
    .rresp_o(S_AXI_I3C_RRESP),
    .rid_o(S_AXI_I3C_RID),
    .rlast_o(S_AXI_I3C_RLAST),
    .rvalid_o(S_AXI_I3C_RVALID),
    .rready_i(S_AXI_I3C_RREADY),

    // AXI Write Channels
    .awaddr_i(S_AXI_I3C_AWADDR),
    .awburst_i(S_AXI_I3C_AWBURST),
    .awsize_i(S_AXI_I3C_AWSIZE),
    .awlen_i(S_AXI_I3C_AWLEN),
    .awuser_i(S_AXI_I3C_AWUSER),
    .awid_i(S_AXI_I3C_AWID),
    .awlock_i(S_AXI_I3C_AWLOCK),
    .awvalid_i(S_AXI_I3C_AWVALID),
    .awready_o(S_AXI_I3C_AWREADY),

    .wdata_i(S_AXI_I3C_WDATA),
    .wstrb_i(S_AXI_I3C_WSTRB),
    .wlast_i(S_AXI_I3C_WLAST),
    .wvalid_i(S_AXI_I3C_WVALID),
    .wready_o(S_AXI_I3C_WREADY),

    .bresp_o(S_AXI_I3C_BRESP),
    .bid_o(S_AXI_I3C_BID),
    .bvalid_o(S_AXI_I3C_BVALID),
    .bready_i(S_AXI_I3C_BREADY),

    // I3C bus IO
    //.scl_i(scl_i),
    //.sda_i(sda_i),
    //.scl_o(scl_o),
    //.sda_o(sda_o),
    //.sel_od_pp_o(sel_od_pp_o)
    //.i3c_scl_io(i3c_scl_io),
    //.i3c_sda_io(i3c_sda_io)
    
    .SDA_UP(SDA_UP),
    .SDA_PUSH(SDA_PUSH),
    .SDA_PULL(SDA_PULL),
    .SDA(SDA),
    .SCL_UP(SCL_UP),
    .SCL_PUSH(SCL_PUSH),
    .SCL_PULL(SCL_PULL),
    .SCL(SCL)
);


/*
  Line Driver logic
  sel_od_pp == 1 indicates push-pull
  | sel_od_pp | phy2io | phy_data_io |    |   EN | IN |    UP |    |      wire      |
  |         0 |      0 |           z | -> |    1 |  x |     1 | -> | z              | // TODO: Use z or pull up 2k?
  |         0 |      1 |           0 | -> |    0 |  1 |     0 | -> | open drain low |
  |         1 |      0 |           0 | -> |    0 |  1 |     1 | -> | push pull low  |
  |         1 |      1 |           1 | -> |    0 |  0 |     1 | -> | push pull high |
*/
/*
Hacks for testing driver board
assign SDA_UP = hwif_out.interface_regs.generic.generic.value[0];
assign SDA_PUSH = hwif_out.interface_regs.generic.generic.value[1]; // IN
assign SDA_PULL = hwif_out.interface_regs.generic.generic.value[2]; // EN

assign SCL_UP = hwif_out.interface_regs.generic.generic.value[4];
assign SCL_PUSH = hwif_out.interface_regs.generic.generic.value[5];
assign SCL_PULL = hwif_out.interface_regs.generic.generic.value[6];

assign hwif_in.interface_regs.generic_in.generic_in.next[3] = SDA;
assign hwif_in.interface_regs.generic_in.generic_in.next[7] = SCL;
*/

    // MCU
    logic mcu_rst_b;
        logic [31:1]  ext_int;
        logic                       mci_mcu_nmi_int;
        logic [31:0] mci_mcu_nmi_vector;
        logic                       mci_mcu_timer_int;
        logic                       soft_int;

        logic        [31:1]         jtag_id;
initial begin
            jtag_id[31:28] = 4'b1;
            jtag_id[27:12] = '0;
            jtag_id[11:1]  = 11'h45;
end

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


        logic                       mpc_debug_halt_req;
        logic                       mpc_debug_run_req;
        logic                       mpc_reset_run_req;
        logic                       mpc_debug_halt_ack;
        logic                       mpc_debug_run_ack;
        logic                       debug_brkpt_status;

        css_mcu0_el2_mem_if              mcu_el2_mem_export ();


       //=========================================================================-
       // RTL instance
       //=========================================================================-
        mcu_top rvtop_wrapper (
        .rst_l                  ( mcu_rst_b ), //hwif_out.interface_regs.control.rst_l.value ),
        .dbg_rst_l              ( hwif_out.interface_regs.control.dbg_rst_l.value ),
        .clk                    ( core_clk      ),
        .rst_vec                ( hwif_out.interface_regs.reset_vector.reset_vector.value[31:1]),
        .nmi_int                ( mci_mcu_nmi_int       ),
        .nmi_vec                ( mci_mcu_nmi_vector[31:1] ),
        .jtag_id                ( jtag_id[31:1]),



        //-------------------------- LSU AXI signals--------------------------
        // // AXI Write Channels

        .lsu_axi_awvalid        (M_AXI_MCU_LSU_AWVALID),
        .lsu_axi_awready        (M_AXI_MCU_LSU_AWREADY),
        .lsu_axi_awid           (M_AXI_MCU_LSU_AWID),
        .lsu_axi_awaddr         (M_AXI_MCU_LSU_AWADDR),
        .lsu_axi_awregion       (M_AXI_MCU_LSU_AWREGION),
        .lsu_axi_awlen          (M_AXI_MCU_LSU_AWLEN),
        .lsu_axi_awsize         (M_AXI_MCU_LSU_AWSIZE),
        .lsu_axi_awburst        (M_AXI_MCU_LSU_AWBURST),
        .lsu_axi_awlock         (M_AXI_MCU_LSU_AWLOCK),
        .lsu_axi_awcache        (M_AXI_MCU_LSU_AWCACHE),
        .lsu_axi_awprot         (M_AXI_MCU_LSU_AWPROT),
        .lsu_axi_awqos          (M_AXI_MCU_LSU_AWQOS),

        .lsu_axi_wvalid         (M_AXI_MCU_LSU_WVALID),
        .lsu_axi_wready         (M_AXI_MCU_LSU_WREADY),
        .lsu_axi_wdata          (M_AXI_MCU_LSU_WDATA),
        .lsu_axi_wstrb          (M_AXI_MCU_LSU_WSTRB),
        .lsu_axi_wlast          (M_AXI_MCU_LSU_WLAST),

        .lsu_axi_bvalid         (M_AXI_MCU_LSU_BVALID),
        .lsu_axi_bready         (M_AXI_MCU_LSU_BREADY),
        .lsu_axi_bresp          (M_AXI_MCU_LSU_BRESP),
        .lsu_axi_bid            (M_AXI_MCU_LSU_BID),

        .lsu_axi_arvalid        (M_AXI_MCU_LSU_ARVALID),
        .lsu_axi_arready        (M_AXI_MCU_LSU_ARREADY),
        .lsu_axi_arid           (M_AXI_MCU_LSU_ARID),
        .lsu_axi_araddr         (M_AXI_MCU_LSU_ARADDR),
        .lsu_axi_arregion       (M_AXI_MCU_LSU_ARREGION),
        .lsu_axi_arlen          (M_AXI_MCU_LSU_ARLEN),
        .lsu_axi_arsize         (M_AXI_MCU_LSU_ARSIZE),
        .lsu_axi_arburst        (M_AXI_MCU_LSU_ARBURST),
        .lsu_axi_arlock         (M_AXI_MCU_LSU_ARLOCK),
        .lsu_axi_arcache        (M_AXI_MCU_LSU_ARCACHE),
        .lsu_axi_arprot         (M_AXI_MCU_LSU_ARPROT),
        .lsu_axi_arqos          (M_AXI_MCU_LSU_ARQOS),

        .lsu_axi_rvalid         (M_AXI_MCU_LSU_RVALID),
        .lsu_axi_rready         (M_AXI_MCU_LSU_RREADY),
        .lsu_axi_rid            (M_AXI_MCU_LSU_RID),
        .lsu_axi_rdata          (M_AXI_MCU_LSU_RDATA),
        .lsu_axi_rresp          (M_AXI_MCU_LSU_RRESP),
        .lsu_axi_rlast          (M_AXI_MCU_LSU_RLAST),

        //-------------------------- IFU AXI signals--------------------------
        // AXI Write Channels

        .ifu_axi_awvalid        ( M_AXI_MCU_IFU_AWVALID ),
        .ifu_axi_awready        ( M_AXI_MCU_IFU_AWREADY ),
        .ifu_axi_awid           ( M_AXI_MCU_IFU_AWID    ),
        .ifu_axi_awaddr         ( M_AXI_MCU_IFU_AWADDR  ),
        .ifu_axi_awregion       ( M_AXI_MCU_IFU_AWREGION),
        .ifu_axi_awlen          ( M_AXI_MCU_IFU_AWLEN   ),
        .ifu_axi_awsize         ( M_AXI_MCU_IFU_AWSIZE  ),
        .ifu_axi_awburst        ( M_AXI_MCU_IFU_AWBURST ),
        .ifu_axi_awlock         ( M_AXI_MCU_IFU_AWLOCK  ),
        .ifu_axi_awcache        ( M_AXI_MCU_IFU_AWCACHE ),
        .ifu_axi_awprot         ( M_AXI_MCU_IFU_AWPROT  ),
        .ifu_axi_awqos          ( M_AXI_MCU_IFU_AWQOS   ),

        .ifu_axi_wvalid         ( M_AXI_MCU_IFU_WVALID  ),
        .ifu_axi_wready         ( M_AXI_MCU_IFU_WREADY  ),
        .ifu_axi_wdata          ( M_AXI_MCU_IFU_WDATA   ),
        .ifu_axi_wstrb          ( M_AXI_MCU_IFU_WSTRB   ),
        .ifu_axi_wlast          ( M_AXI_MCU_IFU_WLAST   ),

        .ifu_axi_bvalid         ( M_AXI_MCU_IFU_BVALID  ),
        .ifu_axi_bready         ( M_AXI_MCU_IFU_BREADY  ),
        .ifu_axi_bresp          ( M_AXI_MCU_IFU_BRESP   ),
        .ifu_axi_bid            ( M_AXI_MCU_IFU_BID     ),

        .ifu_axi_arvalid        ( M_AXI_MCU_IFU_ARVALID ),
        .ifu_axi_arready        ( M_AXI_MCU_IFU_ARREADY ),
        .ifu_axi_arid           ( M_AXI_MCU_IFU_ARID    ),
        .ifu_axi_araddr         ( M_AXI_MCU_IFU_ARADDR  ),
        .ifu_axi_arlen          ( M_AXI_MCU_IFU_ARLEN   ),
        .ifu_axi_arsize         ( M_AXI_MCU_IFU_ARSIZE  ),
        .ifu_axi_arburst        ( M_AXI_MCU_IFU_ARBURST ),
        .ifu_axi_arlock         ( M_AXI_MCU_IFU_ARLOCK  ),
        .ifu_axi_arcache        ( M_AXI_MCU_IFU_ARCACHE ),
        .ifu_axi_arprot         ( M_AXI_MCU_IFU_ARPROT  ),
        .ifu_axi_arqos          ( M_AXI_MCU_IFU_ARQOS   ),
        .ifu_axi_arregion       ( M_AXI_MCU_IFU_ARREGION),

        .ifu_axi_rvalid         ( M_AXI_MCU_IFU_RVALID  ),
        .ifu_axi_rready         ( M_AXI_MCU_IFU_RREADY  ),
        .ifu_axi_rid            ( M_AXI_MCU_IFU_RID     ),
        .ifu_axi_rdata          ( M_AXI_MCU_IFU_RDATA   ),
        .ifu_axi_rresp          ( M_AXI_MCU_IFU_RRESP   ),
        .ifu_axi_rlast          ( M_AXI_MCU_IFU_RLAST   ),

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
        .dma_axi_awvalid        (S_AXI_MCU_DMA_AWVALID),
        .dma_axi_awready        (S_AXI_MCU_DMA_AWREADY),
        .dma_axi_awid           (S_AXI_MCU_DMA_AWID),
        .dma_axi_awaddr         (S_AXI_MCU_DMA_AWADDR),
        .dma_axi_awsize         (S_AXI_MCU_DMA_AWSIZE),
        .dma_axi_awprot         (S_AXI_MCU_DMA_AWPROT),
        .dma_axi_awlen          (S_AXI_MCU_DMA_AWLEN),
        .dma_axi_awburst        (S_AXI_MCU_DMA_AWBURST),

        .dma_axi_wvalid         (S_AXI_MCU_DMA_WVALID),
        .dma_axi_wready         (S_AXI_MCU_DMA_WREADY),
        .dma_axi_wdata          (S_AXI_MCU_DMA_WDATA),
        .dma_axi_wstrb          (S_AXI_MCU_DMA_WSTRB),
        .dma_axi_wlast          (S_AXI_MCU_DMA_WLAST),

        .dma_axi_bvalid         (S_AXI_MCU_DMA_BVALID),
        .dma_axi_bready         (S_AXI_MCU_DMA_BREADY),
        .dma_axi_bresp          (S_AXI_MCU_DMA_BRESP),
        .dma_axi_bid            (S_AXI_MCU_DMA_BID),

        .dma_axi_arvalid        (S_AXI_MCU_DMA_ARVALID),
        .dma_axi_arready        (S_AXI_MCU_DMA_ARREADY),
        .dma_axi_arid           (S_AXI_MCU_DMA_ARID),
        .dma_axi_araddr         (S_AXI_MCU_DMA_ARADDR),
        .dma_axi_arsize         (S_AXI_MCU_DMA_ARSIZE),
        .dma_axi_arprot         (S_AXI_MCU_DMA_ARPROT),
        .dma_axi_arlen          (S_AXI_MCU_DMA_ARLEN),
        .dma_axi_arburst        (S_AXI_MCU_DMA_ARBURST),

        .dma_axi_rvalid         (S_AXI_MCU_DMA_RVALID),
        .dma_axi_rready         (S_AXI_MCU_DMA_RREADY),
        .dma_axi_rid            (S_AXI_MCU_DMA_RID),
        .dma_axi_rdata          (S_AXI_MCU_DMA_RDATA),
        .dma_axi_rresp          (S_AXI_MCU_DMA_RRESP),
        .dma_axi_rlast          (S_AXI_MCU_DMA_RLAST),

        .timer_int              ( mci_mcu_timer_int ),
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

        .mem_clk                (mcu_el2_mem_export.clk),

        .iccm_clken             (mcu_el2_mem_export.iccm_clken),
        .iccm_wren_bank         (mcu_el2_mem_export.iccm_wren_bank),
        .iccm_addr_bank         (mcu_el2_mem_export.iccm_addr_bank),
        .iccm_bank_wr_data      (mcu_el2_mem_export.iccm_bank_wr_data),
        .iccm_bank_wr_ecc       (mcu_el2_mem_export.iccm_bank_wr_ecc),
        .iccm_bank_dout         (mcu_el2_mem_export.iccm_bank_dout),
        .iccm_bank_ecc          (mcu_el2_mem_export.iccm_bank_ecc),

        .dccm_clken             (mcu_el2_mem_export.dccm_clken),
        .dccm_wren_bank         (mcu_el2_mem_export.dccm_wren_bank),
        .dccm_addr_bank         (mcu_el2_mem_export.dccm_addr_bank),
        .dccm_wr_data_bank      (mcu_el2_mem_export.dccm_wr_data_bank),
        .dccm_wr_ecc_bank       (mcu_el2_mem_export.dccm_wr_ecc_bank),
        .dccm_bank_dout         (mcu_el2_mem_export.dccm_bank_dout),
        .dccm_bank_ecc          (mcu_el2_mem_export.dccm_bank_ecc),

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
/*
        // I3C AXI interface
        .i3c_axi_awvalid(S_AXI_I3C_AWVALID),
        .i3c_axi_awready(S_AXI_I3C_AWREADY),
        .i3c_axi_awid(S_AXI_I3C_AWID),
        .i3c_axi_awaddr(S_AXI_I3C_AWADDR),
        .i3c_axi_awsize(S_AXI_I3C_AWSIZE),
        .i3c_axi_awprot(S_AXI_I3C_AWPROT),
        .i3c_axi_awlen(S_AXI_I3C_AWLEN),
        .i3c_axi_awburst(S_AXI_I3C_AWBURST),

        .i3c_axi_wvalid(S_AXI_I3C_WVALID),
        .i3c_axi_wready(S_AXI_I3C_WREADY),
        .i3c_axi_wdata(S_AXI_I3C_WDATA),
        .i3c_axi_wstrb(S_AXI_I3C_WSTRB),
        .i3c_axi_wlast(S_AXI_I3C_WLAST),

        .i3c_axi_bvalid(S_AXI_I3C_BVALID),
        .i3c_axi_bready(S_AXI_I3C_BREADY),
        .i3c_axi_bresp(S_AXI_I3C_BRESP),
        .i3c_axi_bid(S_AXI_I3C_BID),


        .i3c_axi_arvalid(S_AXI_I3C_ARVALID),
        .i3c_axi_arready(S_AXI_I3C_ARREADY),
        .i3c_axi_arid(S_AXI_I3C_ARID),
        .i3c_axi_araddr(S_AXI_I3C_ARADDR),
        .i3c_axi_arsize(S_AXI_I3C_ARSIZE),
        .i3c_axi_arprot(S_AXI_I3C_ARPROT),
        .i3c_axi_arlen(S_AXI_I3C_ARLEN),
        .i3c_axi_arburst(S_AXI_I3C_ARBURST),
        
        .i3c_axi_rvalid(S_AXI_I3C_RVALID),
        .i3c_axi_rready(S_AXI_I3C_RREADY),
        .i3c_axi_rid(S_AXI_I3C_RID),
        .i3c_axi_rdata(S_AXI_I3C_RDATA),
        .i3c_axi_rresp(S_AXI_I3C_RRESP),
        .i3c_axi_rlast(S_AXI_I3C_RLAST),

        //.awuser_i(S_AXI_I3C_AWUSER),
        //.awlock_i(S_AXI_I3C_AWLOCK),
        //.aruser_i(S_AXI_I3C_ARUSER),
        //.arlock_i(S_AXI_I3C_ARLOCK),

        // I3C bus IO
`ifdef I3C_OUTSIDE
        .scl_i(scl_i),
        .sda_i(sda_i),
        .scl_o(scl_o),
        .sda_o(sda_o),
        .sel_od_pp_o(sel_od_pp_o)
`else
        .i3c_scl_io(i3c_scl_io),
        .i3c_sda_io(i3c_sda_io)
`endif
*/
    );


localparam DCCM_SIZE        = 14'h0010 ;
localparam DCCM_NUM_BANKS   = 9'h004;
localparam DCCM_DATA_WIDTH  = 10'h020 ;
localparam DCCM_FDATA_WIDTH = 10'h027;
localparam DCCM_BYTE_WIDTH  = 7'h04;
localparam DCCM_INDEX_BITS  = 8'h0A;
localparam DCCM_INDEX_DEPTH = ((DCCM_SIZE)*1024)/((DCCM_BYTE_WIDTH)*(DCCM_NUM_BANKS));
localparam ICCM_SIZE        = 14'h0080;
localparam ICCM_NUM_BANKS   = 9'h004;
localparam ICCM_INDEX_BITS  = 8'h0D;

//////////////////////////////////////////////////////
// DCCM
//
    `define EL2_LOCAL_DCCM_RAM_TEST_PORTS   .TEST1   (1'b0   ), \
                                            .RME     (1'b0   ), \
                                            .RM      (4'b0000), \
                                            .LS      (1'b0   ), \
                                            .DS      (1'b0   ), \
                                            .SD      (1'b0   ), \
                                            .TEST_RNM(1'b0   ), \
                                            .BC1     (1'b0   ), \
                                            .BC2     (1'b0   ), \

    for (genvar i=0; i<DCCM_NUM_BANKS; i++) begin: dccm_loop

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
            css_mcu0_ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
            css_mcu0_ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
            css_mcu0_ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
            css_mcu0_ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
            css_mcu0_ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
            css_mcu0_ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
            css_mcu0_ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
            css_mcu0_ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
            css_mcu0_ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
            css_mcu0_ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(mcu_el2_mem_export.dccm_clken[i]),
                                    .CLK(mcu_el2_mem_export.clk),
                                    .WE(mcu_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(mcu_el2_mem_export.dccm_addr_bank[i]),
                                    .D(mcu_el2_mem_export.dccm_wr_data_bank[i]),
                                    .Q(mcu_el2_mem_export.dccm_bank_dout[i]   ),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
    end : dccm_loop

//////////////////////////////////////////////////////
// ICCM
//

for (genvar i=0; i<ICCM_NUM_BANKS; i++) begin: iccm_loop

    if (ICCM_INDEX_BITS == 6 ) begin : iccm
                css_mcu0_ram_64x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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

    else if (ICCM_INDEX_BITS == 7 ) begin : iccm
                css_mcu0_ram_128x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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

        else if (ICCM_INDEX_BITS == 8 ) begin : iccm
                css_mcu0_ram_256x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 9 ) begin : iccm
                css_mcu0_ram_512x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 10 ) begin : iccm
                css_mcu0_ram_1024x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 11 ) begin : iccm
                css_mcu0_ram_2048x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 12 ) begin : iccm
                css_mcu0_ram_4096x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 13 ) begin : iccm
                css_mcu0_ram_8192x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
        else if (ICCM_INDEX_BITS == 14 ) begin : iccm
                css_mcu0_ram_16384x39 iccm_bank (
                                        // Primary ports
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
                                        .CLK(mcu_el2_mem_export.clk),
                                        .ME(mcu_el2_mem_export.iccm_clken[i]),
                                        .WE(mcu_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(mcu_el2_mem_export.iccm_addr_bank[i]),
                                        .D(mcu_el2_mem_export.iccm_bank_wr_data[i]),
                                        .Q(mcu_el2_mem_export.iccm_bank_dout[i]),
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
end : iccm_loop

    // MCI AXI Subordinate
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mci_s_axi (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_rst_b.value)); // TODO: Fix reset

    // AW
    assign cptra_ss_mci_s_axi.awaddr   = S_AXI_CALIPTRA_AWADDR;
    assign cptra_ss_mci_s_axi.awburst  = S_AXI_CALIPTRA_AWBURST;
    assign cptra_ss_mci_s_axi.awsize   = S_AXI_CALIPTRA_AWSIZE;
    assign cptra_ss_mci_s_axi.awlen    = S_AXI_CALIPTRA_AWLEN;
    assign cptra_ss_mci_s_axi.awuser   = hwif_out.interface_regs.pauser.pauser.value; //S_AXI_CALIPTRA_AWUSER;
    assign cptra_ss_mci_s_axi.awid     = S_AXI_CALIPTRA_AWID;
    assign cptra_ss_mci_s_axi.awlock   = S_AXI_CALIPTRA_AWLOCK;
    assign cptra_ss_mci_s_axi.awvalid  = S_AXI_CALIPTRA_AWVALID;
    assign S_AXI_CALIPTRA_AWREADY = cptra_ss_mci_s_axi.awready;
    // W
    assign cptra_ss_mci_s_axi.wdata    = S_AXI_CALIPTRA_WDATA;
    assign cptra_ss_mci_s_axi.wstrb    = S_AXI_CALIPTRA_WSTRB;
    assign cptra_ss_mci_s_axi.wvalid   = S_AXI_CALIPTRA_WVALID;
    assign S_AXI_CALIPTRA_WREADY = cptra_ss_mci_s_axi.wready;
    assign cptra_ss_mci_s_axi.wlast    = S_AXI_CALIPTRA_WLAST;
    // B
    assign S_AXI_CALIPTRA_BRESP  = cptra_ss_mci_s_axi.bresp;
    assign S_AXI_CALIPTRA_BID    = cptra_ss_mci_s_axi.bid;
    assign S_AXI_CALIPTRA_BVALID = cptra_ss_mci_s_axi.bvalid;
    assign cptra_ss_mci_s_axi.bready  = S_AXI_CALIPTRA_BREADY;
    // AR
    assign cptra_ss_mci_s_axi.araddr  = S_AXI_CALIPTRA_ARADDR;
    assign cptra_ss_mci_s_axi.arburst = S_AXI_CALIPTRA_ARBURST;
    assign cptra_ss_mci_s_axi.arsize  = S_AXI_CALIPTRA_ARSIZE;
    assign cptra_ss_mci_s_axi.arlen   = S_AXI_CALIPTRA_ARLEN;
    assign cptra_ss_mci_s_axi.aruser  = hwif_out.interface_regs.pauser.pauser.value; // S_AXI_CALIPTRA_ARUSER;
    assign cptra_ss_mci_s_axi.arid    = S_AXI_CALIPTRA_ARID;
    assign cptra_ss_mci_s_axi.arlock  = S_AXI_CALIPTRA_ARLOCK;
    assign cptra_ss_mci_s_axi.arvalid = S_AXI_CALIPTRA_ARVALID;
    assign S_AXI_CALIPTRA_ARREADY = cptra_ss_mci_s_axi.arready;
    // R
    assign S_AXI_CALIPTRA_RDATA  = cptra_ss_mci_s_axi.rdata;
    assign S_AXI_CALIPTRA_RRESP  = cptra_ss_mci_s_axi.rresp;
    assign S_AXI_CALIPTRA_RID    = cptra_ss_mci_s_axi.rid;
    assign S_AXI_CALIPTRA_RLAST  = cptra_ss_mci_s_axi.rlast;
    assign S_AXI_CALIPTRA_RVALID = cptra_ss_mci_s_axi.rvalid;
    assign cptra_ss_mci_s_axi.rready = S_AXI_CALIPTRA_RREADY;

    // MCI AXI Manager
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mci_m_axi (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_rst_b.value)); // TODO: Fix reset

    // AW
    assign M_AXI_CALIPTRA_AWADDR =  cptra_ss_mci_m_axi.awaddr;
    assign M_AXI_CALIPTRA_AWBURST = cptra_ss_mci_m_axi.awburst;
    assign M_AXI_CALIPTRA_AWSIZE =  cptra_ss_mci_m_axi.awsize;
    assign M_AXI_CALIPTRA_AWLEN =   cptra_ss_mci_m_axi.awlen;
    assign M_AXI_CALIPTRA_AWUSER =  cptra_ss_mci_m_axi.awuser;
    assign M_AXI_CALIPTRA_AWID = cptra_ss_mci_m_axi.awid;
    assign M_AXI_CALIPTRA_AWLOCK = cptra_ss_mci_m_axi.awlock;
    assign M_AXI_CALIPTRA_AWVALID = cptra_ss_mci_m_axi.awvalid;
    assign cptra_ss_mci_m_axi.awready = M_AXI_CALIPTRA_AWREADY;
    // W
    assign M_AXI_CALIPTRA_WDATA =   cptra_ss_mci_m_axi.wdata;
    assign M_AXI_CALIPTRA_WSTRB =   cptra_ss_mci_m_axi.wstrb;
    assign M_AXI_CALIPTRA_WVALID =  cptra_ss_mci_m_axi.wvalid;
    assign cptra_ss_mci_m_axi.wready = M_AXI_CALIPTRA_WREADY;
    assign M_AXI_CALIPTRA_WLAST =   cptra_ss_mci_m_axi.wlast;
    // B
    assign cptra_ss_mci_m_axi.bresp =    M_AXI_CALIPTRA_BRESP;
    assign cptra_ss_mci_m_axi.bid =      M_AXI_CALIPTRA_BID;
    assign cptra_ss_mci_m_axi.bvalid =   M_AXI_CALIPTRA_BVALID;
    assign M_AXI_CALIPTRA_BREADY = cptra_ss_mci_m_axi.bready;
    // AR
    assign M_AXI_CALIPTRA_ARADDR = cptra_ss_mci_m_axi.araddr;
    assign M_AXI_CALIPTRA_ARBURST = cptra_ss_mci_m_axi.arburst;
    assign M_AXI_CALIPTRA_ARSIZE = cptra_ss_mci_m_axi.arsize;
    assign M_AXI_CALIPTRA_ARLEN = cptra_ss_mci_m_axi.arlen;
    assign M_AXI_CALIPTRA_ARUSER = cptra_ss_mci_m_axi.aruser;
    assign M_AXI_CALIPTRA_ARID = cptra_ss_mci_m_axi.arid;
    assign M_AXI_CALIPTRA_ARLOCK = cptra_ss_mci_m_axi.arlock;
    assign M_AXI_CALIPTRA_ARVALID = cptra_ss_mci_m_axi.arvalid;
    assign cptra_ss_mci_m_axi.arready = M_AXI_CALIPTRA_ARREADY;
    // R
    assign cptra_ss_mci_m_axi.rdata =    M_AXI_CALIPTRA_RDATA;
    assign cptra_ss_mci_m_axi.rresp =    M_AXI_CALIPTRA_RRESP;
    assign cptra_ss_mci_m_axi.rid =      M_AXI_CALIPTRA_RID;
    assign cptra_ss_mci_m_axi.rlast =    M_AXI_CALIPTRA_RLAST;
    assign cptra_ss_mci_m_axi.rvalid =   M_AXI_CALIPTRA_RVALID;
    assign M_AXI_CALIPTRA_RREADY = cptra_ss_mci_m_axi.rready;

    mci_mcu_sram_if cptra_ss_mcu_rom_mbox0_sram_req_if (
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_i)
    );
    
    mci_mcu_sram_if cptra_ss_mcu_rom_mbox1_sram_req_if (
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_i)
    );

    // ----------------- MCI Connections LCC Connections -----------------------
    logic lcc_to_mci_lc_done;
    logic mci_to_lcc_init_req;
    pwrmgr_pkg::pwr_lc_req_t lcc_init_req;
    
    // ----------------- MCI Connections FC Connections -----------------------
    logic [otp_ctrl_reg_pkg::NumAlerts-1:0] fc_alerts;
    logic fc_intr_otp_error;

    // ----------------- MCI OTP Connections -----------------------------------
    logic mci_to_otp_ctrl_init_req;
    logic otp_ctrl_to_mci_otp_ctrl_done;
    pwrmgr_pkg::pwr_otp_req_t otp_ctrl_init_req;

    // TODO: How does this go to MCU?
    // Caliptra SS MCI MCU SRAM Interface (SRAM, MBOX0, MBOX1)
    mci_mcu_sram_if.request cptra_ss_mci_mcu_sram_req_if,
    mci_mcu_sram_if.request cptra_ss_mci_mbox0_sram_req_if,
    mci_mcu_sram_if.request cptra_ss_mci_mbox1_sram_req_if,


    logic mci_intr;
    logic intr_otp_operation_done;

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
        ext_int[`VEER_INTR_VEC_MCI]                 = mci_intr;
        ext_int[`VEER_INTR_VEC_CLP_MBOX_DATA_AVAIL] = mailbox_data_avail;
        ext_int[`VEER_INTR_VEC_I3C]                 = 0;
        ext_int[`VEER_INTR_VEC_FC]                  = intr_otp_operation_done;
        //ext_int = ext_int_tb; //drive from tb if needed
    end

    // MCI
    mci_top #(
        // .MCI_BASE_ADDR(`SOC_MCI_REG_BASE_ADDR), //-- FIXME : Assign common paramter
        .AXI_DATA_WIDTH(32),
        .MCU_SRAM_SIZE_KB(256)
    ) mci_top_i (

        .clk(core_clk),
        .mci_rst_b(hwif_out.interface_regs.control.mci_rst_b.value),
        .mci_pwrgood(hwif_out.interface_regs.control.mci_pwrgood.value), // TODO: A different signal for pwrgood?

        // MCI AXI Interface
        .s_axi_w_if(cptra_ss_mci_s_axi.w_sub),
        .s_axi_r_if(cptra_ss_mci_s_axi.r_sub),

        // MCI Master interface
        .m_axi_w_if(cptra_ss_mci_m_axi.w_mgr),
        .m_axi_r_if(cptra_ss_mci_m_axi.r_mgr),
        
        .strap_mcu_lsu_axi_user(hwif_out.interface_regs.lsu_user.lsu_user.value),
        .strap_mcu_ifu_axi_user(hwif_out.interface_regs.ifu_user.ifu_user.value),
        .strap_clp_axi_user    (hwif_out.interface_regs.clp_user.clp_user.value),

        // -- connects to ss_generic_fw_exec_ctrl (bit 2)
        .mcu_sram_fw_exec_region_lock(mcu_sram_fw_exec_region_lock),

        .agg_error_fatal(1'b0),
        .agg_error_non_fatal(1'b0),

        .mci_error_fatal(hwif_in.fifo_regs.mci_error.mci_error_fatal.next),
        .mci_error_non_fatal(hwif_in.fifo_regs.mci_error.mci_error_non_fatal.next),

        .mci_generic_input_wires({hwif_out.interface_regs.mci_generic_input_wires[0].value.value, hwif_out.interface_regs.mci_generic_input_wires[1].value.value}),
        .mci_generic_output_wires({hwif_in.interface_regs.mci_generic_output_wires[0].value.next, hwif_in.interface_regs.mci_generic_output_wires[1].value.next}),

        .mcu_timer_int(mci_mcu_timer_int),
        .mci_intr(mci_intr),

        .strap_mcu_reset_vector(cptra_ss_strap_mcu_reset_vector_i), // TODO: What is this for? It doesn't connect to the MCU reset_vector in caliptra_ss_top.sv
        
        .mcu_reset_vector(),

        .mcu_no_rom_config(hwif_out.interface_regs.mcu_config.mcu_no_rom_config),

        .nmi_intr(mci_mcu_nmi_int),
        .mcu_nmi_vector(mci_mcu_nmi_vector),

        .mcu_rst_b(mcu_rst_b),
        .cptra_rst_b(/*mcu_cptra_rst_b*/), // TODO: Connect to caliptra

        .mci_boot_seq_brkpoint(hwif_out.interface_regs.mcu_config.cptra_ss_mci_boot_seq_brkpoint_i),

        .lc_done(lcc_to_mci_lc_done), //output from lcc
        .lc_init(mci_to_lcc_init_req), //input to lcc
        // .lc_bus_integ_error_fatal(1'b0),
        // .lc_state_error_fatal(1'b0),
        // .lc_prog_error_fatal(1'b0),

        .fc_opt_done(otp_ctrl_to_mci_otp_ctrl_done), //output from otp
        .fc_opt_init(mci_to_otp_ctrl_init_req), //input to otp
        // .fc_intr_otp_error(1'b0),

        .mci_mcu_sram_req_if  (cptra_ss_mci_mcu_sram_req_if),
        .mci_mbox0_sram_req_if(cptra_ss_mci_mbox0_sram_req_if),
        .mci_mbox1_sram_req_if(cptra_ss_mci_mbox1_sram_req_if),

        .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
        .lc_dft_en_i(lc_dft_en_i),
        .lc_hw_debug_en_i(lc_hw_debug_en_i),

        // Inputs from OTP_Ctrl
        .from_otp_to_lcc_program_i(from_otp_to_lcc_data_i),

        // Inputs from Caliptra_Core
        .ss_dbg_manuf_enable_i(ss_dbg_manuf_enable), // TODO
        .ss_soc_dbg_unlock_level_i(ss_soc_dbg_unlock_level), // TODO

        // Converted Signals from LCC to SoC
        .SOC_DFT_EN(), // TODO output to SOC
        .SOC_HW_DEBUG_EN(), // TODO output to SOC

        // Converted Signals from LCC to Caliptra-core
        .security_state_o(mci_cptra_security_state) // TODO: Connect to Caliptra

    );

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

    // LCC AXI
    //input
    axi_struct_pkg::axi_wr_req_t cptra_ss_lcc_core_axi_wr_req_i;
    assign cptra_ss_lcc_core_axi_wr_req_i.awaddr  = S_AXI_LCC_awaddr;
    assign cptra_ss_lcc_core_axi_wr_req_i.awburst = S_AXI_LCC_awburst;
    assign cptra_ss_lcc_core_axi_wr_req_i.awsize  = S_AXI_LCC_awsize;
    assign cptra_ss_lcc_core_axi_wr_req_i.awlen   = S_AXI_LCC_awlen;
    assign cptra_ss_lcc_core_axi_wr_req_i.awuser  = S_AXI_LCC_awuser;
    assign cptra_ss_lcc_core_axi_wr_req_i.awid    = S_AXI_LCC_awid;
    assign cptra_ss_lcc_core_axi_wr_req_i.awlock  = S_AXI_LCC_awlock;
    assign cptra_ss_lcc_core_axi_wr_req_i.awvalid = S_AXI_LCC_awvalid;
    assign cptra_ss_lcc_core_axi_wr_req_i.wdata   = S_AXI_LCC_wdata;
    assign cptra_ss_lcc_core_axi_wr_req_i.wstrb   = S_AXI_LCC_wstrb;
    assign cptra_ss_lcc_core_axi_wr_req_i.wlast   = S_AXI_LCC_wlast;
    assign cptra_ss_lcc_core_axi_wr_req_i.wvalid  = S_AXI_LCC_wvalid;
    assign cptra_ss_lcc_core_axi_wr_req_i.bready  = S_AXI_LCC_bready;
    //output
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_lcc_core_axi_wr_rsp_o;
    assign S_AXI_LCC_awready = cptra_ss_lcc_core_axi_wr_rsp_o.awready;
    assign S_AXI_LCC_wready  = cptra_ss_lcc_core_axi_wr_rsp_o.wready;
    assign S_AXI_LCC_bresp   = cptra_ss_lcc_core_axi_wr_rsp_o.bresp;
    assign S_AXI_LCC_bid     = cptra_ss_lcc_core_axi_wr_rsp_o.bid;
    assign S_AXI_LCC_bvalid  = cptra_ss_lcc_core_axi_wr_rsp_o.bvalid;

    //input
    axi_struct_pkg::axi_rd_req_t cptra_ss_lcc_core_axi_rd_req_i;
    assign cptra_ss_lcc_core_axi_rd_req_i.araddr  = S_AXI_LCC_araddr;
    assign cptra_ss_lcc_core_axi_rd_req_i.arburst = S_AXI_LCC_arburst;
    assign cptra_ss_lcc_core_axi_rd_req_i.arsize  = S_AXI_LCC_arsize;
    assign cptra_ss_lcc_core_axi_rd_req_i.arlen   = S_AXI_LCC_arlen;
    assign cptra_ss_lcc_core_axi_rd_req_i.aruser  = S_AXI_LCC_aruser;
    assign cptra_ss_lcc_core_axi_rd_req_i.arid    = S_AXI_LCC_arid;
    assign cptra_ss_lcc_core_axi_rd_req_i.arlock  = S_AXI_LCC_arlock;
    assign cptra_ss_lcc_core_axi_rd_req_i.arvalid = S_AXI_LCC_arvalid;
    assign cptra_ss_lcc_core_axi_rd_req_i.rready  = S_AXI_LCC_rready;
    //output
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_lcc_core_axi_rd_rsp_o;
    assign S_AXI_LCC_arready = cptra_ss_lcc_core_axi_rd_rsp_o.arready;
    assign S_AXI_LCC_rdata   = cptra_ss_lcc_core_axi_rd_rsp_o.rdata;
    assign S_AXI_LCC_rresp   = cptra_ss_lcc_core_axi_rd_rsp_o.rresp;
    assign S_AXI_LCC_rid     = cptra_ss_lcc_core_axi_rd_rsp_o.rid;
    assign S_AXI_LCC_rlast   = cptra_ss_lcc_core_axi_rd_rsp_o.rlast;
    assign S_AXI_LCC_rvalid  = cptra_ss_lcc_core_axi_rd_rsp_o.rvalid;

    // Life Cycle Ctrl
    lc_ctrl u_lc_ctrl (
            .clk_i(core_clk),
            .rst_ni(hwif_out.interface_regs.control.lc_rst_ni.value),
            .Allow_RMA_on_PPD(hwif_out.interface_regs.mci_config.cptra_ss_lc_Allow_RMA_on_PPD_i),
            .axi_wr_req(cptra_ss_lc_axi_wr_req_i),
            .axi_wr_rsp(cptra_ss_lc_axi_wr_rsp_o),
            .axi_rd_req(cptra_ss_lc_axi_rd_req_i),
            .axi_rd_rsp(cptra_ss_lc_axi_rd_rsp_o),

            .jtag_i(cptra_ss_lc_ctrl_jtag_i),
            .jtag_o(cptra_ss_lc_ctrl_jtag_o),
            
            .scan_rst_ni(hwif_out.interface_regs.mci_config.cptra_ss_lc_ctrl_scan_rst_ni_i), // cptra_ss_lc_ctrl_scan_rst_ni_i
            
            .scanmode_i(lc_ctrl_scanmode_i),

            .alerts(lc_alerts_o),

            .esc_scrap_state0(cptra_ss_lc_esclate_scrap_state0_i),
            .esc_scrap_state1(cptra_ss_lc_esclate_scrap_state1_i),

            .pwr_lc_i(lcc_init_req),
            .pwr_lc_o(), // Note: It is tied with this assignment: lcc_to_mci_lc_done = pwrmgr_pkg::pwr_lc_rsp_t'(u_lc_ctrl.pwr_lc_o.lc_done);

            .strap_en_override_o(),  // Note: We use VolatileUnlock and so this port is not used in Caliptra-ss, needs to be removed from LCC RTL        

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
            .lc_cpu_en_o(), // Note: this port is not used in Caliptra-ss, needs to be removed from LCC RTL

            .lc_clk_byp_req_o(cptra_ss_lc_clk_byp_req_o),
            .lc_clk_byp_ack_i(cptra_ss_lc_clk_byp_ack_i),

            .otp_device_id_i('0),   // FIXME: This signal should come from FC 
            .otp_manuf_state_i('0), // FIXME: This signal should come from FC 
            .hw_rev_o()             // FIXME: This signal should go to MCI 
        );
    
    assign otp_ctrl_to_mci_otp_ctrl_done = pwrmgr_pkg::pwr_otp_rsp_t'(u_otp_ctrl.pwr_otp_o.otp_done);
    assign otp_ctrl_init_req.otp_init = mci_to_otp_ctrl_init_req; 


    //input
    axi_struct_pkg::axi_wr_req_t cptra_ss_otp_core_axi_wr_req_i;
    assign cptra_ss_otp_core_axi_wr_req_i.awaddr  = S_AXI_OTP_awaddr;
    assign cptra_ss_otp_core_axi_wr_req_i.awburst = S_AXI_OTP_awburst;
    assign cptra_ss_otp_core_axi_wr_req_i.awsize  = S_AXI_OTP_awsize;
    assign cptra_ss_otp_core_axi_wr_req_i.awlen   = S_AXI_OTP_awlen;
    assign cptra_ss_otp_core_axi_wr_req_i.awuser  = S_AXI_OTP_awuser;
    assign cptra_ss_otp_core_axi_wr_req_i.awid    = S_AXI_OTP_awid;
    assign cptra_ss_otp_core_axi_wr_req_i.awlock  = S_AXI_OTP_awlock;
    assign cptra_ss_otp_core_axi_wr_req_i.awvalid = S_AXI_OTP_awvalid;
    assign cptra_ss_otp_core_axi_wr_req_i.wdata   = S_AXI_OTP_wdata;
    assign cptra_ss_otp_core_axi_wr_req_i.wstrb   = S_AXI_OTP_wstrb;
    assign cptra_ss_otp_core_axi_wr_req_i.wlast   = S_AXI_OTP_wlast;
    assign cptra_ss_otp_core_axi_wr_req_i.wvalid  = S_AXI_OTP_wvalid;
    assign cptra_ss_otp_core_axi_wr_req_i.bready  = S_AXI_OTP_bready;
    //output
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_otp_core_axi_wr_rsp_o;
    assign S_AXI_OTP_awready = cptra_ss_otp_core_axi_wr_rsp_o.awready;
    assign S_AXI_OTP_wready  = cptra_ss_otp_core_axi_wr_rsp_o.wready;
    assign S_AXI_OTP_bresp   = cptra_ss_otp_core_axi_wr_rsp_o.bresp;
    assign S_AXI_OTP_bid     = cptra_ss_otp_core_axi_wr_rsp_o.bid;
    assign S_AXI_OTP_bvalid  = cptra_ss_otp_core_axi_wr_rsp_o.bvalid;

    //input
    axi_struct_pkg::axi_rd_req_t cptra_ss_otp_core_axi_rd_req_i;
    assign cptra_ss_otp_core_axi_rd_req_i.araddr  = S_AXI_OTP_araddr;
    assign cptra_ss_otp_core_axi_rd_req_i.arburst = S_AXI_OTP_arburst;
    assign cptra_ss_otp_core_axi_rd_req_i.arsize  = S_AXI_OTP_arsize;
    assign cptra_ss_otp_core_axi_rd_req_i.arlen   = S_AXI_OTP_arlen;
    assign cptra_ss_otp_core_axi_rd_req_i.aruser  = S_AXI_OTP_aruser;
    assign cptra_ss_otp_core_axi_rd_req_i.arid    = S_AXI_OTP_arid;
    assign cptra_ss_otp_core_axi_rd_req_i.arlock  = S_AXI_OTP_arlock;
    assign cptra_ss_otp_core_axi_rd_req_i.arvalid = S_AXI_OTP_arvalid;
    assign cptra_ss_otp_core_axi_rd_req_i.rready  = S_AXI_OTP_rready;
    //output
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_otp_core_axi_rd_rsp_o;
    assign S_AXI_OTP_arready = cptra_ss_otp_core_axi_rd_rsp_o.arready;
    assign S_AXI_OTP_rdata   = cptra_ss_otp_core_axi_rd_rsp_o.rdata;
    assign S_AXI_OTP_rresp   = cptra_ss_otp_core_axi_rd_rsp_o.rresp;
    assign S_AXI_OTP_rid     = cptra_ss_otp_core_axi_rd_rsp_o.rid;
    assign S_AXI_OTP_rlast   = cptra_ss_otp_core_axi_rd_rsp_o.rlast;
    assign S_AXI_OTP_rvalid  = cptra_ss_otp_core_axi_rd_rsp_o.rvalid;



    otp_ctrl_part_pkg::otp_broadcast_t from_otp_to_clpt_core_broadcast,  // This is a struct data type
    
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

    // Fuse Controller
    otp_ctrl #(
        .MemInitFile ("otp-img.2048.vmem")
    ) u_otp_ctrl (
        .clk_i                      (core_clk),
        .rst_ni                     (cptra_ss_rst_b_i),
        .clk_edn_i                  (1'b0), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .rst_edn_ni                 (1'b1), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .edn_o                      (),     // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .edn_i                      ('0),   // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL

        .core_axi_wr_req            (cptra_ss_otp_core_axi_wr_req_i),
        .core_axi_wr_rsp            (cptra_ss_otp_core_axi_wr_rsp_o),
        .core_axi_rd_req            (cptra_ss_otp_core_axi_rd_req_i),
        .core_axi_rd_rsp            (cptra_ss_otp_core_axi_rd_rsp_o),
        
        .prim_tl_i                  (cptra_ss_fuse_macro_prim_tl_i), // TODO: How to connect?
        .prim_tl_o                  (cptra_ss_fuse_macro_prim_tl_o), // TODO: How to connect?

        .intr_otp_operation_done_o  (intr_otp_operation_done),
        .intr_otp_error_o           (fc_intr_otp_error), //TODO: This signal should be connected to MCI
        // .alert_rx_i                 (),
        // .alert_tx_o                 (),
        .alerts(fc_alerts),
        .obs_ctrl_i                 ('0),    //TODO: Needs to be checked
        .otp_obs_o                  (),
        .otp_ast_pwr_seq_o          (),
        .otp_ast_pwr_seq_h_i        ('0),    //TODO: Needs to be checked
        .pwr_otp_i                  (otp_ctrl_init_req),
        .pwr_otp_o                  (),

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


        .otp_keymgr_key_o           (),   // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .flash_otp_key_i            ('0), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .flash_otp_key_o            (),   // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .sram_otp_key_i             ('0), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .sram_otp_key_o             (),   // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .otbn_otp_key_i             ('0), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .otbn_otp_key_o             (),   // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .otp_broadcast_o            (from_otp_to_clpt_core_broadcast),
        .otp_ext_voltage_h_io       ('Z),
        .scan_en_i                  ('0), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .scan_rst_ni                (1'b1), // FIXME: this port is not used in Caliptra-ss, needs to be removed from FC RTL
        .scanmode_i                 (caliptra_prim_mubi_pkg::MuBi4False),
        .cio_test_o                 (),    //TODO: Needs to be checked
        .cio_test_en_o              ()    //TODO: Needs to be checked
	); 

endmodule
