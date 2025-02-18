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
`default_nettype wire

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"

// TODO: This never gets included?
//`include "css_mcu0_el2_pdef.vh"

// TODO: Not sure if axi_struct_pkg needs to be imported. Currently getting errors
//`include "tlul_pkg.sv"
import axi_struct_pkg::*;
import caliptra_fpga_realtime_regs_pkg::*;

module caliptra_wrapper_top #(
    `include "el2_param.vh"
) (
    input bit core_clk,
    input bit i3c_clk,

    // Caliptra S_AXI Interface
    input  wire [31:0] S_AXI_CALIPTRA_AWADDR,
    input  wire [1:0] S_AXI_CALIPTRA_AWBURST,
    input  wire [2:0] S_AXI_CALIPTRA_AWSIZE,
    input  wire [7:0] S_AXI_CALIPTRA_AWLEN,
    input  wire [31:0] S_AXI_CALIPTRA_AWUSER,
    input  wire [15:0] S_AXI_CALIPTRA_AWID,
    input  wire S_AXI_CALIPTRA_AWLOCK,
    input  wire S_AXI_CALIPTRA_AWVALID,
    output wire S_AXI_CALIPTRA_AWREADY,
    // W
    input  wire [31:0] S_AXI_CALIPTRA_WDATA,
    input  wire [3:0] S_AXI_CALIPTRA_WSTRB,
    input  wire S_AXI_CALIPTRA_WVALID,
    output wire S_AXI_CALIPTRA_WREADY,
    input  wire S_AXI_CALIPTRA_WLAST,
    // B
    output wire [1:0] S_AXI_CALIPTRA_BRESP,
    output reg  [15:0] S_AXI_CALIPTRA_BID,
    output wire S_AXI_CALIPTRA_BVALID,
    input  wire S_AXI_CALIPTRA_BREADY,
    // AR
    input  wire [31:0] S_AXI_CALIPTRA_ARADDR,
    input  wire [1:0] S_AXI_CALIPTRA_ARBURST,
    input  wire [2:0] S_AXI_CALIPTRA_ARSIZE,
    input  wire [7:0] S_AXI_CALIPTRA_ARLEN,
    input  wire [31:0] S_AXI_CALIPTRA_ARUSER,
    input  wire [15:0] S_AXI_CALIPTRA_ARID,
    input  wire S_AXI_CALIPTRA_ARLOCK,
    input  wire S_AXI_CALIPTRA_ARVALID,
    output wire S_AXI_CALIPTRA_ARREADY,
    // R
    output wire [31:0] S_AXI_CALIPTRA_RDATA,
    output wire [1:0] S_AXI_CALIPTRA_RRESP,
    output reg  [15:0] S_AXI_CALIPTRA_RID,
    output wire S_AXI_CALIPTRA_RLAST,
    output wire S_AXI_CALIPTRA_RVALID,
    input  wire S_AXI_CALIPTRA_RREADY,

    // Caliptra M_AXI Interface
    output  wire [31:0] M_AXI_CALIPTRA_AWADDR,
    output  wire [1:0] M_AXI_CALIPTRA_AWBURST,
    output  wire [2:0] M_AXI_CALIPTRA_AWSIZE,
    output  wire [7:0] M_AXI_CALIPTRA_AWLEN,
    output  wire [31:0] M_AXI_CALIPTRA_AWUSER,
    output  wire [15:0] M_AXI_CALIPTRA_AWID,
    output  wire M_AXI_CALIPTRA_AWLOCK,
    output  wire M_AXI_CALIPTRA_AWVALID,
    input wire M_AXI_CALIPTRA_AWREADY,
    // W
    output  wire [31:0] M_AXI_CALIPTRA_WDATA,
    output  wire [3:0] M_AXI_CALIPTRA_WSTRB,
    output  wire M_AXI_CALIPTRA_WVALID,
    input wire M_AXI_CALIPTRA_WREADY,
    output  wire M_AXI_CALIPTRA_WLAST,
    // B
    input wire [1:0] M_AXI_CALIPTRA_BRESP,
    input reg  [15:0] M_AXI_CALIPTRA_BID,
    input wire M_AXI_CALIPTRA_BVALID,
    output  wire M_AXI_CALIPTRA_BREADY,
    // AR
    output  wire [31:0] M_AXI_CALIPTRA_ARADDR,
    output  wire [1:0] M_AXI_CALIPTRA_ARBURST,
    output  wire [2:0] M_AXI_CALIPTRA_ARSIZE,
    output  wire [7:0] M_AXI_CALIPTRA_ARLEN,
    output  wire [31:0] M_AXI_CALIPTRA_ARUSER,
    output  wire [15:0] M_AXI_CALIPTRA_ARID,
    output  wire M_AXI_CALIPTRA_ARLOCK,
    output  wire M_AXI_CALIPTRA_ARVALID,
    input wire M_AXI_CALIPTRA_ARREADY,
    // R
    input wire [31:0] M_AXI_CALIPTRA_RDATA,
    input wire [1:0] M_AXI_CALIPTRA_RRESP,
    input reg  [15:0] M_AXI_CALIPTRA_RID,
    input wire M_AXI_CALIPTRA_RLAST,
    input wire M_AXI_CALIPTRA_RVALID,
    output  wire M_AXI_CALIPTRA_RREADY,

    // MCI S_AXI Interface
    input  wire [31:0] S_AXI_MCI_AWADDR,
    input  wire [1:0] S_AXI_MCI_AWBURST,
    input  wire [2:0] S_AXI_MCI_AWSIZE,
    input  wire [7:0] S_AXI_MCI_AWLEN,
    input  wire [31:0] S_AXI_MCI_AWUSER,
    input  wire [15:0] S_AXI_MCI_AWID,
    input  wire S_AXI_MCI_AWLOCK,
    input  wire S_AXI_MCI_AWVALID,
    output wire S_AXI_MCI_AWREADY,
    // W
    input  wire [31:0] S_AXI_MCI_WDATA,
    input  wire [3:0] S_AXI_MCI_WSTRB,
    input  wire S_AXI_MCI_WVALID,
    output wire S_AXI_MCI_WREADY,
    input  wire S_AXI_MCI_WLAST,
    // B
    output wire [1:0] S_AXI_MCI_BRESP,
    output reg  [15:0] S_AXI_MCI_BID,
    output wire S_AXI_MCI_BVALID,
    input  wire S_AXI_MCI_BREADY,
    // AR
    input  wire [31:0] S_AXI_MCI_ARADDR,
    input  wire [1:0] S_AXI_MCI_ARBURST,
    input  wire [2:0] S_AXI_MCI_ARSIZE,
    input  wire [7:0] S_AXI_MCI_ARLEN,
    input  wire [31:0] S_AXI_MCI_ARUSER,
    input  wire [15:0] S_AXI_MCI_ARID,
    input  wire S_AXI_MCI_ARLOCK,
    input  wire S_AXI_MCI_ARVALID,
    output wire S_AXI_MCI_ARREADY,
    // R
    output wire [31:0] S_AXI_MCI_RDATA,
    output wire [1:0] S_AXI_MCI_RRESP,
    output reg  [15:0] S_AXI_MCI_RID,
    output wire S_AXI_MCI_RLAST,
    output wire S_AXI_MCI_RVALID,
    input  wire S_AXI_MCI_RREADY,

    // MCI ROM S_AXI Interface
    input  wire [31:0] S_AXI_MCU_ROM_AWADDR,
    input  wire [1:0] S_AXI_MCU_ROM_AWBURST,
    input  wire [2:0] S_AXI_MCU_ROM_AWSIZE,
    input  wire [7:0] S_AXI_MCU_ROM_AWLEN,
    input  wire [31:0] S_AXI_MCU_ROM_AWUSER,
    input  wire [15:0] S_AXI_MCU_ROM_AWID,
    input  wire S_AXI_MCU_ROM_AWLOCK,
    input  wire S_AXI_MCU_ROM_AWVALID,
    output wire S_AXI_MCU_ROM_AWREADY,
    // W
    input  wire [31:0] S_AXI_MCU_ROM_WDATA,
    input  wire [3:0] S_AXI_MCU_ROM_WSTRB,
    input  wire S_AXI_MCU_ROM_WVALID,
    output wire S_AXI_MCU_ROM_WREADY,
    input  wire S_AXI_MCU_ROM_WLAST,
    // B
    output wire [1:0] S_AXI_MCU_ROM_BRESP,
    output reg  [15:0] S_AXI_MCU_ROM_BID,
    output wire S_AXI_MCU_ROM_BVALID,
    input  wire S_AXI_MCU_ROM_BREADY,
    // AR
    input  wire [31:0] S_AXI_MCU_ROM_ARADDR,
    input  wire [1:0] S_AXI_MCU_ROM_ARBURST,
    input  wire [2:0] S_AXI_MCU_ROM_ARSIZE,
    input  wire [7:0] S_AXI_MCU_ROM_ARLEN,
    input  wire [31:0] S_AXI_MCU_ROM_ARUSER,
    input  wire [15:0] S_AXI_MCU_ROM_ARID,
    input  wire S_AXI_MCU_ROM_ARLOCK,
    input  wire S_AXI_MCU_ROM_ARVALID,
    output wire S_AXI_MCU_ROM_ARREADY,
    // R
    output wire [31:0] S_AXI_MCU_ROM_RDATA,
    output wire [1:0] S_AXI_MCU_ROM_RRESP,
    output reg  [15:0] S_AXI_MCU_ROM_RID,
    output wire S_AXI_MCU_ROM_RLAST,
    output wire S_AXI_MCU_ROM_RVALID,
    input  wire S_AXI_MCU_ROM_RREADY,

    // MCI M_AXI Interface
    output  wire [31:0] M_AXI_MCI_AWADDR,
    output  wire [1:0] M_AXI_MCI_AWBURST,
    output  wire [2:0] M_AXI_MCI_AWSIZE,
    output  wire [7:0] M_AXI_MCI_AWLEN,
    output  wire [31:0] M_AXI_MCI_AWUSER,
    output  wire [15:0] M_AXI_MCI_AWID,
    output  wire M_AXI_MCI_AWLOCK,
    output  wire M_AXI_MCI_AWVALID,
    input wire M_AXI_MCI_AWREADY,
    // W
    output  wire [31:0] M_AXI_MCI_WDATA,
    output  wire [3:0] M_AXI_MCI_WSTRB,
    output  wire M_AXI_MCI_WVALID,
    input wire M_AXI_MCI_WREADY,
    output  wire M_AXI_MCI_WLAST,
    // B
    input wire [1:0] M_AXI_MCI_BRESP,
    input reg  [15:0] M_AXI_MCI_BID,
    input wire M_AXI_MCI_BVALID,
    output  wire M_AXI_MCI_BREADY,
    // AR
    output  wire [31:0] M_AXI_MCI_ARADDR,
    output  wire [1:0] M_AXI_MCI_ARBURST,
    output  wire [2:0] M_AXI_MCI_ARSIZE,
    output  wire [7:0] M_AXI_MCI_ARLEN,
    output  wire [31:0] M_AXI_MCI_ARUSER,
    output  wire [15:0] M_AXI_MCI_ARID,
    output  wire M_AXI_MCI_ARLOCK,
    output  wire M_AXI_MCI_ARVALID,
    input wire M_AXI_MCI_ARREADY,
    // R
    input wire [31:0] M_AXI_MCI_RDATA,
    input wire [1:0] M_AXI_MCI_RRESP,
    input reg  [15:0] M_AXI_MCI_RID,
    input wire M_AXI_MCI_RLAST,
    input wire M_AXI_MCI_RVALID,
    output  wire M_AXI_MCI_RREADY,


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

    // LCC
    input	wire                      S_AXI_LCC_AWVALID,
    output	wire                      S_AXI_LCC_AWREADY,
    input	wire [31:0]               S_AXI_LCC_AWADDR,
    input	wire [2:0]                S_AXI_LCC_AWPROT,
    input	wire                      S_AXI_LCC_WVALID,
    output	wire                      S_AXI_LCC_WREADY,
    input	wire [63:0]               S_AXI_LCC_WDATA,
    input	wire [7:0]                S_AXI_LCC_WSTRB,
    output	wire                      S_AXI_LCC_BVALID,
    input	wire                      S_AXI_LCC_BREADY,
    output	wire [1:0]                S_AXI_LCC_BRESP,
    input	wire                      S_AXI_LCC_ARVALID,
    output	wire                      S_AXI_LCC_ARREADY,
    input	wire [31:0]               S_AXI_LCC_ARADDR,
    input	wire [2:0]                S_AXI_LCC_ARPROT,
    output	wire                      S_AXI_LCC_RVALID,
    input	wire                      S_AXI_LCC_RREADY,
    output	wire [63:0]               S_AXI_LCC_RDATA,
    output	wire [1:0]                S_AXI_LCC_RRESP,
    
    input wire [1:0] S_AXI_LCC_ARBURST,
    input wire [2:0] S_AXI_LCC_ARSIZE,
    input wire [7:0] S_AXI_LCC_ARLEN,
    input wire [31:0] S_AXI_LCC_ARUSER,
    input wire [18:0] S_AXI_LCC_ARID,
    input wire S_AXI_LCC_ARLOCK,
    output wire [18:0]           S_AXI_LCC_RID,
    output wire                   S_AXI_LCC_RLAST,
    input wire [             1:0] S_AXI_LCC_AWBURST,
    input wire [             2:0] S_AXI_LCC_AWSIZE,
    input wire [             7:0] S_AXI_LCC_AWLEN,
    input wire [31:0] S_AXI_LCC_AWUSER,
    input wire [18:0] S_AXI_LCC_AWID,
    input wire                    S_AXI_LCC_AWLOCK,
    input  wire                  S_AXI_LCC_WLAST,
    output wire [18:0] S_AXI_LCC_BID,
    
    // OTP
    input	wire                      S_AXI_OTP_AWVALID,
    output	wire                      S_AXI_OTP_AWREADY,
    input	wire [31:0]               S_AXI_OTP_AWADDR,
    input	wire [2:0]                S_AXI_OTP_AWPROT,
    input	wire                      S_AXI_OTP_WVALID,
    output	wire                      S_AXI_OTP_WREADY,
    input	wire [63:0]               S_AXI_OTP_WDATA,
    input	wire [7:0]                S_AXI_OTP_WSTRB,
    output	wire                      S_AXI_OTP_BVALID,
    input	wire                      S_AXI_OTP_BREADY,
    output	wire [1:0]                S_AXI_OTP_BRESP,
    input	wire                      S_AXI_OTP_ARVALID,
    output	wire                      S_AXI_OTP_ARREADY,
    input	wire [31:0]               S_AXI_OTP_ARADDR,
    input	wire [2:0]                S_AXI_OTP_ARPROT,
    output	wire                      S_AXI_OTP_RVALID,
    input	wire                      S_AXI_OTP_RREADY,
    output	wire [63:0]               S_AXI_OTP_RDATA,
    output	wire [1:0]                S_AXI_OTP_RRESP,
    
    input wire [1:0] S_AXI_OTP_ARBURST,
    input wire [2:0] S_AXI_OTP_ARSIZE,
    input wire [7:0] S_AXI_OTP_ARLEN,
    input wire [31:0] S_AXI_OTP_ARUSER,
    input wire [18:0] S_AXI_OTP_ARID,
    input wire S_AXI_OTP_ARLOCK,
    output wire [18:0]           S_AXI_OTP_RID,
    output wire                   S_AXI_OTP_RLAST,
    input wire [             1:0] S_AXI_OTP_AWBURST,
    input wire [             2:0] S_AXI_OTP_AWSIZE,
    input wire [             7:0] S_AXI_OTP_AWLEN,
    input wire [31:0] S_AXI_OTP_AWUSER,
    input wire [18:0] S_AXI_OTP_AWID,
    input wire                    S_AXI_OTP_AWLOCK,
    input  wire                  S_AXI_OTP_WLAST,
    output wire [18:0] S_AXI_OTP_BID,

    // ROM AXI Interface
    input  logic axi_bram_clk,
    input  logic axi_bram_en,
    input  logic [3:0] axi_bram_we,
    input  logic [14:0] axi_bram_addr,
    input  logic [31:0] axi_bram_wrdata,
    output logic [31:0] axi_bram_rddata,
    input  logic axi_bram_rst,

    // JTAG Interface
    input logic                       jtag_tck,    // JTAG clk
    input logic                       jtag_tms,    // JTAG tms
    input logic                       jtag_tdi,    // JTAG tdi
    input logic                       jtag_trst_n, // JTAG reset
    output logic                      jtag_tdo,    // JTAG tdo

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
    output logic SDA_UP,
    output logic SDA_PUSH,
    output logic SDA_PULL,
    input  logic SDA,
    output logic SCL_UP,
    output logic SCL_PUSH,
    output logic SCL_PULL,
    input  logic SCL
    );

    axi4lite_intf wrapper_s_axil ();

    caliptra_fpga_realtime_regs__in_t hwif_in;
    caliptra_fpga_realtime_regs__out_t hwif_out;

    assign S_AXI_WRAPPER_AWREADY = wrapper_s_axil.AWREADY;
    assign S_AXI_WRAPPER_WREADY = wrapper_s_axil.WREADY;
    assign S_AXI_WRAPPER_BVALID = wrapper_s_axil.BVALID;
    assign S_AXI_WRAPPER_BRESP = wrapper_s_axil.BRESP;
    assign S_AXI_WRAPPER_ARREADY = wrapper_s_axil.ARREADY;
    assign S_AXI_WRAPPER_RVALID = wrapper_s_axil.RVALID;
    assign S_AXI_WRAPPER_RDATA = wrapper_s_axil.RDATA;
    assign S_AXI_WRAPPER_RRESP = wrapper_s_axil.RRESP;

    always_comb begin
        wrapper_s_axil.AWVALID = S_AXI_WRAPPER_AWVALID;
        wrapper_s_axil.AWADDR =  S_AXI_WRAPPER_AWADDR;
        wrapper_s_axil.AWPROT =  S_AXI_WRAPPER_AWPROT;

        wrapper_s_axil.WVALID =  S_AXI_WRAPPER_WVALID;
        wrapper_s_axil.WDATA =   S_AXI_WRAPPER_WDATA;
        wrapper_s_axil.WSTRB =   S_AXI_WRAPPER_WSTRB;

        wrapper_s_axil.BREADY =  S_AXI_WRAPPER_BREADY;

        wrapper_s_axil.ARVALID = S_AXI_WRAPPER_ARVALID;
        wrapper_s_axil.ARADDR =  S_AXI_WRAPPER_ARADDR;
        wrapper_s_axil.ARPROT =  S_AXI_WRAPPER_ARPROT;

        wrapper_s_axil.RREADY =  S_AXI_WRAPPER_RREADY;
    end

    // Register Block
    caliptra_fpga_realtime_regs regs (
        .clk(core_clk),
        .rst(~S_AXI_WRAPPER_ARESETN),

        .s_axil(wrapper_s_axil),

        .hwif_in (hwif_in),
        .hwif_out(hwif_out)
    );

    // TODO: Rearrange this to be more logically located
    logic [127:0] ss_generic_fw_exec_ctrl;
    assign mcu_sram_fw_exec_region_lock = ss_generic_fw_exec_ctrl[2];

    import soc_ifc_pkg::*;

    logic                       BootFSM_BrkPoint;

    logic mbox_sram_cs;
    logic mbox_sram_we;
    logic [14:0] mbox_sram_addr;
    logic [39-1:0] mbox_sram_wdata;
    logic [39-1:0] mbox_sram_rdata;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

`ifndef CALIPTRA_APB
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_core_s_axi (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

    // AW
    assign cptra_core_s_axi.awaddr   = S_AXI_CALIPTRA_AWADDR;
    assign cptra_core_s_axi.awburst  = S_AXI_CALIPTRA_AWBURST;
    assign cptra_core_s_axi.awsize   = S_AXI_CALIPTRA_AWSIZE;
    assign cptra_core_s_axi.awlen    = S_AXI_CALIPTRA_AWLEN;
    assign cptra_core_s_axi.awuser   = hwif_out.interface_regs.pauser.pauser.value; //S_AXI_CALIPTRA_AWUSER;
    assign cptra_core_s_axi.awid     = S_AXI_CALIPTRA_AWID;
    assign cptra_core_s_axi.awlock   = S_AXI_CALIPTRA_AWLOCK;
    assign cptra_core_s_axi.awvalid  = S_AXI_CALIPTRA_AWVALID;
    assign S_AXI_CALIPTRA_AWREADY = cptra_core_s_axi.awready;
    // W
    assign cptra_core_s_axi.wdata    = S_AXI_CALIPTRA_WDATA;
    assign cptra_core_s_axi.wstrb    = S_AXI_CALIPTRA_WSTRB;
    assign cptra_core_s_axi.wvalid   = S_AXI_CALIPTRA_WVALID;
    assign S_AXI_CALIPTRA_WREADY = cptra_core_s_axi.wready;
    assign cptra_core_s_axi.wlast    = S_AXI_CALIPTRA_WLAST;
    // B
    assign S_AXI_CALIPTRA_BRESP  = cptra_core_s_axi.bresp;
    assign S_AXI_CALIPTRA_BID    = cptra_core_s_axi.bid;
    assign S_AXI_CALIPTRA_BVALID = cptra_core_s_axi.bvalid;
    assign cptra_core_s_axi.bready  = S_AXI_CALIPTRA_BREADY;
    // AR
    assign cptra_core_s_axi.araddr  = S_AXI_CALIPTRA_ARADDR;
    assign cptra_core_s_axi.arburst = S_AXI_CALIPTRA_ARBURST;
    assign cptra_core_s_axi.arsize  = S_AXI_CALIPTRA_ARSIZE;
    assign cptra_core_s_axi.arlen   = S_AXI_CALIPTRA_ARLEN;
    assign cptra_core_s_axi.aruser  = hwif_out.interface_regs.pauser.pauser.value; // S_AXI_CALIPTRA_ARUSER;
    assign cptra_core_s_axi.arid    = S_AXI_CALIPTRA_ARID;
    assign cptra_core_s_axi.arlock  = S_AXI_CALIPTRA_ARLOCK;
    assign cptra_core_s_axi.arvalid = S_AXI_CALIPTRA_ARVALID;
    assign S_AXI_CALIPTRA_ARREADY = cptra_core_s_axi.arready;
    // R
    assign S_AXI_CALIPTRA_RDATA  = cptra_core_s_axi.rdata;
    assign S_AXI_CALIPTRA_RRESP  = cptra_core_s_axi.rresp;
    assign S_AXI_CALIPTRA_RID    = cptra_core_s_axi.rid;
    assign S_AXI_CALIPTRA_RLAST  = cptra_core_s_axi.rlast;
    assign S_AXI_CALIPTRA_RVALID = cptra_core_s_axi.rvalid;
    assign cptra_core_s_axi.rready = S_AXI_CALIPTRA_RREADY;

    axi_if #(
        .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_core_m_axi (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

    // AW
    assign M_AXI_CALIPTRA_AWADDR =  cptra_core_m_axi.awaddr;
    assign M_AXI_CALIPTRA_AWBURST = cptra_core_m_axi.awburst;
    assign M_AXI_CALIPTRA_AWSIZE =  cptra_core_m_axi.awsize;
    assign M_AXI_CALIPTRA_AWLEN =   cptra_core_m_axi.awlen;
    assign M_AXI_CALIPTRA_AWUSER =  cptra_core_m_axi.awuser;
    assign M_AXI_CALIPTRA_AWID = cptra_core_m_axi.awid;
    assign M_AXI_CALIPTRA_AWLOCK = cptra_core_m_axi.awlock;
    assign M_AXI_CALIPTRA_AWVALID = cptra_core_m_axi.awvalid;
    assign cptra_core_m_axi.awready = M_AXI_CALIPTRA_AWREADY;
    // W
    assign M_AXI_CALIPTRA_WDATA =   cptra_core_m_axi.wdata;
    assign M_AXI_CALIPTRA_WSTRB =   cptra_core_m_axi.wstrb;
    assign M_AXI_CALIPTRA_WVALID =  cptra_core_m_axi.wvalid;
    assign cptra_core_m_axi.wready = M_AXI_CALIPTRA_WREADY;
    assign M_AXI_CALIPTRA_WLAST =   cptra_core_m_axi.wlast;
    // B
    assign cptra_core_m_axi.bresp =    M_AXI_CALIPTRA_BRESP;
    assign cptra_core_m_axi.bid =      M_AXI_CALIPTRA_BID;
    assign cptra_core_m_axi.bvalid =   M_AXI_CALIPTRA_BVALID;
    assign M_AXI_CALIPTRA_BREADY = cptra_core_m_axi.bready;
    // AR
    assign M_AXI_CALIPTRA_ARADDR = cptra_core_m_axi.araddr;
    assign M_AXI_CALIPTRA_ARBURST = cptra_core_m_axi.arburst;
    assign M_AXI_CALIPTRA_ARSIZE = cptra_core_m_axi.arsize;
    assign M_AXI_CALIPTRA_ARLEN = cptra_core_m_axi.arlen;
    assign M_AXI_CALIPTRA_ARUSER = cptra_core_m_axi.aruser;
    assign M_AXI_CALIPTRA_ARID = cptra_core_m_axi.arid;
    assign M_AXI_CALIPTRA_ARLOCK = cptra_core_m_axi.arlock;
    assign M_AXI_CALIPTRA_ARVALID = cptra_core_m_axi.arvalid;
    assign cptra_core_m_axi.arready = M_AXI_CALIPTRA_ARREADY;
    // R
    assign cptra_core_m_axi.rdata =    M_AXI_CALIPTRA_RDATA;
    assign cptra_core_m_axi.rresp =    M_AXI_CALIPTRA_RRESP;
    assign cptra_core_m_axi.rid =      M_AXI_CALIPTRA_RID;
    assign cptra_core_m_axi.rlast =    M_AXI_CALIPTRA_RLAST;
    assign cptra_core_m_axi.rvalid =   M_AXI_CALIPTRA_RVALID;
    assign M_AXI_CALIPTRA_RREADY = cptra_core_m_axi.rready;


`endif
    el2_mem_if el2_mem_export();
    mldsa_mem_if mldsa_memory_export();

    initial begin
        BootFSM_BrkPoint = 1'b1; //Set to 1 even before anything starts
    end

    // TRNG Interface
    logic etrng_req;
    logic [3:0] itrng_data;
    logic itrng_valid;

// EL2 Memory
caliptra_veer_sram_export veer_sram_export_inst (
    .el2_mem_export(el2_mem_export.veer_sram_sink)
);

mldsa_mem_top mldsa_mem_top_inst (
    .clk_i(core_clk),
    .mldsa_memory_export(mldsa_memory_export.resp)
);

// Mailbox RAM
xpm_memory_spram #(
    .ADDR_WIDTH_A(15),             // DECIMAL
    .AUTO_SLEEP_TIME(0),           // DECIMAL
    .BYTE_WRITE_WIDTH_A(39),       // DECIMAL
    .CASCADE_HEIGHT(0),            // DECIMAL
    .ECC_MODE("no_ecc"),           // String
    .MEMORY_INIT_FILE("none"),     // String
    .MEMORY_INIT_PARAM("0"),       // String
    .MEMORY_OPTIMIZATION("true"),  // String
    .MEMORY_PRIMITIVE("auto"),     // String
    .MEMORY_SIZE(128*1024*8*39/32), // DECIMAL
    .MESSAGE_CONTROL(0),           // DECIMAL
    .READ_DATA_WIDTH_A(39),        // DECIMAL
    .READ_LATENCY_A(1),            // DECIMAL
    .READ_RESET_VALUE_A("0"),      // String
    .RST_MODE_A("SYNC"),           // String
    .SIM_ASSERT_CHK(0),            // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_MEM_INIT(1),              // DECIMAL
    .USE_MEM_INIT_MMI(0),          // DECIMAL
    .WAKEUP_TIME("disable_sleep"), // String
    .WRITE_DATA_WIDTH_A(39),       // DECIMAL
    .WRITE_MODE_A("read_first"),   // String
    .WRITE_PROTECT(1)              // DECIMAL
)
mbox_ram1 (
    .dbiterra(),
    .douta(mbox_sram_rdata),
    .sbiterra(),
    .addra(mbox_sram_addr),
    .clka(core_clk),
    .dina(mbox_sram_wdata),
    .ena(mbox_sram_cs),
    .injectdbiterra(0),
    .injectsbiterra(0),
    .regcea(1'b1),
    .rsta(axi_bram_rst),
    .sleep(0),
    .wea(mbox_sram_we)

);

// SRAM for imem/ROM
xpm_memory_tdpram #(
    .ADDR_WIDTH_A(`CALIPTRA_IMEM_ADDR_WIDTH), // DECIMAL
    .ADDR_WIDTH_B(15),              // DECIMAL
    .AUTO_SLEEP_TIME(0),            // DECIMAL
    .BYTE_WRITE_WIDTH_A(64),        // DECIMAL
    .BYTE_WRITE_WIDTH_B(8),         // DECIMAL
    .CASCADE_HEIGHT(0),             // DECIMAL
    .CLOCKING_MODE("common_clock"), // String
    .ECC_MODE("no_ecc"),            // String
    .MEMORY_INIT_FILE("none"),      // String
    .MEMORY_INIT_PARAM("0"),        // String
    .MEMORY_OPTIMIZATION("false"),  // String
    .MEMORY_PRIMITIVE("auto"),      // String
    .MEMORY_SIZE(96*1024*8),        // DECIMAL
    .MESSAGE_CONTROL(0),            // DECIMAL
    .READ_DATA_WIDTH_A(64),         // DECIMAL
    .READ_DATA_WIDTH_B(32),         // DECIMAL
    .READ_LATENCY_A(1),             // DECIMAL
    .READ_LATENCY_B(1),             // DECIMAL
    .READ_RESET_VALUE_A("0"),       // String
    .READ_RESET_VALUE_B("0"),       // String
    .RST_MODE_A("SYNC"),            // String
    .RST_MODE_B("SYNC"),            // String
    .SIM_ASSERT_CHK(0),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
    .USE_MEM_INIT(1),               // DECIMAL
    .USE_MEM_INIT_MMI(0),           // DECIMAL
    .WAKEUP_TIME("disable_sleep"),  // String
    .WRITE_DATA_WIDTH_A(64),        // DECIMAL
    .WRITE_DATA_WIDTH_B(32),        // DECIMAL
    .WRITE_MODE_A("no_change"),     // String
    .WRITE_MODE_B("no_change"),     // String
    .WRITE_PROTECT(1)               // DECIMAL
)
imem_inst1 (
    .dbiterra(),
    .dbiterrb(),
    .douta(imem_rdata),
    .doutb(axi_bram_rddata),
    .sbiterra(),
    .sbiterrb(),
    .addra(imem_addr),
    .addrb(axi_bram_addr),
    .clka(core_clk),
    .clkb(core_clk),
    .dina(0),
    .dinb(axi_bram_wrdata),
    .ena(imem_cs),
    .enb(axi_bram_en),
    .injectdbiterra(0),
    .injectdbiterrb(0),
    .injectsbiterra(0),
    .injectsbiterrb(0),
    .regcea(1),
    .regceb(1),
    .rsta(axi_bram_rst),
    .rstb(axi_bram_rst),
    .sleep(0),
    .wea(8'h0),
    .web(axi_bram_we)
);

// Valid = !Empty
logic log_fifo_empty;
assign hwif_in.fifo_regs.log_fifo_data.char_valid.next = ~log_fifo_empty;
assign hwif_in.fifo_regs.log_fifo_status.log_fifo_empty.next = log_fifo_empty;

// When rd_swacc is asserted, use the value of "valid" from when it was sampled.
reg log_fifo_valid_f;
always@(posedge core_clk) begin
    log_fifo_valid_f <= ~log_fifo_empty;
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
    .din(fifo_char),
    .injectdbiterr(0),
    .injectsbiterr(0),
    .rd_en(log_fifo_valid_f & hwif_out.fifo_regs.log_fifo_data.next_char.rd_swacc),
    .rst(~S_AXI_WRAPPER_ARESETN),
    .sleep(0),
    .wr_clk(core_clk),
    .wr_en(fifo_write_en)
);


`ifdef CALIPTRA_INTERNAL_TRNG
// Registers and FIFO for ITRNG entropy

reg throttled_etrng_req;
// wr_swacc is asserted one cycle before the hwif_out has the new value. Delay wr_en by one cycle.
reg trng_fifo_wr_en;
always@(posedge core_clk) begin
    trng_fifo_wr_en <= hwif_out.fifo_regs.itrng_fifo_data.itrng_data.wr_swacc;
end

xpm_fifo_sync #(
    .CASCADE_HEIGHT(0),         // DECIMAL
    .DOUT_RESET_VALUE("0"),     // String
    .ECC_MODE("no_ecc"),        // String
    .FIFO_MEMORY_TYPE("block"), // String
    .FIFO_READ_LATENCY(1),      // DECIMAL
    .FIFO_WRITE_DEPTH(1024),    // DECIMAL
    .FULL_RESET_VALUE(0),       // DECIMAL
    .PROG_EMPTY_THRESH(10),     // DECIMAL
    .PROG_FULL_THRESH(10),      // DECIMAL
    .RD_DATA_COUNT_WIDTH(13),   // DECIMAL
    .READ_DATA_WIDTH(4),        // DECIMAL
    .READ_MODE("std"),          // String
    .SIM_ASSERT_CHK(0),         // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
    .USE_ADV_FEATURES("1000"),  // String
    .WAKEUP_TIME(0),            // DECIMAL
    .WRITE_DATA_WIDTH(32),      // DECIMAL
    .WR_DATA_COUNT_WIDTH(11)    // DECIMAL
)
trng_fifo_inst (
    .almost_empty(),
    .almost_full(),
    .data_valid(itrng_valid),
    .dbiterr(),
    .dout(itrng_data),
    .empty(hwif_in.fifo_regs.itrng_fifo_status.itrng_fifo_empty.next),
    .full(hwif_in.fifo_regs.itrng_fifo_status.itrng_fifo_full.next),
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
    .din(hwif_out.fifo_regs.itrng_fifo_data.itrng_data.value),
    .injectdbiterr(0),
    .injectsbiterr(0),
    .rd_en(throttled_etrng_req),
    .rst(hwif_out.fifo_regs.itrng_fifo_status.itrng_fifo_reset.value),
    .sleep(0),
    .wr_clk(core_clk),
    .wr_en(trng_fifo_wr_en)
);

    // Throttle etrng_req.
    reg [31:0] counter;
    always@(posedge core_clk) begin
        if (counter == 0) begin
            throttled_etrng_req <= etrng_req;
            counter <= hwif_out.interface_regs.itrng_divisor.itrng_divisor.value;
        end else begin
            throttled_etrng_req <= 0;
            counter <= counter - 1;
        end
    end
`else
// ETRNG case
    assign itrng_data  = 4'b0;
    assign itrng_valid = 1'b0;
`endif

// Track how many cycles Caliptra has been out of reset for timestamping events
// TODO: Changed this to track ss reset because ctpra_rst_b no longer in scope. Should this still track that signal using xmr?
reg [31:0] cycle_count;
always@(posedge core_clk or negedge hwif_out.interface_regs.control.cptra_ss_rst_b.value) begin
    if (~hwif_out.interface_regs.control.cptra_ss_rst_b.value) begin
        cycle_count <= 0;
    end
    else begin
        cycle_count <= cycle_count + 1;
    end
end
assign hwif_in.interface_regs.cycle_count.cycle_count.next = cycle_count;

// Set the fpga_version register with the git id of the repo state
assign hwif_in.interface_regs.fpga_version.fpga_version.next = `FPGA_VERSION;


// MCI AXI Subordinate
axi_if #(
    .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
    .DW(`CALIPTRA_AXI_DATA_WIDTH),
    .IW(`CALIPTRA_AXI_ID_WIDTH),
    .UW(`CALIPTRA_AXI_USER_WIDTH)
) cptra_ss_mci_s_axi (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

// AW
assign cptra_ss_mci_s_axi.awaddr   = S_AXI_MCI_AWADDR;
assign cptra_ss_mci_s_axi.awburst  = S_AXI_MCI_AWBURST;
assign cptra_ss_mci_s_axi.awsize   = S_AXI_MCI_AWSIZE;
assign cptra_ss_mci_s_axi.awlen    = S_AXI_MCI_AWLEN;
assign cptra_ss_mci_s_axi.awuser   = hwif_out.interface_regs.pauser.pauser.value; //S_AXI_MCI_AWUSER;
assign cptra_ss_mci_s_axi.awid     = S_AXI_MCI_AWID;
assign cptra_ss_mci_s_axi.awlock   = S_AXI_MCI_AWLOCK;
assign cptra_ss_mci_s_axi.awvalid  = S_AXI_MCI_AWVALID;
assign S_AXI_MCI_AWREADY = cptra_ss_mci_s_axi.awready;
// W
assign cptra_ss_mci_s_axi.wdata    = S_AXI_MCI_WDATA;
assign cptra_ss_mci_s_axi.wstrb    = S_AXI_MCI_WSTRB;
assign cptra_ss_mci_s_axi.wvalid   = S_AXI_MCI_WVALID;
assign S_AXI_MCI_WREADY = cptra_ss_mci_s_axi.wready;
assign cptra_ss_mci_s_axi.wlast    = S_AXI_MCI_WLAST;
// B
assign S_AXI_MCI_BRESP  = cptra_ss_mci_s_axi.bresp;
assign S_AXI_MCI_BID    = cptra_ss_mci_s_axi.bid;
assign S_AXI_MCI_BVALID = cptra_ss_mci_s_axi.bvalid;
assign cptra_ss_mci_s_axi.bready  = S_AXI_MCI_BREADY;
// AR
assign cptra_ss_mci_s_axi.araddr  = S_AXI_MCI_ARADDR;
assign cptra_ss_mci_s_axi.arburst = S_AXI_MCI_ARBURST;
assign cptra_ss_mci_s_axi.arsize  = S_AXI_MCI_ARSIZE;
assign cptra_ss_mci_s_axi.arlen   = S_AXI_MCI_ARLEN;
assign cptra_ss_mci_s_axi.aruser  = hwif_out.interface_regs.pauser.pauser.value; // S_AXI_MCI_ARUSER;
assign cptra_ss_mci_s_axi.arid    = S_AXI_MCI_ARID;
assign cptra_ss_mci_s_axi.arlock  = S_AXI_MCI_ARLOCK;
assign cptra_ss_mci_s_axi.arvalid = S_AXI_MCI_ARVALID;
assign S_AXI_MCI_ARREADY = cptra_ss_mci_s_axi.arready;
// R
assign S_AXI_MCI_RDATA  = cptra_ss_mci_s_axi.rdata;
assign S_AXI_MCI_RRESP  = cptra_ss_mci_s_axi.rresp;
assign S_AXI_MCI_RID    = cptra_ss_mci_s_axi.rid;
assign S_AXI_MCI_RLAST  = cptra_ss_mci_s_axi.rlast;
assign S_AXI_MCI_RVALID = cptra_ss_mci_s_axi.rvalid;
assign cptra_ss_mci_s_axi.rready = S_AXI_MCI_RREADY;

// MCU ROM AXI Subordinate
axi_if #(
    .AW(32),
    .DW(`CALIPTRA_AXI_DATA_WIDTH),
    .IW(`CALIPTRA_AXI_ID_WIDTH),
    .UW(`CALIPTRA_AXI_USER_WIDTH)
) cptra_ss_mcu_rom_s_axi_if (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

// AW
assign cptra_ss_mcu_rom_s_axi_if.awaddr   = S_AXI_MCU_ROM_AWADDR;
assign cptra_ss_mcu_rom_s_axi_if.awburst  = S_AXI_MCU_ROM_AWBURST;
assign cptra_ss_mcu_rom_s_axi_if.awsize   = S_AXI_MCU_ROM_AWSIZE;
assign cptra_ss_mcu_rom_s_axi_if.awlen    = S_AXI_MCU_ROM_AWLEN;
assign cptra_ss_mcu_rom_s_axi_if.awuser   = hwif_out.interface_regs.pauser.pauser.value; //S_AXI_MCU_ROM_AWUSER;
assign cptra_ss_mcu_rom_s_axi_if.awid     = S_AXI_MCU_ROM_AWID;
assign cptra_ss_mcu_rom_s_axi_if.awlock   = S_AXI_MCU_ROM_AWLOCK;
assign cptra_ss_mcu_rom_s_axi_if.awvalid  = S_AXI_MCU_ROM_AWVALID;
assign S_AXI_MCU_ROM_AWREADY = cptra_ss_mcu_rom_s_axi_if.awready;
// W
assign cptra_ss_mcu_rom_s_axi_if.wdata    = S_AXI_MCU_ROM_WDATA;
assign cptra_ss_mcu_rom_s_axi_if.wstrb    = S_AXI_MCU_ROM_WSTRB;
assign cptra_ss_mcu_rom_s_axi_if.wvalid   = S_AXI_MCU_ROM_WVALID;
assign S_AXI_MCU_ROM_WREADY = cptra_ss_mcu_rom_s_axi_if.wready;
assign cptra_ss_mcu_rom_s_axi_if.wlast    = S_AXI_MCU_ROM_WLAST;
// B
assign S_AXI_MCU_ROM_BRESP  = cptra_ss_mcu_rom_s_axi_if.bresp;
assign S_AXI_MCU_ROM_BID    = cptra_ss_mcu_rom_s_axi_if.bid;
assign S_AXI_MCU_ROM_BVALID = cptra_ss_mcu_rom_s_axi_if.bvalid;
assign cptra_ss_mcu_rom_s_axi_if.bready  = S_AXI_MCU_ROM_BREADY;
// AR
assign cptra_ss_mcu_rom_s_axi_if.araddr  = S_AXI_MCU_ROM_ARADDR;
assign cptra_ss_mcu_rom_s_axi_if.arburst = S_AXI_MCU_ROM_ARBURST;
assign cptra_ss_mcu_rom_s_axi_if.arsize  = S_AXI_MCU_ROM_ARSIZE;
assign cptra_ss_mcu_rom_s_axi_if.arlen   = S_AXI_MCU_ROM_ARLEN;
assign cptra_ss_mcu_rom_s_axi_if.aruser  = hwif_out.interface_regs.pauser.pauser.value; // S_AXI_MCU_ROM_ARUSER;
assign cptra_ss_mcu_rom_s_axi_if.arid    = S_AXI_MCU_ROM_ARID;
assign cptra_ss_mcu_rom_s_axi_if.arlock  = S_AXI_MCU_ROM_ARLOCK;
assign cptra_ss_mcu_rom_s_axi_if.arvalid = S_AXI_MCU_ROM_ARVALID;
assign S_AXI_MCU_ROM_ARREADY = cptra_ss_mcu_rom_s_axi_if.arready;
// R
assign S_AXI_MCU_ROM_RDATA  = cptra_ss_mcu_rom_s_axi_if.rdata;
assign S_AXI_MCU_ROM_RRESP  = cptra_ss_mcu_rom_s_axi_if.rresp;
assign S_AXI_MCU_ROM_RID    = cptra_ss_mcu_rom_s_axi_if.rid;
assign S_AXI_MCU_ROM_RLAST  = cptra_ss_mcu_rom_s_axi_if.rlast;
assign S_AXI_MCU_ROM_RVALID = cptra_ss_mcu_rom_s_axi_if.rvalid;
assign cptra_ss_mcu_rom_s_axi_if.rready = S_AXI_MCU_ROM_RREADY;

// MCU ROM
axi_mem_if #(
   .ADDR_WIDTH(32),
   .DATA_WIDTH(64)
) mcu_rom_mem_export_if (
   .clk(core_clk),
   .rst_b(hwif_out.interface_regs.control.cptra_ss_rst_b.value)
);

xpm_memory_spram #(
   .ADDR_WIDTH_A(32),              // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(64),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("false"),  // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(64*1024*8),        // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_A(64),         // DECIMAL
   .READ_LATENCY_A(1),             // DECIMAL
   .READ_RESET_VALUE_A("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .SIM_ASSERT_CHK(0),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(64),        // DECIMAL
   .WRITE_MODE_A("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
mcu_rom (
   .dbiterra(),
   .douta(mcu_rom_mem_export_if.resp.rdata),
   .sbiterra(),
   .addra(mcu_rom_mem_export_if.req.addr),
   .clka(core_clk),
   .dina(mcu_rom_mem_export_if.req.wdata),
   .ena(mcu_rom_mem_export_if.req.cs),
   .injectdbiterra(0),
   .injectsbiterra(0),
   .regcea(1),
   .rsta(ss_axi_bram_rst),
   .sleep(0),
   .wea(mcu_rom_mem_export_if.req.we)
);

// MCI AXI Manager
axi_if #(
   .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
   .DW(`CALIPTRA_AXI_DATA_WIDTH),
   .IW(`CALIPTRA_AXI_ID_WIDTH),
   .UW(`CALIPTRA_AXI_USER_WIDTH)
) cptra_ss_mci_m_axi_if (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

// AW
assign M_AXI_MCI_AWADDR =  cptra_ss_mci_m_axi_if.awaddr;
assign M_AXI_MCI_AWBURST = cptra_ss_mci_m_axi_if.awburst;
assign M_AXI_MCI_AWSIZE =  cptra_ss_mci_m_axi_if.awsize;
assign M_AXI_MCI_AWLEN =   cptra_ss_mci_m_axi_if.awlen;
assign M_AXI_MCI_AWUSER =  cptra_ss_mci_m_axi_if.awuser;
assign M_AXI_MCI_AWID = cptra_ss_mci_m_axi_if.awid;
assign M_AXI_MCI_AWLOCK = cptra_ss_mci_m_axi_if.awlock;
assign M_AXI_MCI_AWVALID = cptra_ss_mci_m_axi_if.awvalid;
assign cptra_ss_mci_m_axi_if.awready = M_AXI_MCI_AWREADY;
// W
assign M_AXI_MCI_WDATA =   cptra_ss_mci_m_axi_if.wdata;
assign M_AXI_MCI_WSTRB =   cptra_ss_mci_m_axi_if.wstrb;
assign M_AXI_MCI_WVALID =  cptra_ss_mci_m_axi_if.wvalid;
assign cptra_ss_mci_m_axi_if.wready = M_AXI_MCI_WREADY;
assign M_AXI_MCI_WLAST =   cptra_ss_mci_m_axi_if.wlast;
// B
assign cptra_ss_mci_m_axi_if.bresp =    M_AXI_MCI_BRESP;
assign cptra_ss_mci_m_axi_if.bid =      M_AXI_MCI_BID;
assign cptra_ss_mci_m_axi_if.bvalid =   M_AXI_MCI_BVALID;
assign M_AXI_MCI_BREADY = cptra_ss_mci_m_axi_if.bready;
// AR
assign M_AXI_MCI_ARADDR = cptra_ss_mci_m_axi_if.araddr;
assign M_AXI_MCI_ARBURST = cptra_ss_mci_m_axi_if.arburst;
assign M_AXI_MCI_ARSIZE = cptra_ss_mci_m_axi_if.arsize;
assign M_AXI_MCI_ARLEN = cptra_ss_mci_m_axi_if.arlen;
assign M_AXI_MCI_ARUSER = cptra_ss_mci_m_axi_if.aruser;
assign M_AXI_MCI_ARID = cptra_ss_mci_m_axi_if.arid;
assign M_AXI_MCI_ARLOCK = cptra_ss_mci_m_axi_if.arlock;
assign M_AXI_MCI_ARVALID = cptra_ss_mci_m_axi_if.arvalid;
assign cptra_ss_mci_m_axi_if.arready = M_AXI_MCI_ARREADY;
// R
assign cptra_ss_mci_m_axi_if.rdata =    M_AXI_MCI_RDATA;
assign cptra_ss_mci_m_axi_if.rresp =    M_AXI_MCI_RRESP;
assign cptra_ss_mci_m_axi_if.rid =      M_AXI_MCI_RID;
assign cptra_ss_mci_m_axi_if.rlast =    M_AXI_MCI_RLAST;
assign cptra_ss_mci_m_axi_if.rvalid =   M_AXI_MCI_RVALID;
assign M_AXI_MCI_RREADY = cptra_ss_mci_m_axi_if.rready;

// TODO: Connect these?
mci_mcu_sram_if cptra_ss_mcu_rom_macro_req_if (
    .clk(core_clk),
    .rst_b(rst_l)
);

//    xpm_memory_spram #(
//        .ADDR_WIDTH_A(32),              // DECIMAL
//        .AUTO_SLEEP_TIME(0),            // DECIMAL
//        .BYTE_WRITE_WIDTH_A(32),        // DECIMAL
//        .CASCADE_HEIGHT(0),             // DECIMAL
//        .ECC_MODE("no_ecc"),            // String
//        .MEMORY_INIT_FILE("none"),      // String
//        .MEMORY_INIT_PARAM("0"),        // String
//        .MEMORY_OPTIMIZATION("false"),  // String
//        .MEMORY_PRIMITIVE("auto"),      // String
//        .MEMORY_SIZE(1024*1024*8),      // DECIMAL
//        .MESSAGE_CONTROL(0),            // DECIMAL
//        .READ_DATA_WIDTH_A(32),         // DECIMAL
//        .READ_LATENCY_A(1),             // DECIMAL
//        .READ_RESET_VALUE_A("0"),       // String
//        .RST_MODE_A("SYNC"),            // String
//        .SIM_ASSERT_CHK(0),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
//        .USE_MEM_INIT(1),               // DECIMAL
//        .USE_MEM_INIT_MMI(0),           // DECIMAL
//        .WAKEUP_TIME("disable_sleep"),  // String
//        .WRITE_DATA_WIDTH_A(32),        // DECIMAL
//        .WRITE_MODE_A("no_change"),     // String
//        .WRITE_PROTECT(1)               // DECIMAL
//    )
//    mcu_sram (
//        .dbiterra(),
//        .douta(ss_axi_bram_dout),
//        .sbiterra(),
//        .addra(ss_axi_bram_addr),
//        .clka(core_clk),
//        .dina(ss_axi_bram_din),
//        .ena(ss_axi_bram_en),
//        .injectdbiterra(0),
//        .injectsbiterra(0),
//        .regcea(1),
//        .rsta(ss_axi_bram_rst),
//        .sleep(0),
//        .wea(ss_axi_bram_we)
//    );

    mci_mcu_sram_if cptra_ss_mci_mcu_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );

    mci_mcu_sram_if cptra_ss_mci_mbox0_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );
    
    mci_mcu_sram_if cptra_ss_mci_mbox1_sram_req_if (
        .clk(core_clk),
        .rst_b(rst_l)
    );
    
    // MCU LSU AXI Manager
    axi_if #(
        .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_lsu_m_axi_if (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

    // AW
    assign M_AXI_MCU_LSU_AWADDR =  cptra_ss_mcu_lsu_m_axi_if.awaddr;
    assign M_AXI_MCU_LSU_AWBURST = cptra_ss_mcu_lsu_m_axi_if.awburst;
    assign M_AXI_MCU_LSU_AWSIZE =  cptra_ss_mcu_lsu_m_axi_if.awsize;
    assign M_AXI_MCU_LSU_AWLEN =   cptra_ss_mcu_lsu_m_axi_if.awlen;
    assign M_AXI_MCU_LSU_AWUSER =  cptra_ss_mcu_lsu_m_axi_if.awuser;
    assign M_AXI_MCU_LSU_AWID = cptra_ss_mcu_lsu_m_axi_if.awid;
    assign M_AXI_MCU_LSU_AWLOCK = cptra_ss_mcu_lsu_m_axi_if.awlock;
    assign M_AXI_MCU_LSU_AWVALID = cptra_ss_mcu_lsu_m_axi_if.awvalid;
    assign cptra_ss_mcu_lsu_m_axi_if.awready = M_AXI_MCU_LSU_AWREADY;
    // W
    assign M_AXI_MCU_LSU_WDATA =   cptra_ss_mcu_lsu_m_axi_if.wdata;
    assign M_AXI_MCU_LSU_WSTRB =   cptra_ss_mcu_lsu_m_axi_if.wstrb;
    assign M_AXI_MCU_LSU_WVALID =  cptra_ss_mcu_lsu_m_axi_if.wvalid;
    assign cptra_ss_mcu_lsu_m_axi_if.wready = M_AXI_MCU_LSU_WREADY;
    assign M_AXI_MCU_LSU_WLAST =   cptra_ss_mcu_lsu_m_axi_if.wlast;
    // B
    assign cptra_ss_mcu_lsu_m_axi_if.bresp =    M_AXI_MCU_LSU_BRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.bid =      M_AXI_MCU_LSU_BID;
    assign cptra_ss_mcu_lsu_m_axi_if.bvalid =   M_AXI_MCU_LSU_BVALID;
    assign M_AXI_MCU_LSU_BREADY = cptra_ss_mcu_lsu_m_axi_if.bready;
    // AR
    assign M_AXI_MCU_LSU_ARADDR = cptra_ss_mcu_lsu_m_axi_if.araddr;
    assign M_AXI_MCU_LSU_ARBURST = cptra_ss_mcu_lsu_m_axi_if.arburst;
    assign M_AXI_MCU_LSU_ARSIZE = cptra_ss_mcu_lsu_m_axi_if.arsize;
    assign M_AXI_MCU_LSU_ARLEN = cptra_ss_mcu_lsu_m_axi_if.arlen;
    assign M_AXI_MCU_LSU_ARUSER = cptra_ss_mcu_lsu_m_axi_if.aruser;
    assign M_AXI_MCU_LSU_ARID = cptra_ss_mcu_lsu_m_axi_if.arid;
    assign M_AXI_MCU_LSU_ARLOCK = cptra_ss_mcu_lsu_m_axi_if.arlock;
    assign M_AXI_MCU_LSU_ARVALID = cptra_ss_mcu_lsu_m_axi_if.arvalid;
    assign cptra_ss_mcu_lsu_m_axi_if.arready = M_AXI_MCU_LSU_ARREADY;
    // R
    assign cptra_ss_mcu_lsu_m_axi_if.rdata =    M_AXI_MCU_LSU_RDATA;
    assign cptra_ss_mcu_lsu_m_axi_if.rresp =    M_AXI_MCU_LSU_RRESP;
    assign cptra_ss_mcu_lsu_m_axi_if.rid =      M_AXI_MCU_LSU_RID;
    assign cptra_ss_mcu_lsu_m_axi_if.rlast =    M_AXI_MCU_LSU_RLAST;
    assign cptra_ss_mcu_lsu_m_axi_if.rvalid =   M_AXI_MCU_LSU_RVALID;
    assign M_AXI_MCU_LSU_RREADY = cptra_ss_mcu_lsu_m_axi_if.rready;

    // MCU IFU AXI Manager
    axi_if #(
        .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_mcu_ifu_m_axi_if (.clk(core_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

    // AW
    assign M_AXI_MCU_IFU_AWADDR =  cptra_ss_mcu_ifu_m_axi_if.awaddr;
    assign M_AXI_MCU_IFU_AWBURST = cptra_ss_mcu_ifu_m_axi_if.awburst;
    assign M_AXI_MCU_IFU_AWSIZE =  cptra_ss_mcu_ifu_m_axi_if.awsize;
    assign M_AXI_MCU_IFU_AWLEN =   cptra_ss_mcu_ifu_m_axi_if.awlen;
    assign M_AXI_MCU_IFU_AWUSER =  cptra_ss_mcu_ifu_m_axi_if.awuser;
    assign M_AXI_MCU_IFU_AWID = cptra_ss_mcu_ifu_m_axi_if.awid;
    assign M_AXI_MCU_IFU_AWLOCK = cptra_ss_mcu_ifu_m_axi_if.awlock;
    assign M_AXI_MCU_IFU_AWVALID = cptra_ss_mcu_ifu_m_axi_if.awvalid;
    assign cptra_ss_mcu_ifu_m_axi_if.awready = M_AXI_MCU_IFU_AWREADY;
    // W
    assign M_AXI_MCU_IFU_WDATA =   cptra_ss_mcu_ifu_m_axi_if.wdata;
    assign M_AXI_MCU_IFU_WSTRB =   cptra_ss_mcu_ifu_m_axi_if.wstrb;
    assign M_AXI_MCU_IFU_WVALID =  cptra_ss_mcu_ifu_m_axi_if.wvalid;
    assign cptra_ss_mcu_ifu_m_axi_if.wready = M_AXI_MCU_IFU_WREADY;
    assign M_AXI_MCU_IFU_WLAST =   cptra_ss_mcu_ifu_m_axi_if.wlast;
    // B
    assign cptra_ss_mcu_ifu_m_axi_if.bresp =    M_AXI_MCU_IFU_BRESP;
    assign cptra_ss_mcu_ifu_m_axi_if.bid =      M_AXI_MCU_IFU_BID;
    assign cptra_ss_mcu_ifu_m_axi_if.bvalid =   M_AXI_MCU_IFU_BVALID;
    assign M_AXI_MCU_IFU_BREADY = cptra_ss_mcu_ifu_m_axi_if.bready;
    // AR
    assign M_AXI_MCU_IFU_ARADDR = cptra_ss_mcu_ifu_m_axi_if.araddr;
    assign M_AXI_MCU_IFU_ARBURST = cptra_ss_mcu_ifu_m_axi_if.arburst;
    assign M_AXI_MCU_IFU_ARSIZE = cptra_ss_mcu_ifu_m_axi_if.arsize;
    assign M_AXI_MCU_IFU_ARLEN = cptra_ss_mcu_ifu_m_axi_if.arlen;
    assign M_AXI_MCU_IFU_ARUSER = cptra_ss_mcu_ifu_m_axi_if.aruser;
    assign M_AXI_MCU_IFU_ARID = cptra_ss_mcu_ifu_m_axi_if.arid;
    assign M_AXI_MCU_IFU_ARLOCK = cptra_ss_mcu_ifu_m_axi_if.arlock;
    assign M_AXI_MCU_IFU_ARVALID = cptra_ss_mcu_ifu_m_axi_if.arvalid;
    assign cptra_ss_mcu_ifu_m_axi_if.arready = M_AXI_MCU_IFU_ARREADY;
    // R
    assign cptra_ss_mcu_ifu_m_axi_if.rdata =    M_AXI_MCU_IFU_RDATA;
    assign cptra_ss_mcu_ifu_m_axi_if.rresp =    M_AXI_MCU_IFU_RRESP;
    assign cptra_ss_mcu_ifu_m_axi_if.rid =      M_AXI_MCU_IFU_RID;
    assign cptra_ss_mcu_ifu_m_axi_if.rlast =    M_AXI_MCU_IFU_RLAST;
    assign cptra_ss_mcu_ifu_m_axi_if.rvalid =   M_AXI_MCU_IFU_RVALID;
    assign M_AXI_MCU_IFU_RREADY = cptra_ss_mcu_ifu_m_axi_if.rready;

    // I3C AXI Subordinate
    axi_if #(
        .AW(32),//`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) cptra_ss_i3c_s_axi_if (.clk(i3c_clk), .rst_n(hwif_out.interface_regs.control.cptra_ss_rst_b.value));

    // AW
    assign cptra_ss_i3c_s_axi_if.awaddr   = S_AXI_I3C_AWADDR;
    assign cptra_ss_i3c_s_axi_if.awburst  = S_AXI_I3C_AWBURST;
    assign cptra_ss_i3c_s_axi_if.awsize   = S_AXI_I3C_AWSIZE;
    assign cptra_ss_i3c_s_axi_if.awlen    = S_AXI_I3C_AWLEN;
    assign cptra_ss_i3c_s_axi_if.awuser   = hwif_out.interface_regs.pauser.pauser.value; //S_AXI_I3C_AWUSER;
    assign cptra_ss_i3c_s_axi_if.awid     = S_AXI_I3C_AWID;
    assign cptra_ss_i3c_s_axi_if.awlock   = S_AXI_I3C_AWLOCK;
    assign cptra_ss_i3c_s_axi_if.awvalid  = S_AXI_I3C_AWVALID;
    assign S_AXI_I3C_AWREADY = cptra_ss_i3c_s_axi_if.awready;
    // W
    assign cptra_ss_i3c_s_axi_if.wdata    = S_AXI_I3C_WDATA;
    assign cptra_ss_i3c_s_axi_if.wstrb    = S_AXI_I3C_WSTRB;
    assign cptra_ss_i3c_s_axi_if.wvalid   = S_AXI_I3C_WVALID;
    assign S_AXI_I3C_WREADY = cptra_ss_i3c_s_axi_if.wready;
    assign cptra_ss_i3c_s_axi_if.wlast    = S_AXI_I3C_WLAST;
    // B
    assign S_AXI_I3C_BRESP  = cptra_ss_i3c_s_axi_if.bresp;
    assign S_AXI_I3C_BID    = cptra_ss_i3c_s_axi_if.bid;
    assign S_AXI_I3C_BVALID = cptra_ss_i3c_s_axi_if.bvalid;
    assign cptra_ss_i3c_s_axi_if.bready  = S_AXI_I3C_BREADY;
    // AR
    assign cptra_ss_i3c_s_axi_if.araddr  = S_AXI_I3C_ARADDR;
    assign cptra_ss_i3c_s_axi_if.arburst = S_AXI_I3C_ARBURST;
    assign cptra_ss_i3c_s_axi_if.arsize  = S_AXI_I3C_ARSIZE;
    assign cptra_ss_i3c_s_axi_if.arlen   = S_AXI_I3C_ARLEN;
    assign cptra_ss_i3c_s_axi_if.aruser  = hwif_out.interface_regs.pauser.pauser.value; // S_AXI_I3C_ARUSER;
    assign cptra_ss_i3c_s_axi_if.arid    = S_AXI_I3C_ARID;
    assign cptra_ss_i3c_s_axi_if.arlock  = S_AXI_I3C_ARLOCK;
    assign cptra_ss_i3c_s_axi_if.arvalid = S_AXI_I3C_ARVALID;
    assign S_AXI_I3C_ARREADY = cptra_ss_i3c_s_axi_if.arready;
    // R
    assign S_AXI_I3C_RDATA  = cptra_ss_i3c_s_axi_if.rdata;
    assign S_AXI_I3C_RRESP  = cptra_ss_i3c_s_axi_if.rresp;
    assign S_AXI_I3C_RID    = cptra_ss_i3c_s_axi_if.rid;
    assign S_AXI_I3C_RLAST  = cptra_ss_i3c_s_axi_if.rlast;
    assign S_AXI_I3C_RVALID = cptra_ss_i3c_s_axi_if.rvalid;
    assign cptra_ss_i3c_s_axi_if.rready = S_AXI_I3C_RREADY;

    // LCC AXI
    //input
    axi_struct_pkg::axi_wr_req_t cptra_ss_lc_axi_wr_req_i;
    assign cptra_ss_lc_axi_wr_req_i.awaddr  = S_AXI_LCC_AWADDR;
    assign cptra_ss_lc_axi_wr_req_i.awburst = S_AXI_LCC_AWBURST;
    assign cptra_ss_lc_axi_wr_req_i.awsize  = S_AXI_LCC_AWSIZE;
    assign cptra_ss_lc_axi_wr_req_i.awlen   = S_AXI_LCC_AWLEN;
    assign cptra_ss_lc_axi_wr_req_i.awuser  = S_AXI_LCC_AWUSER;
    assign cptra_ss_lc_axi_wr_req_i.awid    = S_AXI_LCC_AWID;
    assign cptra_ss_lc_axi_wr_req_i.awlock  = S_AXI_LCC_AWLOCK;
    assign cptra_ss_lc_axi_wr_req_i.awvalid = S_AXI_LCC_AWVALID;
    assign cptra_ss_lc_axi_wr_req_i.wdata   = S_AXI_LCC_WDATA;
    assign cptra_ss_lc_axi_wr_req_i.wstrb   = S_AXI_LCC_WSTRB;
    assign cptra_ss_lc_axi_wr_req_i.wlast   = S_AXI_LCC_WLAST;
    assign cptra_ss_lc_axi_wr_req_i.wvalid  = S_AXI_LCC_WVALID;
    assign cptra_ss_lc_axi_wr_req_i.bready  = S_AXI_LCC_BREADY;
    //output
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_lc_axi_wr_rsp_o;
    assign S_AXI_LCC_AWREADY = cptra_ss_lc_axi_wr_rsp_o.awready;
    assign S_AXI_LCC_WREADY  = cptra_ss_lc_axi_wr_rsp_o.wready;
    assign S_AXI_LCC_BRESP   = cptra_ss_lc_axi_wr_rsp_o.bresp;
    assign S_AXI_LCC_BID     = cptra_ss_lc_axi_wr_rsp_o.bid;
    assign S_AXI_LCC_BVALID  = cptra_ss_lc_axi_wr_rsp_o.bvalid;
    //input
    axi_struct_pkg::axi_rd_req_t cptra_ss_lc_axi_rd_req_i;
    assign cptra_ss_lc_axi_rd_req_i.araddr  = S_AXI_LCC_ARADDR;
    assign cptra_ss_lc_axi_rd_req_i.arburst = S_AXI_LCC_ARBURST;
    assign cptra_ss_lc_axi_rd_req_i.arsize  = S_AXI_LCC_ARSIZE;
    assign cptra_ss_lc_axi_rd_req_i.arlen   = S_AXI_LCC_ARLEN;
    assign cptra_ss_lc_axi_rd_req_i.aruser  = S_AXI_LCC_ARUSER;
    assign cptra_ss_lc_axi_rd_req_i.arid    = S_AXI_LCC_ARID;
    assign cptra_ss_lc_axi_rd_req_i.arlock  = S_AXI_LCC_ARLOCK;
    assign cptra_ss_lc_axi_rd_req_i.arvalid = S_AXI_LCC_ARVALID;
    assign cptra_ss_lc_axi_rd_req_i.rready  = S_AXI_LCC_RREADY;
    //output
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_lc_axi_rd_rsp_o;
    assign S_AXI_LCC_ARREADY = cptra_ss_lc_axi_rd_rsp_o.arready;
    assign S_AXI_LCC_RDATA   = cptra_ss_lc_axi_rd_rsp_o.rdata;
    assign S_AXI_LCC_RRESP   = cptra_ss_lc_axi_rd_rsp_o.rresp;
    assign S_AXI_LCC_RID     = cptra_ss_lc_axi_rd_rsp_o.rid;
    assign S_AXI_LCC_RLAST   = cptra_ss_lc_axi_rd_rsp_o.rlast;
    assign S_AXI_LCC_RVALID  = cptra_ss_lc_axi_rd_rsp_o.rvalid;

    // Fuse/OTP Controller AXI
    //input
    axi_struct_pkg::axi_wr_req_t cptra_ss_otp_core_axi_wr_req_i;
    assign cptra_ss_otp_core_axi_wr_req_i.awaddr  = S_AXI_OTP_AWADDR;
    assign cptra_ss_otp_core_axi_wr_req_i.awburst = S_AXI_OTP_AWBURST;
    assign cptra_ss_otp_core_axi_wr_req_i.awsize  = S_AXI_OTP_AWSIZE;
    assign cptra_ss_otp_core_axi_wr_req_i.awlen   = S_AXI_OTP_AWLEN;
    assign cptra_ss_otp_core_axi_wr_req_i.awuser  = S_AXI_OTP_AWUSER;
    assign cptra_ss_otp_core_axi_wr_req_i.awid    = S_AXI_OTP_AWID;
    assign cptra_ss_otp_core_axi_wr_req_i.awlock  = S_AXI_OTP_AWLOCK;
    assign cptra_ss_otp_core_axi_wr_req_i.awvalid = S_AXI_OTP_AWVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.wdata   = S_AXI_OTP_WDATA;
    assign cptra_ss_otp_core_axi_wr_req_i.wstrb   = S_AXI_OTP_WSTRB;
    assign cptra_ss_otp_core_axi_wr_req_i.wlast   = S_AXI_OTP_WLAST;
    assign cptra_ss_otp_core_axi_wr_req_i.wvalid  = S_AXI_OTP_WVALID;
    assign cptra_ss_otp_core_axi_wr_req_i.bready  = S_AXI_OTP_BREADY;
    //output
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_otp_core_axi_wr_rsp_o;
    assign S_AXI_OTP_AWREADY = cptra_ss_otp_core_axi_wr_rsp_o.awready;
    assign S_AXI_OTP_WREADY  = cptra_ss_otp_core_axi_wr_rsp_o.wready;
    assign S_AXI_OTP_BRESP   = cptra_ss_otp_core_axi_wr_rsp_o.bresp;
    assign S_AXI_OTP_BID     = cptra_ss_otp_core_axi_wr_rsp_o.bid;
    assign S_AXI_OTP_BVALID  = cptra_ss_otp_core_axi_wr_rsp_o.bvalid;
    //input
    axi_struct_pkg::axi_rd_req_t cptra_ss_otp_core_axi_rd_req_i;
    assign cptra_ss_otp_core_axi_rd_req_i.araddr  = S_AXI_OTP_ARADDR;
    assign cptra_ss_otp_core_axi_rd_req_i.arburst = S_AXI_OTP_ARBURST;
    assign cptra_ss_otp_core_axi_rd_req_i.arsize  = S_AXI_OTP_ARSIZE;
    assign cptra_ss_otp_core_axi_rd_req_i.arlen   = S_AXI_OTP_ARLEN;
    assign cptra_ss_otp_core_axi_rd_req_i.aruser  = S_AXI_OTP_ARUSER;
    assign cptra_ss_otp_core_axi_rd_req_i.arid    = S_AXI_OTP_ARID;
    assign cptra_ss_otp_core_axi_rd_req_i.arlock  = S_AXI_OTP_ARLOCK;
    assign cptra_ss_otp_core_axi_rd_req_i.arvalid = S_AXI_OTP_ARVALID;
    assign cptra_ss_otp_core_axi_rd_req_i.rready  = S_AXI_OTP_RREADY;
    //output
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_otp_core_axi_rd_rsp_o;
    assign S_AXI_OTP_ARREADY = cptra_ss_otp_core_axi_rd_rsp_o.arready;
    assign S_AXI_OTP_RDATA   = cptra_ss_otp_core_axi_rd_rsp_o.rdata;
    assign S_AXI_OTP_RRESP   = cptra_ss_otp_core_axi_rd_rsp_o.rresp;
    assign S_AXI_OTP_RID     = cptra_ss_otp_core_axi_rd_rsp_o.rid;
    assign S_AXI_OTP_RLAST   = cptra_ss_otp_core_axi_rd_rsp_o.rlast;
    assign S_AXI_OTP_RVALID  = cptra_ss_otp_core_axi_rd_rsp_o.rvalid;

    // CSR HMAC KEY - TODO: Copying initialization from soc_bfm. Should probably connect to SW
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0] cptra_ss_cptra_csr_hmac_key_i;
    initial begin
      for (int dword = 0; dword < `CLP_CSR_HMAC_KEY_DWORDS; dword++) begin
         cptra_ss_cptra_csr_hmac_key_i[dword] = '1; //FIXME
      end
    end
    
    css_mcu0_el2_mem_if cptra_ss_mcu0_el2_mem_export ();


    /*
    Line Driver logic
    sel_od_pp == 1 indicates push-pull
    | sel_od_pp | phy2io | phy_data_io |    |   IN |   EN | UP |    |      wire      |
    |         0 |      0 |           z | -> |    x |    1 |  1 | -> | z              | // TODO: Use z or pull up 2k?
    |         0 |      1 |           0 | -> |    1 |    0 |  0 | -> | open drain low |
    |         1 |      0 |           0 | -> |    1 |    0 |  1 | -> | push pull low  |
    |         1 |      1 |           1 | -> |    0 |    0 |  1 | -> | push pull high |

    Discrete logic
    sel_od_pp == 1 indicates push-pull
    | sel_od_pp | phy2io | phy_data_io |    | PUSH | PULL | UP |    |      wire      |
    |         0 |      0 |           z | -> |    1 |    0 |  1 | -> | z              | // TODO: Use z or pull up 2k?
    |         0 |      1 |           0 | -> |    1 |    1 |  0 | -> | open drain low |
    |         1 |      0 |           0 | -> |    1 |    1 |  1 | -> | push pull low  |
    |         1 |      1 |           1 | -> |    0 |    0 |  1 | -> | push pull high |
    */
    logic cptra_ss_i3c_scl_o;
    logic cptra_ss_i3c_sda_o;
    logic cptra_ss_sel_od_pp_o;

    always_comb begin
        case ({
        cptra_ss_sel_od_pp_o, cptra_ss_i3c_scl_o
        })
        2'b00:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b101;
        2'b01:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b110;
        2'b10:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b111;
        2'b11:   {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b001;
        default: {SCL_PUSH, SCL_PULL, SCL_UP} = 3'b101;
        endcase
    end

    always_comb begin
        case ({
        cptra_ss_sel_od_pp_o, cptra_ss_i3c_sda_o
        })
        2'b00:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b101;
        2'b01:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b110;
        2'b10:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b111;
        2'b11:   {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b001;
        default: {SDA_PUSH, SDA_PULL, SDA_UP} = 3'b101;
        endcase
    end

caliptra_ss_top caliptra_ss_top_0 (
    .cptra_ss_clk_i(core_clk),
    .cptra_i3c_clk_i(i3c_clk),
    .cptra_ss_pwrgood_i(hwif_out.interface_regs.control.cptra_pwrgood.value),
    .cptra_ss_rst_b_i(hwif_out.interface_regs.control.cptra_ss_rst_b.value),

    // Caliptra Core AXI Sub Interface
    .cptra_ss_cptra_core_s_axi_if(cptra_core_s_axi),

    // Caliptra Core AXI Manager Interface
    .cptra_ss_cptra_core_m_axi_if(cptra_core_m_axi),

    // Caliptra SS MCI AXI Sub Interface
    .cptra_ss_mci_s_axi_if(cptra_ss_mci_s_axi),

    // Caliptra SS MCU ROM AXI Sub Interface
    .cptra_ss_mcu_rom_s_axi_if,
    .mcu_rom_mem_export_if,

    // Caliptra SS MCI AXI Manager Interface
    .cptra_ss_mci_m_axi_if,

    // Caliptra SS MCU LSU/IFU AXI Manager Interface
    .cptra_ss_mcu_lsu_m_axi_if,
    .cptra_ss_mcu_ifu_m_axi_if,

    // Caliptra SS I3C AXI Sub Interface
    .cptra_ss_i3c_s_axi_if,

    // Caliptra SS LC Controller AXI Sub Interface
    .cptra_ss_lc_axi_wr_req_i,
    .cptra_ss_lc_axi_wr_rsp_o,
    .cptra_ss_lc_axi_rd_req_i,
    .cptra_ss_lc_axi_rd_rsp_o,

    // Caliptra SS FC / OTP Controller AXI Sub Interface
    .cptra_ss_otp_core_axi_wr_req_i,
    .cptra_ss_otp_core_axi_wr_rsp_o,
    .cptra_ss_otp_core_axi_rd_req_i,
    .cptra_ss_otp_core_axi_rd_rsp_o,

    //--------------------
    // caliptra core Obf Key & CSR Signing Key
    //--------------------
    .cptra_ss_cptra_obf_key_i({hwif_out.interface_regs.cptra_obf_key[7].value.value,
                               hwif_out.interface_regs.cptra_obf_key[6].value.value,
                               hwif_out.interface_regs.cptra_obf_key[5].value.value,
                               hwif_out.interface_regs.cptra_obf_key[4].value.value,
                               hwif_out.interface_regs.cptra_obf_key[3].value.value,
                               hwif_out.interface_regs.cptra_obf_key[2].value.value,
                               hwif_out.interface_regs.cptra_obf_key[1].value.value,
                               hwif_out.interface_regs.cptra_obf_key[0].value.value}),
    .cptra_ss_cptra_csr_hmac_key_i,

    // Caliptra JTAG Interface
    .cptra_ss_cptra_core_jtag_tck_i(jtag_tck),
    .cptra_ss_cptra_core_jtag_tdi_i(jtag_tdi),
    .cptra_ss_cptra_core_jtag_tms_i(jtag_tms),
    .cptra_ss_cptra_core_jtag_trst_n_i(jtag_trst_n),
    .cptra_ss_cptra_core_jtag_tdo_o(jtag_tdo),
    .cptra_ss_cptra_core_jtag_tdoEn_o(),
    //output logic [124:0]               cptra_ss_cptra_generic_fw_exec_ctrl_o,
    .cptra_ss_cptra_generic_fw_exec_ctrl_o(),

    // LC Controller JTAG
    //input   jtag_pkg::jtag_req_t                       cptra_ss_lc_ctrl_jtag_i,
    //output  jtag_pkg::jtag_rsp_t                       cptra_ss_lc_ctrl_jtag_o,
    .cptra_ss_lc_ctrl_jtag_i(),
    .cptra_ss_lc_ctrl_jtag_o(),

    // Caliptra Memory Export Interface
    // Caliptra Core, ICCM and DCCM interface
    .cptra_ss_cptra_core_el2_mem_export(el2_mem_export.veer_sram_src),
    .mldsa_memory_export_req(mldsa_memory_export.req),

    // SRAM interface for mbox
    // Caliptra SS mailbox sram interface
    .cptra_ss_cptra_core_mbox_sram_cs_o(mbox_sram_cs),
    .cptra_ss_cptra_core_mbox_sram_we_o(mbox_sram_we),
    .cptra_sscptra_core_mbox_sram_addr_o(mbox_sram_addr),
    .cptra_ss_cptra_core_mbox_sram_wdata_o(mbox_sram_wdata),
    .cptra_ss_cptra_core_mbox_sram_rdata_i(mbox_sram_rdata),

    .cptra_ss_cptra_core_imem_cs_o(imem_cs),
    .cptra_ss_cptra_core_imem_addr_o(imem_addr),
    .cptra_ss_cptra_core_imem_rdata_i(imem_rdata),

    .cptra_ss_cptra_core_bootfsm_bp_i(BootFSM_BrkPoint),

// TRNG Interface
`ifdef CALIPTRA_INTERNAL_TRNG
    // External Request
    .cptra_ss_cptra_core_etrng_req_o(etrng_req),
    // Physical Source for Internal TRNG
    .cptra_ss_cptra_core_itrng_data_i(itrng_data),
    .cptra_ss_cptra_core_itrng_valid_i(itrng_valid),
`endif

    .cptra_ss_mcu_rom_macro_req_if,

    // Caliptra SS MCU 
    .cptra_ss_strap_mcu_lsu_axi_user_i(hwif_out.interface_regs.lsu_user.lsu_user.value),
    .cptra_ss_strap_mcu_ifu_axi_user_i(hwif_out.interface_regs.ifu_user.ifu_user.value),
    .cptra_ss_strap_clp_axi_user_i    (hwif_out.interface_regs.clp_user.clp_user.value),

    // Caliptra SS MCI MCU SRAM Interface (SRAM, MBOX0, MBOX1)
    .cptra_ss_mci_mcu_sram_req_if,
    .cptra_ss_mci_mbox0_sram_req_if,
    .cptra_ss_mci_mbox1_sram_req_if,
    .cptra_ss_mcu0_el2_mem_export,
    
    .cptra_ss_mci_generic_input_wires_i({hwif_out.interface_regs.mci_generic_input_wires[0].value.value, hwif_out.interface_regs.mci_generic_input_wires[1].value.value}),
    .cptra_ss_mci_generic_output_wires_o({hwif_in.interface_regs.mci_generic_output_wires[0].value.next, hwif_in.interface_regs.mci_generic_output_wires[1].value.next}),

    .cptra_ss_strap_mcu_reset_vector_i(hwif_out.interface_regs.mcu_reset_vector.mcu_reset_vector.value),
    .cptra_ss_mcu_no_rom_config_i(hwif_out.interface_regs.mcu_config.mcu_no_rom_config.value),
    .cptra_ss_mci_boot_seq_brkpoint_i(hwif_out.interface_regs.mcu_config.cptra_ss_mci_boot_seq_brkpoint_i.value),
    
    //input logic cptra_ss_lc_Allow_RMA_on_PPD_i,
    .cptra_ss_lc_Allow_RMA_on_PPD_i(1'b0),

    .cptra_ss_mci_error_fatal_o(hwif_in.interface_regs.mci_error.mci_error_fatal.next),
    .cptra_ss_mci_error_non_fatal_o(hwif_in.interface_regs.mci_error.mci_error_non_fatal.next),
    
    // TODO: MCU JTAG
    .cptra_ss_mcu_jtag_tck_i(),
    .cptra_ss_mcu_jtag_tms_i(),
    .cptra_ss_mcu_jtag_tdi_i(),
    .cptra_ss_mcu_jtag_trst_n_i(),
    .cptra_ss_mcu_jtag_tdo_o(),
    .cptra_ss_mcu_jtag_tdoEn_o(),

    // Address straps
    .cptra_ss_strap_caliptra_base_addr_i     (64'hA4100000),
    .cptra_ss_strap_mci_base_addr_i          (64'hA4050000),
    .cptra_ss_strap_recovery_ifc_base_addr_i (64'h0), // TODO: What to set this to?
    .cptra_ss_strap_otp_fc_base_addr_i       (64'hA4060000),
    .cptra_ss_strap_uds_seed_base_addr_i     (64'h0), // TODO: What to set this to?
    .cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i(32'h0), // TODO: What to set this to?
    .cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i(32'h0), // TODO: What to set this to?
    .cptra_ss_strap_generic_0_i(32'h0),
    .cptra_ss_strap_generic_1_i(32'h0),
    .cptra_ss_strap_generic_2_i(32'h0),
    .cptra_ss_strap_generic_3_i(32'h0),
    .cptra_ss_debug_intent_i(1'b0),            // Debug intent signal

    // TODO: Connect
    /*output logic        */ .cptra_ss_dbg_manuf_enable_o(),
    /*output logic [63:0] */ .cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o(),

    // LC Clock bypass not interesting for FPGA. Disconnect
    .cptra_ss_lc_clk_byp_ack_i(),
    .cptra_ss_lc_clk_byp_req_o(),
    .cptra_ss_lc_ctrl_scan_rst_ni_i(1'b1),

    .cptra_ss_lc_esclate_scrap_state0_i(hwif_out.interface_regs.mcu_config.cptra_ss_lc_esclate_scrap_state0_i.value),   // NOTE: These two signals are very important. FIXME: Renaming is needed
    .cptra_ss_lc_esclate_scrap_state1_i(hwif_out.interface_regs.mcu_config.cptra_ss_lc_esclate_scrap_state1_i.value),   // If you assert them, Caliptr-SS will enter SCRAP mode

    /*output wire*/ .cptra_ss_soc_dft_en_o(),
    /*output wire*/ .cptra_ss_soc_hw_debug_en_o(),
    
    // Caliptra SS Fuse Controller Interface (Fuse Macros)
    /*input  tlul_pkg::tl_h2d_t*/ .cptra_ss_fuse_macro_prim_tl_i('0),
    /*output tlul_pkg::tl_d2h_t*/ .cptra_ss_fuse_macro_prim_tl_o(),
   
    // Caliptra SS I3C GPIO Interface
    .cptra_ss_i3c_scl_i(SCL),
    .cptra_ss_i3c_sda_i(SDA),
    .cptra_ss_i3c_scl_o,
    .cptra_ss_i3c_sda_o,
    .cptra_ss_sel_od_pp_o,

    // -- THESE ARE NOT RTL SIGNALS, DO NOT USE THEM
    .cptra_ss_cptra_core_generic_input_wires_i(),
    .cptra_ss_cptra_core_scan_mode_i(),
    .cptra_error_fatal(),
    .cptra_error_non_fatal(),
    .ready_for_fuses(),
    .ready_for_mb_processing(),
    .mailbox_data_avail()
);

    // Hierarchical references to generic output wires register. Use as input to log FIFO.
    logic fifo_write_en;
    logic [7:0] fifo_char;
    assign fifo_write_en = caliptra_ss_top_0.caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.CPTRA_GENERIC_OUTPUT_WIRES[0].generic_wires.load_next;
    assign fifo_char[7:0] = caliptra_ss_top_0.caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.CPTRA_GENERIC_OUTPUT_WIRES[0].generic_wires.next[7:0];




//////////////////////////////////////////////////////
// DCCM
//
logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_wr_fdata;
logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_fdout;
logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

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
    always_ff @(cptra_ss_mcu0_el2_mem_export.clk) begin : inject_dccm_ecc_error
        // if (~error_injection_mode.dccm_single_bit_error && ~error_injection_mode.dccm_double_bit_error) begin
        //     dccm_wdata_bitflip <= '{default:0};
        // end else if (cptra_ss_mcu0_el2_mem_export.dccm_clken & cptra_ss_mcu0_el2_mem_export.dccm_wren_bank) begin
        //     for (ii=0; ii<pt.DCCM_NUM_BANKS; ii++) begin: dccm_bitflip_injection_loop
        //         dccm_wdata_bitflip[ii] <= get_bitflip_mask(error_injection_mode.dccm_double_bit_error);
        //     end
        // end
        dccm_wdata_bitflip <= '{default:0};
    end
    for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop

        assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0] = {cptra_ss_mcu0_el2_mem_export.dccm_wr_ecc_bank[i], cptra_ss_mcu0_el2_mem_export.dccm_wr_data_bank[i]} ^ dccm_wdata_bitflip[i];
        assign cptra_ss_mcu0_el2_mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][31:0];
        assign cptra_ss_mcu0_el2_mem_export.dccm_bank_ecc[i] = dccm_bank_fdout[i][38:32];

    `ifdef VERILATOR

            el2_ram #(DCCM_INDEX_DEPTH,39)  ram (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
    `else

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
	 	 	 	 ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
	 	 	 	 ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
	 	 	 	 ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
	 	 	 	 ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
	 	 	 	 ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
	 	 	 	 ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
	 	 	 	 ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
	 	 	 	 ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
	 	 	 	 ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `MCU_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
	 	 	 	 ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(cptra_ss_mcu0_el2_mem_export.dccm_clken[i]),
                                    .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                    .WE(cptra_ss_mcu0_el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(cptra_ss_mcu0_el2_mem_export.dccm_addr_bank[i]),
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

//logic [pt.ICCM_NUM_BANKS-1:0] [38:0] iccm_wdata_bitflip;
//int jj;
//always_ff @(cptra_ss_mcu0_el2_mem_export.clk) begin : inject_iccm_ecc_error
//    if (~error_injection_mode.iccm_single_bit_error && ~error_injection_mode.iccm_double_bit_error) begin
//        iccm_wdata_bitflip <= '{default:0};
//    end else if (cptra_ss_mcu0_el2_mem_export.iccm_clken & cptra_ss_mcu0_el2_mem_export.iccm_wren_bank) begin
//        for (jj=0; jj<pt.ICCM_NUM_BANKS; jj++) begin: iccm_bitflip_injection_loop
//            iccm_wdata_bitflip[jj] <= get_bitflip_mask(error_injection_mode.iccm_double_bit_error);
//        end
//    end
//end
for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin: iccm_loop
    // -- new --- assign iccm_bank_wr_fdata[i][31:0] = cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_data[i];
    // -- new --- assign iccm_bank_wr_fdata[i][38:32] = cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_ecc[i];
    // -- new --- assign cptra_ss_mcu0_el2_mem_export.iccm_bank_dout[i] = iccm_bank_fdout[i][31:0];
    // -- new --- assign cptra_ss_mcu0_el2_mem_export.iccm_bank_ecc[i] = iccm_bank_fdout[i][38:32];
    //assign cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_data[i] = iccm_bank_wr_fdata[i][31:0];
    //assign cptra_ss_mcu0_el2_mem_export.iccm_bank_wr_ecc[i] = iccm_bank_wr_fdata[i][37:32];
    //assign iccm_bank_fdout[i] = {cptra_ss_mcu0_el2_mem_export.iccm_bank_ecc[i], cptra_ss_mcu0_el2_mem_export.iccm_bank_dout[i]};

    `ifdef VERILATOR

    el2_ram #(.depth(1<<pt.ICCM_INDEX_BITS), .width(39)) iccm_bank (
                                        // Primary ports
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_64x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_128x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_256x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_512x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_1024x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_2048x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_4096x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_8192x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_16384x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
	 	 	 	 ram_32768x39 iccm_bank (
                                        // Primary ports
                                        .CLK(cptra_ss_mcu0_el2_mem_export.clk),
                                        .ME(cptra_ss_mcu0_el2_mem_export.iccm_clken[i]),
                                        .WE(cptra_ss_mcu0_el2_mem_export.iccm_wren_bank[i]),
                                        .ADR(cptra_ss_mcu0_el2_mem_export.iccm_addr_bank[i]),
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
            `EL2_IC_DATA_SRAM(8192,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
            `EL2_IC_DATA_SRAM(4096,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
            `EL2_IC_DATA_SRAM(2048,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
            `EL2_IC_DATA_SRAM(1024,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
            `EL2_IC_DATA_SRAM(512,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
          else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
            `EL2_IC_DATA_SRAM(256,71,i,k,cptra_ss_mcu0_el2_mem_export)
          end
          else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
            `EL2_IC_DATA_SRAM(128,71,i,k,cptra_ss_mcu0_el2_mem_export)
          end
          else  begin : size_64
            `EL2_IC_DATA_SRAM(64,71,i,k,cptra_ss_mcu0_el2_mem_export)
         end
       end // if (pt.ICACHE_ECC)
 
       else  begin  : ECC0
         if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
            `EL2_IC_DATA_SRAM(8192,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
            `EL2_IC_DATA_SRAM(4096,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
            `EL2_IC_DATA_SRAM(2048,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
            `EL2_IC_DATA_SRAM(1024,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
            `EL2_IC_DATA_SRAM(512,68,i,k,cptra_ss_mcu0_el2_mem_export)
         end
          else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
             `EL2_IC_DATA_SRAM(256,68,i,k,cptra_ss_mcu0_el2_mem_export)
           end
           else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
             `EL2_IC_DATA_SRAM(128,68,i,k,cptra_ss_mcu0_el2_mem_export)
           end
           else  begin : size_64
             `EL2_IC_DATA_SRAM(64,68,i,k,cptra_ss_mcu0_el2_mem_export)
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
              `EL2_PACKED_IC_DATA_SRAM(8192,284,71,k,cptra_ss_mcu0_el2_mem_export)    // 64b data + 7b ecc
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,284,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,142,71,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_64
       end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        // SRAMs with parity
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,272,68,k,cptra_ss_mcu0_el2_mem_export)    // 64b data + 4b parity
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(8192,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(4096,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(2048,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(1024,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(512,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(256,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(128,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,272,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM(64,136,68,k,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        end // block: size_64
     end // block: ECC0
     end // block: BANKS_WAY
 end // block: PACKED_10


// ICACHE TAG
if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_11
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
                 `EL2_IC_TAG_SRAM(32,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 32)
        if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
                 `EL2_IC_TAG_SRAM(64,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 64)
        if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
                 `EL2_IC_TAG_SRAM(128,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 128)
        if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
                 `EL2_IC_TAG_SRAM(256,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 256)
        if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
                 `EL2_IC_TAG_SRAM(512,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 512)
        if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
                 `EL2_IC_TAG_SRAM(1024,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 1024)
        if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
                 `EL2_IC_TAG_SRAM(2048,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 2048)
        if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
                 `EL2_IC_TAG_SRAM(4096,26,i,cptra_ss_mcu0_el2_mem_export)
        end // if (pt.ICACHE_TAG_DEPTH == 4096)
    end // block: WAYS
end // block: PACKED_11

else begin : PACKED_1
    if (pt.ICACHE_ECC) begin  : ECC1
        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,104,cptra_ss_mcu0_el2_mem_export)
           end // block: WAYS
        else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,104,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,52,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,104,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,52,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_4096
    end // block: ECC1

    else  begin : ECC0
        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
            if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,88,cptra_ss_mcu0_el2_mem_export)
            end // block: WAYS
            else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(32,44,cptra_ss_mcu0_el2_mem_export)
            end // block: WAYS
        end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(64,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,88,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(128,44,cptra_ss_mcu0_el2_mem_export)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(256,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(512,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(1024,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(2048,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,88,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM(4096,44,cptra_ss_mcu0_el2_mem_export)
        end // block: WAYS
      end // block: size_4096
    end // block: ECC0
end // block: PACKED_1
// end ICACHE TAG



endmodule
