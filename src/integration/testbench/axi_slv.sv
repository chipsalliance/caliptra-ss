
//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// 
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
//********************************************************************************
module axi_slv #(
    TAGW = 1
) (
    input                 aclk,
    input                 rst_l,
    input                 arvalid,
    output reg            arready,
    input      [    31:0] araddr,
    input      [TAGW-1:0] arid,
    input      [     7:0] arlen,
    input      [     1:0] arburst,
    input      [     2:0] arsize,

    output reg            rvalid,
    input                 rready,
    output reg [    63:0] rdata,
    output reg [     1:0] rresp,
    output reg [TAGW-1:0] rid,
    output reg            rlast,

    input             awvalid,
    output            awready,
    input  [    31:0] awaddr,
    input  [TAGW-1:0] awid,
    input  [     7:0] awlen,
    input  [     1:0] awburst,
    input  [     2:0] awsize,

    input  [63:0] wdata,
    input  [ 7:0] wstrb,
    input         wvalid,
    output        wready,

    output reg            bvalid,
    input                 bready,
    output reg [     1:0] bresp,
    output reg [TAGW-1:0] bid
);

  parameter MAILBOX_ADDR = 32'hD0580000;
  parameter MEM_SIZE_DW = 8192;

  bit [7:0] mem[bit [31:0]];
  bit [63:0] memdata;
  bit        rlast_local;
  logic [31:0]            awaddr_aligned,awaddr_aligned_r;
  logic [31:0]            araddr_aligned;
  always_comb begin
      awaddr_aligned = {awaddr[31:3],3'b000};
      araddr_aligned = {araddr[31:3],3'b000};
  end

  reg [TAGW-1:0] awid_local;

  assign awid_local = (awvalid == 1)? awid : bid;

  always @(posedge aclk or negedge rst_l) begin
    if (!rst_l) begin
      rvalid <= 0;
      bvalid <= 0;
      rlast  <= 0;
      bid    <= 0;
    end else begin
      bid    <= awid_local;
      rid    <= arid;
      rvalid <= arvalid;
      bvalid <= wvalid;
      rdata  <= memdata;
      rlast  <= rlast_local;
    end
  end

  always @(negedge aclk) begin

    if (arvalid) begin
      memdata <= {
        mem[araddr_aligned+7],
        mem[araddr_aligned+6],
        mem[araddr_aligned+5],
        mem[araddr_aligned+4],
        mem[araddr_aligned+3],
        mem[araddr_aligned+2],
        mem[araddr_aligned+1],
        mem[araddr_aligned]
      };
      rlast_local  <= 1'b1;
    end else begin
      rlast_local  <= 1'b0;
    end

    if(awvalid) awaddr_aligned_r <= awaddr_aligned;
    if(awvalid&&wvalid) begin
        if(wstrb[7]) mem[awaddr_aligned+7] = wdata[63:56];
        if(wstrb[6]) mem[awaddr_aligned+6] = wdata[55:48];
        if(wstrb[5]) mem[awaddr_aligned+5] = wdata[47:40];
        if(wstrb[4]) mem[awaddr_aligned+4] = wdata[39:32];
        if(wstrb[3]) mem[awaddr_aligned+3] = wdata[31:24];
        if(wstrb[2]) mem[awaddr_aligned+2] = wdata[23:16];
        if(wstrb[1]) mem[awaddr_aligned+1] = wdata[15:08];
        if(wstrb[0]) mem[awaddr_aligned+0] = wdata[07:00];
    end
    else if(wvalid) begin
        if(wstrb[7]) mem[awaddr_aligned_r+7] = wdata[63:56];
        if(wstrb[6]) mem[awaddr_aligned_r+6] = wdata[55:48];
        if(wstrb[5]) mem[awaddr_aligned_r+5] = wdata[47:40];
        if(wstrb[4]) mem[awaddr_aligned_r+4] = wdata[39:32];
        if(wstrb[3]) mem[awaddr_aligned_r+3] = wdata[31:24];
        if(wstrb[2]) mem[awaddr_aligned_r+2] = wdata[23:16];
        if(wstrb[1]) mem[awaddr_aligned_r+1] = wdata[15:08];
        if(wstrb[0]) mem[awaddr_aligned_r+0] = wdata[07:00];
    end
  end


  assign arready = 1'b1;
  assign awready = 1'b1;
  assign wready  = 1'b1;
  assign rresp   = 2'b0;
  assign bresp   = 2'b0;
//   assign rlast   = 1'b1;

endmodule
