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
// DESCRIPTION:
//   - This module has two interface connections, an AXI manager and subordinate.
//   - When an input request from the Manager is detected with AxSIZE == 3, which
//     indicates a request size of 64b, the downsizer will form an outgoing request
//     with AxSIZE == 2, and increase the AxLEN appropriately.
//   - Write data will be broken into smaller packets and sent out.
//   - Read data will be aggregated (from the correct lanes) into a 64b response
//
// LIMITATIONS:
//   - Only works with requests for which address is 8-byte aligned
//
// TODO:
//   - This is a temporary solution to workaround a limitation in the Avery AXI
//     interconnect VIP that 64b requests towards a 32b subordinate are not supported.
//   - This module should be deleted once this feature is natively supported in the
//     AXI interconnect VIP.

`include "caliptra_sva.svh"

module caliptra_ss_top_tb_axi_64_to_32_downsizer (
    input logic clk,
    input logic rst_n,
    axi_if      m_axi_if,
    input logic [3:0] m_axi_if_arcache,
    input logic [2:0] m_axi_if_arprot,
    input logic [3:0] m_axi_if_arregion,
    input logic [3:0] m_axi_if_arqos,
    input logic [3:0] m_axi_if_awcache,
    input logic [2:0] m_axi_if_awprot,
    input logic [3:0] m_axi_if_awregion,
    input logic [3:0] m_axi_if_awqos,
    axi_if      s_axi_if,
    output logic [3:0] s_axi_if_arcache,
    output logic [2:0] s_axi_if_arprot,
    output logic [3:0] s_axi_if_arregion,
    output logic [3:0] s_axi_if_arqos,
    output logic [3:0] s_axi_if_awcache,
    output logic [2:0] s_axi_if_awprot,
    output logic [3:0] s_axi_if_awregion,
    output logic [3:0] s_axi_if_awqos
);

import axi_pkg::*;


//==================================
// Parameters
//==================================
localparam FIFO_BC = 4096;
localparam FIFO_DEPTH = FIFO_BC/8;


//==================================
// Variables
//==================================

// Read context
logic m_ar_hshake, m_r_hshake;
logic s_ar_hshake, s_r_hshake;
logic rd_beat_upper;
logic rd_active;
logic rd_ds_bypass; // Skip the downsizer fifo for datapath
logic [31:0] rd_low_word;
logic [$bits(axi_resp_e)-1:0] rd_low_resp;
logic [63:0] rd_qword;
logic [63:0] rd_resp;
logic [$bits(m_axi_if.rid)-1:0] rd_rid;
logic        rd_last;

logic r_fifo_wvalid;
logic r_fifo_wready;
logic r_fifo_rvalid;
logic r_fifo_rready;
struct packed {
    logic [63:0] data;
    logic [$bits(m_axi_if.rresp)-1:0] resp;
    logic [$bits(m_axi_if.rid)-1:0]   rid;
    logic                             last;
} r_fifo_wdata, r_fifo_rdata;
logic r_fifo_full, r_fifo_error;
logic [caliptra_prim_util_pkg::vbits(FIFO_DEPTH+1)-1:0] r_fifo_depth;

// Write context
logic m_aw_hshake, m_w_hshake;
logic s_aw_hshake, s_w_hshake;
logic wr_beat_upper;
logic wr_active;
logic wr_ds_bypass; // Skip the downsizer fifo for datapath
logic [63:0] wr_qword;
logic [7 :0] wr_qword_strb;
logic        wr_last;

logic w_fifo_wvalid;
logic w_fifo_wready;
logic w_fifo_rvalid;
logic w_fifo_rready;
struct packed {
    logic [63:0]                      data;
    logic [$bits(m_axi_if.wstrb)-1:0] strb;
    logic                             last;
} w_fifo_wdata, w_fifo_rdata;
logic w_fifo_full, w_fifo_error;
logic [caliptra_prim_util_pkg::vbits(FIFO_DEPTH+1)-1:0] w_fifo_depth;

// Request context struct
struct packed {
    logic [$bits(m_axi_if.araddr)-1:0] axaddr;
    logic [$bits(axi_burst_e)-1:0]     axburst;
    logic [2:0]                        axsize;
    logic [7:0]                        axlen;
    logic [$bits(m_axi_if.aruser)-1:0] axuser;
    logic [$bits(m_axi_if.arid)-1:0]   axid;
    logic                              axlock;
    logic [3:0]                        axcache;
    logic [2:0]                        axprot;
    logic [3:0]                        axregion;
    logic [3:0]                        axqos;
} m_axi_if_r_ctx, m_axi_if_w_ctx, s_axi_if_r_ctx, s_axi_if_w_ctx;


//==================================
// Read Downsizer
//==================================

assign m_ar_hshake = m_axi_if.arvalid && m_axi_if.arready;
assign s_ar_hshake = s_axi_if.arvalid && s_axi_if.arready;

always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rd_ds_bypass <= 1'b1;
        rd_active    <= 1'b0;
    end
    else if (m_ar_hshake) begin
        rd_ds_bypass <= m_axi_if.arsize <= 2;
        rd_active    <= 1'b1;
        if (m_axi_if.arburst != AXI_BURST_INCR)
            $fatal("Burst type of %p not supported by 64-to-32 downsizer", axi_burst_e'(m_axi_if.arburst));
    end
    else if (m_r_hshake && m_axi_if.rlast) begin
        rd_ds_bypass <= 1'b1;
        rd_active    <= 1'b0;
    end
end
always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        s_axi_if.arvalid        <= 1'b0;

        m_axi_if_r_ctx.axaddr   <= '0;
        m_axi_if_r_ctx.axburst  <= '0;
        m_axi_if_r_ctx.axsize   <= '0;
        m_axi_if_r_ctx.axlen    <= '0;
        m_axi_if_r_ctx.axuser   <= '0;
        m_axi_if_r_ctx.axid     <= '0;
        m_axi_if_r_ctx.axlock   <= '0;
        m_axi_if_r_ctx.axcache  <= '0;
        m_axi_if_r_ctx.axprot   <= '0;
        m_axi_if_r_ctx.axregion <= '0;
        m_axi_if_r_ctx.axqos    <= '0;

        s_axi_if_r_ctx.axaddr   <= '0;
        s_axi_if_r_ctx.axburst  <= '0;
        s_axi_if_r_ctx.axsize   <= '0;
        s_axi_if_r_ctx.axlen    <= '0;
        s_axi_if_r_ctx.axuser   <= '0;
        s_axi_if_r_ctx.axid     <= '0;
        s_axi_if_r_ctx.axlock   <= '0;
        s_axi_if_r_ctx.axcache  <= '0;
        s_axi_if_r_ctx.axprot   <= '0;
        s_axi_if_r_ctx.axregion <= '0;
        s_axi_if_r_ctx.axqos    <= '0;
    end
    else if (m_ar_hshake) begin
        s_axi_if.arvalid        <= 1'b1;
        m_axi_if_r_ctx.axaddr   <= m_axi_if.araddr ;
        m_axi_if_r_ctx.axburst  <= m_axi_if.arburst;
        m_axi_if_r_ctx.axsize   <= m_axi_if.arsize ;
        m_axi_if_r_ctx.axlen    <= m_axi_if.arlen  ;
        m_axi_if_r_ctx.axuser   <= m_axi_if.aruser ;
        m_axi_if_r_ctx.axid     <= m_axi_if.arid   ;
        m_axi_if_r_ctx.axlock   <= m_axi_if.arlock ;
        m_axi_if_r_ctx.axcache  <= m_axi_if_arcache  ;
        m_axi_if_r_ctx.axprot   <= m_axi_if_arprot   ;
        m_axi_if_r_ctx.axregion <= m_axi_if_arregion ;
        m_axi_if_r_ctx.axqos    <= m_axi_if_arqos    ;

        s_axi_if_r_ctx.axaddr   <= m_axi_if.araddr ;
        s_axi_if_r_ctx.axburst  <= m_axi_if.arburst;
        s_axi_if_r_ctx.axuser   <= m_axi_if.aruser ;
        s_axi_if_r_ctx.axid     <= m_axi_if.arid   ;
        s_axi_if_r_ctx.axlock   <= m_axi_if.arlock ;
        s_axi_if_r_ctx.axcache  <= m_axi_if_arcache  ;
        s_axi_if_r_ctx.axprot   <= m_axi_if_arprot   ;
        s_axi_if_r_ctx.axregion <= m_axi_if_arregion ;
        s_axi_if_r_ctx.axqos    <= m_axi_if_arqos    ;
        if (m_axi_if.arsize <= 2) begin
            s_axi_if_r_ctx.axsize   <= m_axi_if.arsize ;
            s_axi_if_r_ctx.axlen    <= m_axi_if.arlen  ;
        end
        else if (m_axi_if.arsize == 3) begin
            s_axi_if_r_ctx.axsize  <= 2               ;
            s_axi_if_r_ctx.axlen   <= m_axi_if.arlen  * 2 + 1;
        end
        else begin
            $fatal("Unexpected value of arsize, 0x%x", m_axi_if.arsize);
        end
    end
    else if (s_ar_hshake) begin
        s_axi_if.arvalid       <= 1'b0;
    end
end

assign s_axi_if.araddr   = s_axi_if_r_ctx.axaddr  ;
assign s_axi_if.arburst  = s_axi_if_r_ctx.axburst ;
assign s_axi_if.arsize   = s_axi_if_r_ctx.axsize  ;
assign s_axi_if.arlen    = s_axi_if_r_ctx.axlen   ;
assign s_axi_if.aruser   = s_axi_if_r_ctx.axuser  ;
assign s_axi_if.arid     = s_axi_if_r_ctx.axid    ;
assign s_axi_if.arlock   = s_axi_if_r_ctx.axlock  ;
assign s_axi_if_arcache  = s_axi_if_r_ctx.axcache ;
assign s_axi_if_arprot   = s_axi_if_r_ctx.axprot  ;
assign s_axi_if_arregion = s_axi_if_r_ctx.axregion;
assign s_axi_if_arqos    = s_axi_if_r_ctx.axqos   ;

assign m_axi_if.arready = !rd_active;

always_comb begin
    m_axi_if.rvalid = rd_ds_bypass ? s_axi_if.rvalid : r_fifo_rvalid;
    m_axi_if.rdata  = rd_ds_bypass ? s_axi_if.rdata  : rd_qword;
    m_axi_if.rlast  = rd_ds_bypass ? s_axi_if.rlast  : rd_last;
    m_axi_if.rresp  = rd_ds_bypass ? s_axi_if.rresp  : rd_resp;
    m_axi_if.ruser  = rd_ds_bypass ? s_axi_if.ruser  : '0;
    m_axi_if.rid    = rd_ds_bypass ? s_axi_if.rid    : rd_rid;
    s_axi_if.rready = rd_ds_bypass ? m_axi_if.rready : r_fifo_wready;
    r_fifo_rready   = rd_ds_bypass ? 1'b0            : m_axi_if.rready;
end

assign m_r_hshake = m_axi_if.rvalid && m_axi_if.rready;
assign s_r_hshake = s_axi_if.rvalid && s_axi_if.rready;

always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rd_beat_upper <= 0;
    end
    else if (m_ar_hshake && m_axi_if.arsize == 3) begin
        rd_beat_upper <= 0;
    end
    else if (s_r_hshake) begin
        rd_beat_upper <= ~rd_beat_upper;
        rd_low_word   <= rd_beat_upper ? rd_low_word : s_axi_if.rdata[31:0];
        rd_low_resp   <= rd_beat_upper ? rd_low_resp : s_axi_if.rresp;
    end
end

assign r_fifo_wvalid = rd_ds_bypass ? 1'b0 : (s_r_hshake && rd_beat_upper);

assign r_fifo_wdata.data = {s_axi_if.rdata[63:32],rd_low_word};
assign r_fifo_wdata.resp = (s_axi_if.rresp | rd_low_resp);
assign r_fifo_wdata.rid  = s_axi_if.rid;
assign r_fifo_wdata.last = s_axi_if.rlast;

assign rd_qword = r_fifo_rdata.data;
assign rd_resp  = r_fifo_rdata.resp;
assign rd_rid   = r_fifo_rdata.rid;
assign rd_last  = r_fifo_rdata.last;

// --------- Read Data FIFO --------- //
caliptra_prim_fifo_sync #(
  .Width            ($bits(r_fifo_wdata)),
  .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
  .Depth            (FIFO_DEPTH),
  .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
  .Secure           (1'b0)  // use prim count for pointers; no secret data transmitted via DMA on AXI, no hardened counters
) i_fifo_rd (
  .clk_i   (clk     ),
  .rst_ni  (rst_n   ),
  // synchronous clear / flush port
  .clr_i   (1'b0),
  // write port
  .wvalid_i(r_fifo_wvalid),
  .wready_o(r_fifo_wready),
  .wdata_i (r_fifo_wdata),
  // read port
  .rvalid_o(r_fifo_rvalid),
  .rready_i(r_fifo_rready),
  .rdata_o (r_fifo_rdata),
  // occupancy
  .full_o  (r_fifo_full ),
  .depth_o (r_fifo_depth),
  .err_o   (r_fifo_error)
);

`CALIPTRA_ASSERT_NEVER(RD_FIFO_OFLOW, r_fifo_wvalid && !r_fifo_wready,                   clk, !rst_n)
`CALIPTRA_ASSERT_NEVER(RD_FIFO_FULL,  r_fifo_full,                                       clk, !rst_n)
`CALIPTRA_ASSERT_NEVER(RD_FIFO_ERROR, r_fifo_error,                                      clk, !rst_n)
`CALIPTRA_ASSERT      (RD_FIFO_UNUSED,(rd_ds_bypass || !rd_active) -> r_fifo_depth == 0, clk, !rst_n)


//==================================
// Write Downsizer
//==================================

assign m_aw_hshake = m_axi_if.awvalid && m_axi_if.awready;
assign s_aw_hshake = s_axi_if.awvalid && s_axi_if.awready;

always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_ds_bypass <= 1'b1;
        wr_active    <= 1'b0;
    end
    else if (m_aw_hshake) begin
        wr_ds_bypass <= m_axi_if.awsize <= 2;
        wr_active    <= 1'b1;
        if (m_axi_if.awburst != AXI_BURST_INCR)
            $fatal("Burst type of %s not supported by 64-to-32 downsizer", axi_burst_e'(m_axi_if.awburst));
    end
    else if (s_w_hshake && s_axi_if.wlast) begin
        wr_ds_bypass <= 1'b1;
        wr_active    <= 1'b0;
    end
end
always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        s_axi_if.awvalid        <= 1'b0;

        m_axi_if_w_ctx.axaddr   <= '0;
        m_axi_if_w_ctx.axburst  <= '0;
        m_axi_if_w_ctx.axsize   <= '0;
        m_axi_if_w_ctx.axlen    <= '0;
        m_axi_if_w_ctx.axuser   <= '0;
        m_axi_if_w_ctx.axid     <= '0;
        m_axi_if_w_ctx.axlock   <= '0;
        m_axi_if_w_ctx.axcache  <= '0;
        m_axi_if_w_ctx.axprot   <= '0;
        m_axi_if_w_ctx.axregion <= '0;
        m_axi_if_w_ctx.axqos    <= '0;

        s_axi_if_w_ctx.axaddr   <= '0;
        s_axi_if_w_ctx.axburst  <= '0;
        s_axi_if_w_ctx.axsize   <= '0;
        s_axi_if_w_ctx.axlen    <= '0;
        s_axi_if_w_ctx.axuser   <= '0;
        s_axi_if_w_ctx.axid     <= '0;
        s_axi_if_w_ctx.axlock   <= '0;
        s_axi_if_w_ctx.axcache  <= '0;
        s_axi_if_w_ctx.axprot   <= '0;
        s_axi_if_w_ctx.axregion <= '0;
        s_axi_if_w_ctx.axqos    <= '0;
    end
    else if (m_aw_hshake) begin
        s_axi_if.awvalid        <= 1'b1;
        m_axi_if_w_ctx.axaddr   <= m_axi_if.awaddr ;
        m_axi_if_w_ctx.axburst  <= m_axi_if.awburst;
        m_axi_if_w_ctx.axsize   <= m_axi_if.awsize ;
        m_axi_if_w_ctx.axlen    <= m_axi_if.awlen  ;
        m_axi_if_w_ctx.axuser   <= m_axi_if.awuser ;
        m_axi_if_w_ctx.axid     <= m_axi_if.awid   ;
        m_axi_if_w_ctx.axlock   <= m_axi_if.awlock ;
        m_axi_if_w_ctx.axcache  <= m_axi_if_awcache  ;
        m_axi_if_w_ctx.axprot   <= m_axi_if_awprot   ;
        m_axi_if_w_ctx.axregion <= m_axi_if_awregion ;
        m_axi_if_w_ctx.axqos    <= m_axi_if_awqos    ;

        s_axi_if_w_ctx.axaddr   <= m_axi_if.awaddr ;
        s_axi_if_w_ctx.axburst  <= m_axi_if.awburst;
        s_axi_if_w_ctx.axuser   <= m_axi_if.awuser ;
        s_axi_if_w_ctx.axid     <= m_axi_if.awid   ;
        s_axi_if_w_ctx.axlock   <= m_axi_if.awlock ;
        s_axi_if_w_ctx.axcache  <= m_axi_if_awcache  ;
        s_axi_if_w_ctx.axprot   <= m_axi_if_awprot   ;
        s_axi_if_w_ctx.axregion <= m_axi_if_awregion ;
        s_axi_if_w_ctx.axqos    <= m_axi_if_awqos    ;
        if (m_axi_if.awsize <= 2) begin
            s_axi_if_w_ctx.axsize   <= m_axi_if.awsize ;
            s_axi_if_w_ctx.axlen    <= m_axi_if.awlen  ;
        end
        else if (m_axi_if.awsize == 3) begin
            s_axi_if_w_ctx.axsize   <= 2               ;
            s_axi_if_w_ctx.axlen    <= m_axi_if.awlen  * 2 + 1;
        end
        else begin
            $fatal("Unexpected value of awsize, 0x%x", m_axi_if.awsize);
        end
    end
    else if (s_aw_hshake) begin
        s_axi_if.awvalid       <= 1'b0;
    end
end

assign s_axi_if.awaddr   = s_axi_if_w_ctx.axaddr  ;
assign s_axi_if.awburst  = s_axi_if_w_ctx.axburst ;
assign s_axi_if.awsize   = s_axi_if_w_ctx.axsize  ;
assign s_axi_if.awlen    = s_axi_if_w_ctx.axlen   ;
assign s_axi_if.awuser   = s_axi_if_w_ctx.axuser  ;
assign s_axi_if.awid     = s_axi_if_w_ctx.axid    ;
assign s_axi_if.awlock   = s_axi_if_w_ctx.axlock  ;
assign s_axi_if_awcache  = s_axi_if_w_ctx.axcache ;
assign s_axi_if_awprot   = s_axi_if_w_ctx.axprot  ;
assign s_axi_if_awregion = s_axi_if_w_ctx.axregion;
assign s_axi_if_awqos    = s_axi_if_w_ctx.axqos   ;

assign m_axi_if.awready = !wr_active;

assign w_fifo_wvalid   =  wr_ds_bypass               ? 1'b0 : m_axi_if.wvalid;
assign m_axi_if.wready = (wr_ds_bypass && wr_active) ? s_axi_if.wready : wr_active ? w_fifo_wready : '0;

assign m_w_hshake = m_axi_if.wvalid && m_axi_if.wready;
assign s_w_hshake = s_axi_if.wvalid && s_axi_if.wready;

always_ff@(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_beat_upper <= 0;
    end
    else if (m_aw_hshake && m_axi_if.awsize == 3) begin
        wr_beat_upper <= 0;
    end
    else if (s_w_hshake) begin
        wr_beat_upper <= ~wr_beat_upper;
    end
end

always_comb begin
    s_axi_if.wvalid = (wr_ds_bypass && wr_active) ? m_axi_if.wvalid : w_fifo_rvalid;
    s_axi_if.wdata  = (wr_ds_bypass && wr_active) ? m_axi_if.wdata  : wr_beat_upper ? {wr_qword[63:32],32'h0}   : {32'h0,wr_qword[31: 0]};
    s_axi_if.wlast  = (wr_ds_bypass && wr_active) ? m_axi_if.wlast  : wr_beat_upper ? wr_last                   : 1'b0;
    s_axi_if.wstrb  = (wr_ds_bypass && wr_active) ? m_axi_if.wstrb  : wr_beat_upper ? {wr_qword_strb[7:4],4'h0} : {4'h0,wr_qword_strb[3:0]};
    s_axi_if.wuser  = (wr_ds_bypass && wr_active) ? m_axi_if.wuser  : '0;

    w_fifo_rready   = (wr_ds_bypass             ) ? 1'b0            : wr_beat_upper ? s_axi_if.wready           : 1'b0;
end

assign w_fifo_wdata.data = m_axi_if.wdata;
assign w_fifo_wdata.strb = m_axi_if.wstrb;
assign w_fifo_wdata.last = m_axi_if.wlast;

assign wr_qword      = w_fifo_rdata.data;
assign wr_qword_strb = w_fifo_rdata.strb;
assign wr_last       = w_fifo_rdata.last;

// --------- Write Data FIFO --------- //
caliptra_prim_fifo_sync #(
  .Width            ($bits(w_fifo_wdata)),
  .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
  .Depth            (FIFO_DEPTH),
  .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
  .Secure           (1'b0)  // use prim count for pointers; no secret data transmitted via DMA on AXI, no hardened counters
) i_fifo_wr (
  .clk_i   (clk     ),
  .rst_ni  (rst_n   ),
  // synchronous clear / flush port
  .clr_i   (1'b0),
  // write port
  .wvalid_i(w_fifo_wvalid),
  .wready_o(w_fifo_wready),
  .wdata_i (w_fifo_wdata),
  // read port
  .rvalid_o(w_fifo_rvalid),
  .rready_i(w_fifo_rready),
  .rdata_o (w_fifo_rdata ),
  // occupancy
  .full_o  (w_fifo_full ),
  .depth_o (w_fifo_depth),
  .err_o   (w_fifo_error)
);

// No conversion on Write Response Channel
assign m_axi_if.bresp  = s_axi_if.bresp ;
assign m_axi_if.bid    = s_axi_if.bid   ;
assign m_axi_if.buser  = s_axi_if.buser ;
assign m_axi_if.bvalid = s_axi_if.bvalid;
assign s_axi_if.bready = m_axi_if.bready;

`CALIPTRA_ASSERT_NEVER(WR_FIFO_OFLOW, w_fifo_wvalid && !w_fifo_wready,                   clk, !rst_n)
`CALIPTRA_ASSERT_NEVER(WR_FIFO_FULL,  w_fifo_full,                                       clk, !rst_n)
`CALIPTRA_ASSERT_NEVER(WR_FIFO_ERROR, w_fifo_error,                                      clk, !rst_n)
`CALIPTRA_ASSERT      (WR_FIFO_UNUSED,(wr_ds_bypass || !wr_active) -> w_fifo_depth == 0, clk, !rst_n)

    //=========================================================================-
    // AXI Protocol Checker
    //=========================================================================-
    `ifdef AXI4PC
        Axi4PC #(
            .DATA_WIDTH  ($bits(m_axi_if.rdata  )),
            .WID_WIDTH   ($bits(m_axi_if.rid    )),
            .RID_WIDTH   ($bits(m_axi_if.rid    )),
            .ADDR_WIDTH  ($bits(m_axi_if.araddr )),
            .AWUSER_WIDTH($bits(m_axi_if.awuser )),
            .WUSER_WIDTH ($bits(m_axi_if.wuser  )),
            .BUSER_WIDTH ($bits(m_axi_if.buser  )),
            .ARUSER_WIDTH($bits(m_axi_if.aruser )),
            .RUSER_WIDTH ($bits(m_axi_if.ruser  )),
//            .MAXWAITS    (256                         ),
            .RecMaxWaitOn(0                           )
        ) axi4_pc_inst (
            // Global Signals
            .ACLK   (clk   ),
            .ARESETn(rst_n ),

            // Write Address Channel
            .AWID    (m_axi_if.awid),
            .AWADDR  (m_axi_if.awaddr),
            .AWLEN   (m_axi_if.awlen),
            .AWSIZE  (m_axi_if.awsize),
            .AWBURST (m_axi_if.awburst),
            .AWLOCK  (m_axi_if.awlock),
            .AWCACHE (m_axi_if_awcache ),
            .AWPROT  (m_axi_if_awprot  ),
            .AWQOS   (m_axi_if_awqos   ),
            .AWREGION(m_axi_if_awregion),
            .AWUSER  (m_axi_if.awuser),
            .AWVALID (m_axi_if.awvalid),
            .AWREADY (m_axi_if.awready),

            // Write Channel
            .WLAST   (m_axi_if.wlast),
            .WDATA   (m_axi_if.wdata),
            .WSTRB   (m_axi_if.wstrb),
            .WUSER   (m_axi_if.wuser),
            .WVALID  (m_axi_if.wvalid),
            .WREADY  (m_axi_if.wready),

            // Write Response Channel
            .BID     (m_axi_if.bid),
            .BRESP   (m_axi_if.bresp),
            .BUSER   (m_axi_if.buser),
            .BVALID  (m_axi_if.bvalid),
            .BREADY  (m_axi_if.bready),

            // Read Address Channel
            .ARID    (m_axi_if.arid),
            .ARADDR  (m_axi_if.araddr),
            .ARLEN   (m_axi_if.arlen),
            .ARSIZE  (m_axi_if.arsize),
            .ARBURST (m_axi_if.arburst),
            .ARLOCK  (m_axi_if.arlock),
            .ARCACHE (m_axi_if_arcache ),
            .ARPROT  (m_axi_if_arprot  ),
            .ARQOS   (m_axi_if_arqos   ),
            .ARREGION(m_axi_if_arregion),
            .ARUSER  (m_axi_if.aruser),
            .ARVALID (m_axi_if.arvalid),
            .ARREADY (m_axi_if.arready),

            // Read Channel
            .RID     (m_axi_if.rid),
            .RLAST   (m_axi_if.rlast),
            .RDATA   (m_axi_if.rdata),
            .RRESP   (m_axi_if.rresp),
            .RUSER   (m_axi_if.ruser),
            .RVALID  (m_axi_if.rvalid),
            .RREADY  (m_axi_if.rready),

            // Low power interface
            .CACTIVE (1'b0),
            .CSYSREQ (1'b0),
            .CSYSACK (1'b0)
        );
    `endif

endmodule
