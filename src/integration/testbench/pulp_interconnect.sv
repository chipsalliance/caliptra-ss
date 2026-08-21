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

`timescale 1ps/1ps

module pulp_interconnect
  import caliptra_ss_top_tb_axi_pkg::*;
(
  input  logic                   core_clk,
  input  logic                   rst_l,
  // Manager ports: the TB drives the requests, reads the responses.
  input  axi_req_t [NumMgr-1:0]  mgr_req_i,
  output axi_rsp_t [NumMgr-1:0]  mgr_rsp_o,
  // Subordinate ports: the TB reads the requests, drives the responses.
  output axi_req_t [NumSub-1:0]  sub_req_o,
  input  axi_rsp_t [NumSub-1:0]  sub_rsp_i
);

  axi_req_t      [NumMgr-1:0] xbar_mgr_reqs;  // Into the xbar subordinate ports
  axi_rsp_t      [NumMgr-1:0] xbar_mgr_rsps;
  axi_xbar_req_t [NumSub-1:0] xbar_sub_reqs;  // Out of the xbar manager ports
  axi_xbar_rsp_t [NumSub-1:0] xbar_sub_rsps;

  //--------------------------------------------------------------------------
  // Manager ports -> xbar
  //--------------------------------------------------------------------------
  for (genvar gi = 0; gi < NumMgr; gi++) begin : gen_mgr_ports
    if (MgrPortNarrow[gi]) begin : gen_narrow
      // 32-bit manager: data sits on byte lanes [3:0] of the 64-bit struct
      // fields; repack into the narrow types and upsize to the 64-bit xbar.
      axi_nrw_req_t mgr_nrw_req;
      axi_nrw_rsp_t mgr_nrw_rsp;

      assign mgr_nrw_req.aw       = mgr_req_i[gi].aw;
      assign mgr_nrw_req.aw_valid = mgr_req_i[gi].aw_valid;
      assign mgr_nrw_req.w.data   = mgr_req_i[gi].w.data[NarrowDataWidth-1:0];
      assign mgr_nrw_req.w.strb   = mgr_req_i[gi].w.strb[NarrowDataWidth/8-1:0];
      assign mgr_nrw_req.w.last   = mgr_req_i[gi].w.last;
      assign mgr_nrw_req.w.user   = mgr_req_i[gi].w.user;
      assign mgr_nrw_req.w_valid  = mgr_req_i[gi].w_valid;
      assign mgr_nrw_req.b_ready  = mgr_req_i[gi].b_ready;
      assign mgr_nrw_req.ar       = mgr_req_i[gi].ar;
      assign mgr_nrw_req.ar_valid = mgr_req_i[gi].ar_valid;
      assign mgr_nrw_req.r_ready  = mgr_req_i[gi].r_ready;

      assign mgr_rsp_o[gi].aw_ready = mgr_nrw_rsp.aw_ready;
      assign mgr_rsp_o[gi].w_ready  = mgr_nrw_rsp.w_ready;
      assign mgr_rsp_o[gi].b        = mgr_nrw_rsp.b;
      assign mgr_rsp_o[gi].b_valid  = mgr_nrw_rsp.b_valid;
      assign mgr_rsp_o[gi].ar_ready = mgr_nrw_rsp.ar_ready;
      assign mgr_rsp_o[gi].r.id     = mgr_nrw_rsp.r.id;
      assign mgr_rsp_o[gi].r.data   = axi_data_t'(mgr_nrw_rsp.r.data);
      assign mgr_rsp_o[gi].r.resp   = mgr_nrw_rsp.r.resp;
      assign mgr_rsp_o[gi].r.last   = mgr_nrw_rsp.r.last;
      assign mgr_rsp_o[gi].r.user   = mgr_nrw_rsp.r.user;
      assign mgr_rsp_o[gi].r_valid  = mgr_nrw_rsp.r_valid;

      caliptra_ss_tb_axi_dw_converter #(
        .AxiMaxReads             ( 8                ),
        .AxiSlvPortDataWidth     ( NarrowDataWidth  ),
        .AxiMstPortDataWidth     ( DataWidth        ),
        .AxiAddrWidth            ( AddrWidth        ),
        .AxiIdWidth              ( MgrIdWidth       ),
        .caliptra_ss_tb_aw_chan_t( axi_aw_t         ),
        .mst_w_chan_t            ( axi_w_t          ),
        .slv_w_chan_t            ( axi_nrw_w_t      ),
        .caliptra_ss_tb_b_chan_t ( axi_b_t          ),
        .caliptra_ss_tb_ar_chan_t( axi_ar_t         ),
        .mst_r_chan_t            ( axi_r_t          ),
        .slv_r_chan_t            ( axi_nrw_r_t      ),
        .axi_mst_req_t           ( axi_req_t        ),
        .axi_mst_resp_t          ( axi_rsp_t        ),
        .axi_slv_req_t           ( axi_nrw_req_t    ),
        .axi_slv_resp_t          ( axi_nrw_rsp_t    )
      ) u_axi_dw_upsizer (
        .clk_i      ( core_clk          ),
        .rst_ni     ( rst_l             ),
        .slv_req_i  ( mgr_nrw_req       ),
        .slv_resp_o ( mgr_nrw_rsp       ),
        .mst_req_o  ( xbar_mgr_reqs[gi] ),
        .mst_resp_i ( xbar_mgr_rsps[gi] )
      );
    end else begin : gen_native
      // Native 64-bit manager: connect directly to the crossbar.
      assign xbar_mgr_reqs[gi] = mgr_req_i[gi];
      assign mgr_rsp_o[gi]     = xbar_mgr_rsps[gi];
    end
  end

  //--------------------------------------------------------------------------
  // Crossbar.  Unmapped addresses terminate in the internal error subordinate
  //--------------------------------------------------------------------------
  caliptra_ss_tb_axi_xbar #(
    .Cfg                     ( XbarCfg        ),
    .ATOPs                   ( 1'b0           ),
    .slv_aw_chan_t           ( axi_aw_t       ),
    .mst_aw_chan_t           ( axi_xbar_aw_t  ),
    .caliptra_ss_tb_w_chan_t ( axi_w_t        ),
    .slv_b_chan_t            ( axi_b_t        ),
    .mst_b_chan_t            ( axi_xbar_b_t   ),
    .slv_ar_chan_t           ( axi_ar_t       ),
    .mst_ar_chan_t           ( axi_xbar_ar_t  ),
    .slv_r_chan_t            ( axi_r_t        ),
    .mst_r_chan_t            ( axi_xbar_r_t   ),
    .slv_req_t               ( axi_req_t      ),
    .slv_resp_t              ( axi_rsp_t      ),
    .mst_req_t               ( axi_xbar_req_t ),
    .mst_resp_t              ( axi_xbar_rsp_t ),
    .rule_t                  ( caliptra_ss_tb_axi_pkg::caliptra_ss_tb_xbar_rule_64_t )
  ) u_axi_xbar (
    .clk_i                 ( core_clk      ),
    .rst_ni                ( rst_l         ),
    .test_i                ( 1'b0          ),
    .slv_ports_req_i       ( xbar_mgr_reqs ),
    .slv_ports_resp_o      ( xbar_mgr_rsps ),
    .mst_ports_req_o       ( xbar_sub_reqs ),
    .mst_ports_resp_i      ( xbar_sub_rsps ),
    .addr_map_i            ( AddrMap       ),
    .en_default_mst_port_i ( '0            ),
    .default_mst_port_i    ( '0            )
  );

  //--------------------------------------------------------------------------
  // xbar -> ID width converter (-> DW converter) -> subordinate ports
  //--------------------------------------------------------------------------
  for (genvar gj = 0; gj < NumSub; gj++) begin : gen_sub_ports
    axi_req_t sub_req;  // manager-port ID width again, native 64-bit data
    axi_rsp_t sub_rsp;

    // Convert the xbar master-port ID width back down so that subordinate
    // ports see the same ID width as the manager ports.
    caliptra_ss_tb_axi_iw_converter #(
      .AxiSlvPortIdWidth      ( XbarSubIdWidth ),
      .AxiMstPortIdWidth      ( MgrIdWidth     ),
      .AxiSlvPortMaxUniqIds   ( 16             ),
      .AxiSlvPortMaxTxnsPerId ( 4              ),
      .AxiAddrWidth           ( AddrWidth      ),
      .AxiDataWidth           ( DataWidth      ),
      .AxiUserWidth           ( UserWidth      ),
      .slv_req_t              ( axi_xbar_req_t ),
      .slv_resp_t             ( axi_xbar_rsp_t ),
      .mst_req_t              ( axi_req_t      ),
      .mst_resp_t             ( axi_rsp_t      )
    ) u_axi_iw_converter (
      .clk_i      ( core_clk          ),
      .rst_ni     ( rst_l             ),
      .slv_req_i  ( xbar_sub_reqs[gj] ),
      .slv_resp_o ( xbar_sub_rsps[gj] ),
      .mst_req_o  ( sub_req           ),
      .mst_resp_i ( sub_rsp           )
    );

    if (SubPortNarrow[gj]) begin : gen_narrow
      // 32-bit subordinate: downsize so that data is always presented on
      // byte lanes [3:0] of the 64-bit struct fields.
      axi_nrw_req_t sub_nrw_req;
      axi_nrw_rsp_t sub_nrw_rsp;

      caliptra_ss_tb_axi_dw_converter #(
        .AxiMaxReads             ( 8                ),
        .AxiSlvPortDataWidth     ( DataWidth        ),
        .AxiMstPortDataWidth     ( NarrowDataWidth  ),
        .AxiAddrWidth            ( AddrWidth        ),
        .AxiIdWidth              ( MgrIdWidth       ),
        .caliptra_ss_tb_aw_chan_t( axi_aw_t         ),
        .mst_w_chan_t            ( axi_nrw_w_t      ),
        .slv_w_chan_t            ( axi_w_t          ),
        .caliptra_ss_tb_b_chan_t ( axi_b_t          ),
        .caliptra_ss_tb_ar_chan_t( axi_ar_t         ),
        .mst_r_chan_t            ( axi_nrw_r_t      ),
        .slv_r_chan_t            ( axi_r_t          ),
        .axi_mst_req_t           ( axi_nrw_req_t    ),
        .axi_mst_resp_t          ( axi_nrw_rsp_t    ),
        .axi_slv_req_t           ( axi_req_t        ),
        .axi_slv_resp_t          ( axi_rsp_t        )
      ) u_axi_dw_downsizer (
        .clk_i      ( core_clk    ),
        .rst_ni     ( rst_l       ),
        .slv_req_i  ( sub_req     ),
        .slv_resp_o ( sub_rsp     ),
        .mst_req_o  ( sub_nrw_req ),
        .mst_resp_i ( sub_nrw_rsp )
      );

      assign sub_req_o[gj].aw       = sub_nrw_req.aw;
      assign sub_req_o[gj].aw_valid = sub_nrw_req.aw_valid;
      assign sub_req_o[gj].w.data   = axi_data_t'(sub_nrw_req.w.data);
      assign sub_req_o[gj].w.strb   = axi_strb_t'(sub_nrw_req.w.strb);
      assign sub_req_o[gj].w.last   = sub_nrw_req.w.last;
      assign sub_req_o[gj].w.user   = sub_nrw_req.w.user;
      assign sub_req_o[gj].w_valid  = sub_nrw_req.w_valid;
      assign sub_req_o[gj].b_ready  = sub_nrw_req.b_ready;
      assign sub_req_o[gj].ar       = sub_nrw_req.ar;
      assign sub_req_o[gj].ar_valid = sub_nrw_req.ar_valid;
      assign sub_req_o[gj].r_ready  = sub_nrw_req.r_ready;

      assign sub_nrw_rsp.aw_ready = sub_rsp_i[gj].aw_ready;
      assign sub_nrw_rsp.w_ready  = sub_rsp_i[gj].w_ready;
      assign sub_nrw_rsp.b        = sub_rsp_i[gj].b;
      assign sub_nrw_rsp.b_valid  = sub_rsp_i[gj].b_valid;
      assign sub_nrw_rsp.ar_ready = sub_rsp_i[gj].ar_ready;
      assign sub_nrw_rsp.r.id     = sub_rsp_i[gj].r.id;
      assign sub_nrw_rsp.r.data   = sub_rsp_i[gj].r.data[NarrowDataWidth-1:0];
      assign sub_nrw_rsp.r.resp   = sub_rsp_i[gj].r.resp;
      assign sub_nrw_rsp.r.last   = sub_rsp_i[gj].r.last;
      assign sub_nrw_rsp.r.user   = sub_rsp_i[gj].r.user;
      assign sub_nrw_rsp.r_valid  = sub_rsp_i[gj].r_valid;
    end else begin : gen_native
      // Native 64-bit subordinate.
      assign sub_req_o[gj] = sub_req;
      assign sub_rsp       = sub_rsp_i[gj];
    end
  end

`ifdef TB_PULP_AXI4PC
  //--------------------------------------------------------------------------
  // ARM Axi4PC (BP063) protocol checkers, one per port (replaces the former
  // Avery AXI monitors).  DATA_WIDTH matches the port's native width: 32-bit
  // ports keep their data on byte lanes [3:0] of the 64-bit struct fields,
  // which would violate the AXI lane-steering rules on a true 64-bit bus.
  //--------------------------------------------------------------------------
  for (genvar gi = 0; gi < NumMgr; gi++) begin : gen_mgr_pc
    localparam int unsigned PcDataWidth = MgrPortNarrow[gi] ? NarrowDataWidth : DataWidth;
    Axi4PC #(
      .DATA_WIDTH   ( PcDataWidth ),
      .ADDR_WIDTH   ( AddrWidth   ),
      .WID_WIDTH    ( MgrIdWidth  ),
      .RID_WIDTH    ( MgrIdWidth  ),
      .AWUSER_WIDTH ( UserWidth   ),
      .WUSER_WIDTH  ( UserWidth   ),
      .BUSER_WIDTH  ( UserWidth   ),
      .ARUSER_WIDTH ( UserWidth   ),
      .RUSER_WIDTH  ( UserWidth   ),
      .RecMaxWaitOn ( 0           )
    ) u_axi4pc (
      .ACLK    ( core_clk ),
      .ARESETn ( rst_l    ),
      .AWID    ( mgr_req_i[gi].aw.id     ),
      .AWADDR  ( mgr_req_i[gi].aw.addr   ),
      .AWLEN   ( mgr_req_i[gi].aw.len    ),
      .AWSIZE  ( mgr_req_i[gi].aw.size   ),
      .AWBURST ( mgr_req_i[gi].aw.burst  ),
      .AWLOCK  ( mgr_req_i[gi].aw.lock   ),
      .AWCACHE ( mgr_req_i[gi].aw.cache  ),
      .AWPROT  ( mgr_req_i[gi].aw.prot   ),
      .AWQOS   ( mgr_req_i[gi].aw.qos    ),
      .AWREGION( mgr_req_i[gi].aw.region ),
      .AWUSER  ( mgr_req_i[gi].aw.user   ),
      .AWVALID ( mgr_req_i[gi].aw_valid  ),
      .AWREADY ( mgr_rsp_o[gi].aw_ready  ),
      .WLAST   ( mgr_req_i[gi].w.last    ),
      .WDATA   ( mgr_req_i[gi].w.data[PcDataWidth-1:0]   ),
      .WSTRB   ( mgr_req_i[gi].w.strb[PcDataWidth/8-1:0] ),
      .WUSER   ( mgr_req_i[gi].w.user    ),
      .WVALID  ( mgr_req_i[gi].w_valid   ),
      .WREADY  ( mgr_rsp_o[gi].w_ready   ),
      .BID     ( mgr_rsp_o[gi].b.id      ),
      .BRESP   ( mgr_rsp_o[gi].b.resp    ),
      .BUSER   ( mgr_rsp_o[gi].b.user    ),
      .BVALID  ( mgr_rsp_o[gi].b_valid   ),
      .BREADY  ( mgr_req_i[gi].b_ready   ),
      .ARID    ( mgr_req_i[gi].ar.id     ),
      .ARADDR  ( mgr_req_i[gi].ar.addr   ),
      .ARLEN   ( mgr_req_i[gi].ar.len    ),
      .ARSIZE  ( mgr_req_i[gi].ar.size   ),
      .ARBURST ( mgr_req_i[gi].ar.burst  ),
      .ARLOCK  ( mgr_req_i[gi].ar.lock   ),
      .ARCACHE ( mgr_req_i[gi].ar.cache  ),
      .ARPROT  ( mgr_req_i[gi].ar.prot   ),
      .ARQOS   ( mgr_req_i[gi].ar.qos    ),
      .ARREGION( mgr_req_i[gi].ar.region ),
      .ARUSER  ( mgr_req_i[gi].ar.user   ),
      .ARVALID ( mgr_req_i[gi].ar_valid  ),
      .ARREADY ( mgr_rsp_o[gi].ar_ready  ),
      .RID     ( mgr_rsp_o[gi].r.id      ),
      .RLAST   ( mgr_rsp_o[gi].r.last    ),
      .RDATA   ( mgr_rsp_o[gi].r.data[PcDataWidth-1:0] ),
      .RRESP   ( mgr_rsp_o[gi].r.resp    ),
      .RUSER   ( mgr_rsp_o[gi].r.user    ),
      .RVALID  ( mgr_rsp_o[gi].r_valid   ),
      .RREADY  ( mgr_req_i[gi].r_ready   ),
      .CACTIVE ( 1'b0 ),
      .CSYSREQ ( 1'b0 ),
      .CSYSACK ( 1'b0 )
    );
  end

  for (genvar gj = 0; gj < NumSub; gj++) begin : gen_sub_pc
    localparam int unsigned PcDataWidth = SubPortNarrow[gj] ? NarrowDataWidth : DataWidth;
    Axi4PC #(
      .DATA_WIDTH   ( PcDataWidth ),
      .ADDR_WIDTH   ( AddrWidth   ),
      .WID_WIDTH    ( MgrIdWidth  ),
      .RID_WIDTH    ( MgrIdWidth  ),
      .AWUSER_WIDTH ( UserWidth   ),
      .WUSER_WIDTH  ( UserWidth   ),
      .BUSER_WIDTH  ( UserWidth   ),
      .ARUSER_WIDTH ( UserWidth   ),
      .RUSER_WIDTH  ( UserWidth   ),
      .RecMaxWaitOn ( 0           )
    ) u_axi4pc (
      .ACLK    ( core_clk ),
      .ARESETn ( rst_l    ),
      .AWID    ( sub_req_o[gj].aw.id     ),
      .AWADDR  ( sub_req_o[gj].aw.addr   ),
      .AWLEN   ( sub_req_o[gj].aw.len    ),
      .AWSIZE  ( sub_req_o[gj].aw.size   ),
      .AWBURST ( sub_req_o[gj].aw.burst  ),
      .AWLOCK  ( sub_req_o[gj].aw.lock   ),
      .AWCACHE ( sub_req_o[gj].aw.cache  ),
      .AWPROT  ( sub_req_o[gj].aw.prot   ),
      .AWQOS   ( sub_req_o[gj].aw.qos    ),
      .AWREGION( sub_req_o[gj].aw.region ),
      .AWUSER  ( sub_req_o[gj].aw.user   ),
      .AWVALID ( sub_req_o[gj].aw_valid  ),
      .AWREADY ( sub_rsp_i[gj].aw_ready  ),
      .WLAST   ( sub_req_o[gj].w.last    ),
      .WDATA   ( sub_req_o[gj].w.data[PcDataWidth-1:0]   ),
      .WSTRB   ( sub_req_o[gj].w.strb[PcDataWidth/8-1:0] ),
      .WUSER   ( sub_req_o[gj].w.user    ),
      .WVALID  ( sub_req_o[gj].w_valid   ),
      .WREADY  ( sub_rsp_i[gj].w_ready   ),
      .BID     ( sub_rsp_i[gj].b.id      ),
      .BRESP   ( sub_rsp_i[gj].b.resp    ),
      .BUSER   ( sub_rsp_i[gj].b.user    ),
      .BVALID  ( sub_rsp_i[gj].b_valid   ),
      .BREADY  ( sub_req_o[gj].b_ready   ),
      .ARID    ( sub_req_o[gj].ar.id     ),
      .ARADDR  ( sub_req_o[gj].ar.addr   ),
      .ARLEN   ( sub_req_o[gj].ar.len    ),
      .ARSIZE  ( sub_req_o[gj].ar.size   ),
      .ARBURST ( sub_req_o[gj].ar.burst  ),
      .ARLOCK  ( sub_req_o[gj].ar.lock   ),
      .ARCACHE ( sub_req_o[gj].ar.cache  ),
      .ARPROT  ( sub_req_o[gj].ar.prot   ),
      .ARQOS   ( sub_req_o[gj].ar.qos    ),
      .ARREGION( sub_req_o[gj].ar.region ),
      .ARUSER  ( sub_req_o[gj].ar.user   ),
      .ARVALID ( sub_req_o[gj].ar_valid  ),
      .ARREADY ( sub_rsp_i[gj].ar_ready  ),
      .RID     ( sub_rsp_i[gj].r.id      ),
      .RLAST   ( sub_rsp_i[gj].r.last    ),
      .RDATA   ( sub_rsp_i[gj].r.data[PcDataWidth-1:0] ),
      .RRESP   ( sub_rsp_i[gj].r.resp    ),
      .RUSER   ( sub_rsp_i[gj].r.user    ),
      .RVALID  ( sub_rsp_i[gj].r_valid   ),
      .RREADY  ( sub_req_o[gj].r_ready   ),
      .CACTIVE ( 1'b0 ),
      .CSYSREQ ( 1'b0 ),
      .CSYSACK ( 1'b0 )
    );
  end
`endif

endmodule
