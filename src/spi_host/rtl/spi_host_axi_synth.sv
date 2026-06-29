// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synthesis wrapper for spi_host_axi.

module spi_host_axi_synth #(
  parameter int unsigned NumCS    = 2,
  parameter int unsigned CmdDepth = 8,
  parameter int unsigned AxiAw    = 32,
  parameter int unsigned AxiDw    = 32,
  parameter int unsigned AxiUw    = 32,
  parameter int unsigned AxiIw    = 1
) (
  input  logic clk_i,
  input  logic rst_ni,

  // AXI AW channel
  input  logic [AxiAw-1:0] s_axi_awaddr_i,
  input  logic [1:0]       s_axi_awburst_i,
  input  logic [2:0]       s_axi_awsize_i,
  input  logic [7:0]       s_axi_awlen_i,
  input  logic [AxiUw-1:0] s_axi_awuser_i,
  input  logic [AxiIw-1:0] s_axi_awid_i,
  input  logic             s_axi_awlock_i,
  input  logic             s_axi_awvalid_i,
  output logic             s_axi_awready_o,

  // AXI W channel
  input  logic [AxiDw-1:0]   s_axi_wdata_i,
  input  logic [AxiDw/8-1:0] s_axi_wstrb_i,
  input  logic [AxiUw-1:0]   s_axi_wuser_i,
  input  logic               s_axi_wvalid_i,
  output logic               s_axi_wready_o,
  input  logic               s_axi_wlast_i,

  // AXI B channel
  output logic [1:0]       s_axi_bresp_o,
  output logic [AxiIw-1:0] s_axi_bid_o,
  output logic [AxiUw-1:0] s_axi_buser_o,
  output logic             s_axi_bvalid_o,
  input  logic             s_axi_bready_i,

  // AXI AR channel
  input  logic [AxiAw-1:0] s_axi_araddr_i,
  input  logic [1:0]       s_axi_arburst_i,
  input  logic [2:0]       s_axi_arsize_i,
  input  logic [7:0]       s_axi_arlen_i,
  input  logic [AxiUw-1:0] s_axi_aruser_i,
  input  logic [AxiIw-1:0] s_axi_arid_i,
  input  logic             s_axi_arlock_i,
  input  logic             s_axi_arvalid_i,
  output logic             s_axi_arready_o,

  // AXI R channel
  output logic [AxiDw-1:0] s_axi_rdata_o,
  output logic [1:0]       s_axi_rresp_o,
  output logic [AxiIw-1:0] s_axi_rid_o,
  output logic [AxiUw-1:0] s_axi_ruser_o,
  output logic             s_axi_rlast_o,
  output logic             s_axi_rvalid_o,
  input  logic             s_axi_rready_i,

  // Register integrity error
  output logic intg_error_o,

  // SPI interface
  output logic             cio_sck_o,
  output logic [NumCS-1:0] cio_csb_o,
  inout  logic [3:0]       cio_sd_io,

  output logic intr_error_o,
  output logic intr_spi_event_o
);

  logic             cio_sck;
  logic             cio_sck_en;
  logic [NumCS-1:0] cio_csb;
  logic [NumCS-1:0] cio_csb_en;
  logic [3:0]       cio_sd_out;
  logic [3:0]       cio_sd_en;
  logic [3:0]       cio_sd_in;

  axi_if #(
    .AW(AxiAw),
    .DW(AxiDw),
    .IW(AxiIw),
    .UW(AxiUw)
  ) s_axi_w_if (
    .clk(clk_i),
    .rst_n(rst_ni)
  );

  axi_if #(
    .AW(AxiAw),
    .DW(AxiDw),
    .IW(AxiIw),
    .UW(AxiUw)
  ) s_axi_r_if (
    .clk(clk_i),
    .rst_n(rst_ni)
  );


  // AW
  assign s_axi_w_if.awaddr  = s_axi_awaddr_i;
  assign s_axi_w_if.awburst = s_axi_awburst_i;
  assign s_axi_w_if.awsize  = s_axi_awsize_i;
  assign s_axi_w_if.awlen   = s_axi_awlen_i;
  assign s_axi_w_if.awuser  = s_axi_awuser_i;
  assign s_axi_w_if.awid    = s_axi_awid_i;
  assign s_axi_w_if.awlock  = s_axi_awlock_i;
  assign s_axi_w_if.awvalid = s_axi_awvalid_i;
  assign s_axi_awready_o      = s_axi_w_if.awready;

  // W
  assign s_axi_w_if.wdata  = s_axi_wdata_i;
  assign s_axi_w_if.wstrb  = s_axi_wstrb_i;
  assign s_axi_w_if.wuser  = s_axi_wuser_i;
  assign s_axi_w_if.wvalid = s_axi_wvalid_i;
  assign s_axi_wready_o      = s_axi_w_if.wready;
  assign s_axi_w_if.wlast  = s_axi_wlast_i;

  // B
  assign s_axi_bresp_o       = s_axi_w_if.bresp;
  assign s_axi_bid_o         = s_axi_w_if.bid;
  assign s_axi_buser_o       = s_axi_w_if.buser;
  assign s_axi_bvalid_o      = s_axi_w_if.bvalid;
  assign s_axi_w_if.bready = s_axi_bready_i;

  // AR
  assign s_axi_r_if.araddr  = s_axi_araddr_i;
  assign s_axi_r_if.arburst = s_axi_arburst_i;
  assign s_axi_r_if.arsize  = s_axi_arsize_i;
  assign s_axi_r_if.arlen   = s_axi_arlen_i;
  assign s_axi_r_if.aruser  = s_axi_aruser_i;
  assign s_axi_r_if.arid    = s_axi_arid_i;
  assign s_axi_r_if.arlock  = s_axi_arlock_i;
  assign s_axi_r_if.arvalid = s_axi_arvalid_i;
  assign s_axi_arready_o      = s_axi_r_if.arready;

  // R
  assign s_axi_rdata_o       = s_axi_r_if.rdata;
  assign s_axi_rresp_o       = s_axi_r_if.rresp;
  assign s_axi_rid_o         = s_axi_r_if.rid;
  assign s_axi_ruser_o       = s_axi_r_if.ruser;
  assign s_axi_rlast_o       = s_axi_r_if.rlast;
  assign s_axi_rvalid_o      = s_axi_r_if.rvalid;
  assign s_axi_r_if.rready = s_axi_rready_i;


  // Pad models
  assign cio_sck_o = cio_sck_en ? cio_sck : 1'bz;

  for (genvar i = 0; i < NumCS; i++) begin : gen_csb_fake_pad
    assign cio_csb_o[i] = cio_csb_en[i] ? cio_csb[i] : 1'bz;
  end

  for (genvar i = 0; i < 4; i++) begin : gen_sd_out_fake_pad
    assign cio_sd_io[i] = cio_sd_en[i] ? cio_sd_out[i] : 1'bz;
  end
  assign cio_sd_in = cio_sd_io;


  spi_host_axi #(
    .NumCS   (NumCS   ),
    .CmdDepth(CmdDepth),
    .AxiAw   (AxiAw   ),
    .AxiDw   (AxiDw   ),
    .AxiUw   (AxiUw   ),
    .AxiIw   (AxiIw   )
  ) u_spi_host_axi (
    .clk_i,
    .rst_ni,
    .s_axi_w_if   (s_axi_w_if.w_sub),
    .s_axi_r_if   (s_axi_r_if.r_sub),
    .intg_error_o,
    .cio_sck_o    (cio_sck),
    .cio_sck_en_o (cio_sck_en),
    .cio_csb_o    (cio_csb),
    .cio_csb_en_o (cio_csb_en),
    .cio_sd_o     (cio_sd_out),
    .cio_sd_en_o  (cio_sd_en),
    .cio_sd_i     (cio_sd_in),
    .passthrough_i('0),
    .passthrough_o(),
    .intr_error_o,
    .intr_spi_event_o
  );

endmodule
