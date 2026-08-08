// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Host module with AXI interface.

`include "caliptra_prim_assert.sv"

module spi_host_axi #(
  parameter int unsigned NumCS    = 2,
  parameter int unsigned CmdDepth = 8,
  parameter int unsigned AxiAw    = 32,
  parameter int unsigned AxiDw    = 32,
  parameter int unsigned AxiUw    = 32,
  parameter int unsigned AxiIw    = 1
) (

  input logic clk_i,
  input logic rst_ni,

  // AXI interface
  axi_if.w_sub s_axi_w_if,
  axi_if.r_sub s_axi_r_if,

  // Register integrity error
  output logic intg_error_o,

  // SPI interface
  output logic             cio_sck_o,
  output logic             cio_sck_en_o,
  output logic [NumCS-1:0] cio_csb_o,
  output logic [NumCS-1:0] cio_csb_en_o,
  output logic [3:0]       cio_sd_o,
  output logic [3:0]       cio_sd_en_o,
  input  logic [3:0]       cio_sd_i,

  // Passthrough interface
  input  caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_req_t passthrough_i,
  output caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_rsp_t passthrough_o,

  output logic intr_error_o,
  output logic intr_spi_event_o

);

  tlul_pkg::tl_h2d_t tl_h2d;
  tlul_pkg::tl_d2h_t tl_d2h;

  axi2tlul #(
    .AW(AxiAw),
    .DW(AxiDw),
    .UW(AxiUw),
    .IW(AxiIw),
    .EX_EN(1'b0),
    .C_LAT(32'd0)
  ) u_axi2tlul_spi_host (
    .clk       (clk_i),
    .rst_n     (rst_ni),
    .s_axi_w_if(s_axi_w_if),
    .s_axi_r_if(s_axi_r_if),
    .tl_o      (tl_h2d),
    .tl_i      (tl_d2h)
  );

  caliptra_ss_spi_host #(
    .NumCS(NumCS),
    .CmdDepth(CmdDepth)
  ) u_caliptra_ss_spi_host (
    .clk_i,
    .rst_ni,
    .tl_i             (tl_h2d),
    .tl_o             (tl_d2h),
    .intg_error_o,
    .cio_sck_o,
    .cio_sck_en_o,
    .cio_csb_o,
    .cio_csb_en_o,
    .cio_sd_o,
    .cio_sd_en_o,
    .cio_sd_i,
    .passthrough_i,
    .passthrough_o,
    .intr_error_o,
    .intr_spi_event_o
  );


  `CALIPTRA_ASSERT_INIT(NumCSValid_A, NumCS inside {1, 2})
  `CALIPTRA_ASSERT_INIT(CmdDepthValid_A, CmdDepth inside {4, 8})

endmodule
