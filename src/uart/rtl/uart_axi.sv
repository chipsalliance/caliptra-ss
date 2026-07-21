// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// UART module with AXI interface.

module uart_axi #(
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
  output logic intg_err_o,

  // Generic IO
  input  logic cio_rx_i,
  output logic cio_tx_o,
  output logic cio_tx_en_o,

  // Interrupts
  output logic intr_tx_watermark_o,
  output logic intr_tx_empty_o,
  output logic intr_rx_watermark_o,
  output logic intr_tx_done_o,
  output logic intr_rx_overflow_o,
  output logic intr_rx_frame_err_o,
  output logic intr_rx_break_err_o,
  output logic intr_rx_timeout_o,
  output logic intr_rx_parity_err_o

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
  ) u_axi2tlul_uart (
    .clk       (clk_i),
    .rst_n     (rst_ni),
    .s_axi_w_if(s_axi_w_if),
    .s_axi_r_if(s_axi_r_if),
    .tl_o      (tl_h2d),
    .tl_i      (tl_d2h)
  );

  caliptra_ss_uart u_caliptra_ss_uart (
    .clk_i,
    .rst_ni,
    .tl_i (tl_h2d),
    .tl_o (tl_d2h),
    .intg_err_o,
    .cio_rx_i,
    .cio_tx_o,
    .cio_tx_en_o,
    .intr_tx_watermark_o,
    .intr_tx_empty_o,
    .intr_rx_watermark_o,
    .intr_tx_done_o,
    .intr_rx_overflow_o,
    .intr_rx_frame_err_o,
    .intr_rx_break_err_o,
    .intr_rx_timeout_o,
    .intr_rx_parity_err_o
  );

endmodule
