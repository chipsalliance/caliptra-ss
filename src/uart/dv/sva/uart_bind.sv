// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_assert.sv"

module uart_data_stable_assert (
  input logic clk_i,
  input logic rst_ni,
  input logic tx_enable,
  input logic tick_baud_q,
  input logic tx
);

`ifdef UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"
`endif

  // UART TX serial line data stability between baud bit ticks when TX is enabled
  UartTxDataStable_A: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (tx_enable && $past(tx_enable) && !$past(tick_baud_q)) |-> $stable(tx))
  else `uvm_error($sformatf("%m"), "UART TX line changed between baud bit ticks")

endmodule

module uart_bind;

  bind caliptra_ss_uart tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind caliptra_ss_uart uart_data_stable_assert u_uart_data_stable_assert (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .tx_enable   (caliptra_ss_uart_core.tx_enable),
    .tick_baud_q (caliptra_ss_uart_core.caliptra_ss_uart_tx.tick_baud_q),
    .tx          (caliptra_ss_uart_core.caliptra_ss_uart_tx.tx)
  );

endmodule
