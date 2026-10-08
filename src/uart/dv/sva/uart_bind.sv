// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  bind caliptra_ss_uart tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  // UART TX serial line data stability between baud bit ticks when TX is enabled
  UartTxDataStable_A: assert property (@(posedge clk) disable iff (!rst_n)
    (dut.u_caliptra_ss_uart.caliptra_ss_uart_core.tx_enable &&
     $past(dut.u_caliptra_ss_uart.caliptra_ss_uart_core.tx_enable) &&
     !$past(dut.u_caliptra_ss_uart.caliptra_ss_uart_core.caliptra_ss_uart_tx.tick_baud_q))
    |-> $stable(dut.u_caliptra_ss_uart.caliptra_ss_uart_core.caliptra_ss_uart_tx.tx))
  else `uvm_error($sformatf("%m"), "UART TX line changed between baud bit ticks")

  // When TX is idle, TX FIFO must also report empty
  UartTxIdleImpliesEmpty_A: assert property (@(posedge clk) disable iff (!rst_n)
    dut.u_caliptra_ss_uart.caliptra_ss_uart_core.hw2reg.status.txidle.d
    |-> dut.u_caliptra_ss_uart.caliptra_ss_uart_core.hw2reg.status.txempty.d)
  else `uvm_error($sformatf("%m"), "UART status.txidle asserted while status.txempty is 0")

  // TX and RX FIFO occupancy levels must never exceed architectural FIFO depths (TxFifoDepth=32, RxFifoDepth=64)
  UartFifoLevelBound_A: assert property (@(posedge clk) disable iff (!rst_n)
    (dut.u_caliptra_ss_uart.caliptra_ss_uart_core.hw2reg.fifo_status.txlvl.d <=
     caliptra_ss_uart_reg_pkg::TxFifoDepth) &&
    (dut.u_caliptra_ss_uart.caliptra_ss_uart_core.hw2reg.fifo_status.rxlvl.d <=
     caliptra_ss_uart_reg_pkg::RxFifoDepth))
  else `uvm_error($sformatf("%m"), "UART FIFO level exceeded maximum architectural depth")
