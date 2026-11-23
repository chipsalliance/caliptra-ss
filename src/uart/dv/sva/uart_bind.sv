// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  `include "caliptra_prim_assert.sv"

`ifndef CLP_ASSERT_ON
  $fatal(1, "CLP_ASSERT_ON must be defined in UART DV builds so concurrent CALIPTRA_ASSERT RTL assertions are active.");
`endif

  bind caliptra_ss_uart tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  // SEC_CM: REG.BUS.INTEGRITY & REG_WE.ONEHOT concurrent assertions
  `CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ERR(
      RegWeOnehotCheck_A,
      dut.u_caliptra_ss_uart.u_reg.u_prim_reg_we_check.u_caliptra_prim_onehot_check,
      intg_error, 0, 2, clk, !rst_n)

  `CALIPTRA_ASSERT(FpvSecCmTlulIntgCheck_A,
      $rose(dut.u_caliptra_ss_uart.u_reg.u_chk.err_o) |-> ##[0:2] intg_error,
      clk, !rst_n)

  `CALIPTRA_ASSERT(FpvSecCmTlulIntgBlocksSideEffect_A,
      dut.u_caliptra_ss_uart.u_reg.u_chk.err_o |->
      ((dut.u_caliptra_ss_uart.u_reg.reg_we_check == '0) &&
       !dut.u_caliptra_ss_uart.u_reg.status_re &&
       !dut.u_caliptra_ss_uart.u_reg.rdata_re &&
       !dut.u_caliptra_ss_uart.u_reg.fifo_status_re &&
       !dut.u_caliptra_ss_uart.u_reg.val_re),
      clk, !rst_n)

  // Outgoing D2H TL-UL response and data SECDED integrity check on caliptra_ss_uart.tl_o
  logic tlul_rsp_intg_err;
  tlul_rsp_intg_chk #(
    .EnableRspDataIntgCheck(1'b1)
  ) u_tlul_rsp_intg_chk (
    .tl_i  (dut.u_caliptra_ss_uart.tl_o),
    .err_o (tlul_rsp_intg_err)
  );

  `CALIPTRA_ASSERT(FpvSecCmTlulRspIntgCheck_A,
      dut.u_caliptra_ss_uart.tl_o.d_valid |-> !tlul_rsp_intg_err,
      clk, !rst_n)

  `CALIPTRA_ASSERT(UartIntgErrSticky_A, intg_error |=> intg_error, clk, !rst_n)
  `CALIPTRA_ASSERT_KNOWN(UartIntgErrKnown_A, intg_error, clk, !rst_n)

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
