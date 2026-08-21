// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART top level wrapper file

`include "caliptra_prim_assert.sv"

module caliptra_ss_uart
    import caliptra_ss_uart_reg_pkg::*;
(
  input           clk_i,
  input           rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Register integrity error
  output logic intg_err_o,

  // Generic IO
  input           cio_rx_i,
  output logic    cio_tx_o,
  output logic    cio_tx_en_o,

  // Interrupts
  output logic    intr_tx_watermark_o ,
  output logic    intr_tx_empty_o ,
  output logic    intr_rx_watermark_o ,
  output logic    intr_tx_done_o  ,
  output logic    intr_rx_overflow_o  ,
  output logic    intr_rx_frame_err_o ,
  output logic    intr_rx_break_err_o ,
  output logic    intr_rx_timeout_o   ,
  output logic    intr_rx_parity_err_o
);

  caliptra_ss_uart_reg2hw_t reg2hw;
  caliptra_ss_uart_hw2reg_t hw2reg;

  caliptra_ss_uart_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o
  );

  caliptra_ss_uart_core caliptra_ss_uart_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .rx    (cio_rx_i   ),
    .tx    (cio_tx_o   ),

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

  // always enable the driving out of TX
  assign cio_tx_en_o = 1'b1;

  // Assert Known for outputs
  `CALIPTRA_ASSERT(TxEnIsOne_A, cio_tx_en_o === 1'b1)
  `CALIPTRA_ASSERT_KNOWN(TxKnown_A, cio_tx_o, clk_i, !rst_ni || !cio_tx_en_o)

  // Assert Known for interrupts
  `CALIPTRA_ASSERT_KNOWN(TxWatermarkKnown_A, intr_tx_watermark_o)
  `CALIPTRA_ASSERT_KNOWN(TxEmptyKnown_A, intr_tx_empty_o)
  `CALIPTRA_ASSERT_KNOWN(RxWatermarkKnown_A, intr_rx_watermark_o)
  `CALIPTRA_ASSERT_KNOWN(TxDoneKnown_A, intr_tx_done_o)
  `CALIPTRA_ASSERT_KNOWN(RxOverflowKnown_A, intr_rx_overflow_o)
  `CALIPTRA_ASSERT_KNOWN(RxFrameErrKnown_A, intr_rx_frame_err_o)
  `CALIPTRA_ASSERT_KNOWN(RxBreakErrKnown_A, intr_rx_break_err_o)
  `CALIPTRA_ASSERT_KNOWN(RxTimeoutKnown_A, intr_rx_timeout_o)
  `CALIPTRA_ASSERT_KNOWN(RxParityErrKnown_A, intr_rx_parity_err_o)

endmodule
