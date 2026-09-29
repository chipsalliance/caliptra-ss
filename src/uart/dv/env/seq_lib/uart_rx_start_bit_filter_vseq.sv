// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test start bit length < 0.5 will be ignored
class uart_rx_start_bit_filter_vseq extends uart_smoke_vseq;
  `uvm_object_utils(uart_rx_start_bit_filter_vseq)

  int total_start_bit_glitches_injected;

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    total_start_bit_glitches_injected = 0;
  endtask

  // add noise before sending rx byte
  // when start bit is detected, design will check it again after 0.5 uart clock
  // if it's not low, consider it as glitch and ignore it
  virtual task send_rx_byte(byte data);
    uint uart_clk_period_ps = cfg.m_uart_agent_cfg.vif.uart_clk_period / 1ps;
    bit [TL_DW-1:0] rxlvl_before, rxlvl_after;
    int num_glitches = $urandom_range(10, 100);

    // monitor doesn't have start bit filter, need to disable it while driving filtered start bit
    bit [TL_DW-1:0] fifo_status_val, status_val;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
    rxlvl_before = get_field_val(ral.fifo_status.rxlvl, fifo_status_val);
    repeat (num_glitches) begin
      // drive 0 for up to 0.4 uart clk and 1 for 0.8 clk. Design samples start bit (0) first,
      // after 0.5 clk, design will sample 1 and should drop this start bit
      // need stable period > 0.5, use 0.8 clk to have enough margin
      cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
          .max_glitch_ps(uart_clk_period_ps * 0.4),
          .stable_ps_after_glitch(uart_clk_period_ps * 0.8));
    end
    total_start_bit_glitches_injected += num_glitches;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    csr_rd(.ptr(ral.status), .value(status_val));
    if (!cfg.under_reset) `DV_CHECK_EQ(get_field_val(ral.status.rxidle, status_val), 1'b1, "status.rxidle must be 1");
    csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
    rxlvl_after = get_field_val(ral.fifo_status.rxlvl, fifo_status_val);
    if (!cfg.under_reset) `DV_CHECK_EQ(rxlvl_after, rxlvl_before, "Start bit glitch should not trigger RX FIFO push")

    super.send_rx_byte(data);
  endtask

  virtual task post_start();
    if (!cfg.under_reset && this.get_type_name() == "uart_rx_start_bit_filter_vseq") begin
      `DV_CHECK_GT(total_start_bit_glitches_injected, 0, "Verify start bit glitches were injected and filtered")
      `uvm_info(`gfn, $sformatf("Verified %0d start bit glitches were successfully filtered!", total_start_bit_glitches_injected), UVM_LOW)
    end
    super.post_start();
  endtask

  // disable txidle check as it will also read rxidle which value is unexpected
  // during the long start bit glitch, rxidle will be low. mon/scb isn't supported
  // for checking this glitch for rxidle. Check it in test instead.
  virtual task spinwait_txidle();
  endtask

endclass : uart_rx_start_bit_filter_vseq
