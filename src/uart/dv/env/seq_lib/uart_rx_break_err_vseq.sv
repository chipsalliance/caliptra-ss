// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: uart_rx_break_err (uart_rx_break_err_vseq)
// Tests UART RX Break Error detection across all break levels (rxblvl):
// 1. Configures ctrl.rxblvl for 2, 4, 8, 16 break character detection.
// 2. Injects a break condition by driving RX low for >= (break_chars + 2) character times.
// 3. Verifies event_rx_break_err triggers and sets intr_state.rx_break_err.
// 4. Returns RX line high (rx_in = 1) to transition break_st_q from BRK_WAIT back to BRK_CHK (covering line 136 in uart_core.sv).
// 5. Clears the interrupt via W1C and verifies it is cleared.

class uart_rx_break_err_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_rx_break_err_vseq)

  `uvm_object_new

  int total_break_err_count;

  virtual task pre_start();
    super.pre_start();
    total_break_err_count = 0;
  endtask

  virtual task body();
    `uvm_info(`gfn, "Starting uart_rx_break_err_vseq", UVM_LOW)

    // Initialize UART DUT & Agent
    en_rx           = 1'b1;
    en_tx           = 1'b0;
    en_parity       = 1'b0;
    odd_parity      = 1'b0;
    en_noise_filter = 1'b0;
    uart_init();

    // Disable monitor & scoreboard checks for break/framing error injection
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;

    // Enable RX and all interrupts
    csr_wr(.ptr(ral.intr_enable), .value(32'h1FF));

    // Test across all break levels: 0 (2 chars), 1 (4 chars), 2 (8 chars), 3 (16 chars)
    for (int lvl = 0; lvl < 4; lvl++) begin
      int break_chars;
      bit [TL_DW-1:0] intr_val;
      case (lvl)
        0: break_chars = 2;
        1: break_chars = 4;
        2: break_chars = 8;
        3: break_chars = 16;
      endcase

      `uvm_info(`gfn, $sformatf("--- Testing RX Break Error: rxblvl=%0d (break_chars=%0d) ---", lvl, break_chars), UVM_LOW)

      // Set rxblvl in ctrl
      ral.ctrl.rxblvl.set(lvl);
      ral.ctrl.rx.set(1'b1);
      csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));

      // Ensure RX line is idle (high) to reset allzero_cnt
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(100);

      // Clear any pending interrupts and FIFOs
      csr_wr(.ptr(ral.intr_state), .value(32'h1FF));
      clear_fifos(.clear_tx_fifo(0), .clear_rx_fifo(1));

      // Drive RX line low for (break_chars + 2) character times to guarantee break condition
      // Each character is 10 bit times (1 start + 8 data + 1 stop)
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      #(cfg.m_uart_agent_cfg.vif.uart_clk_period * 10 * (break_chars + 2));

      // Verify interrupt occurred
      csr_rd(.ptr(ral.intr_state), .value(intr_val));
      if (intr_val[RxBreakErr]) begin
        total_break_err_count++;
        `uvm_info(`gfn, $sformatf("Verified RxBreakErr triggered for rxblvl=%0d!", lvl), UVM_LOW)
      end else begin
        `uvm_error(`gfn, $sformatf("Expected RxBreakErr for rxblvl=%0d, but intr_state=0x%0h", lvl, intr_val))
      end

      // Drive RX line back to high (idle). This causes rx_in=1, transitioning break_st_q from BRK_WAIT back to BRK_CHK!
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      #(cfg.m_uart_agent_cfg.vif.uart_clk_period * 20);

      // Clear interrupt via W1C
      csr_wr(.ptr(ral.intr_state), .value(1 << RxBreakErr));
      csr_rd(.ptr(ral.intr_state), .value(intr_val));
      `DV_CHECK_EQ(intr_val[RxBreakErr], 1'b0, "RxBreakErr should be cleared after W1C")

      // Clear FIFOs
      clear_fifos(.clear_tx_fifo(0), .clear_rx_fifo(1));
    end

    // Re-enable monitors
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;

    `uvm_info(`gfn, $sformatf("Completed uart_rx_break_err_vseq successfully with %0d break errors verified!",
               total_break_err_count), UVM_LOW)
    dut_shutdown();
  endtask

  virtual task post_start();
    `DV_CHECK_GE(total_break_err_count, 4, "Verify all 4 break levels triggered break error")
    super.post_start();
  endtask

endclass : uart_rx_break_err_vseq
