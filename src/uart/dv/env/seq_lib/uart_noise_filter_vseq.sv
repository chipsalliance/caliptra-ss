// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test small glitch that can be filtered when noise filter is enabled
class uart_noise_filter_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_noise_filter_vseq)

  `uvm_object_new

  // add noise before sending rx byte
  // check rxidle should be high after adding noise
  virtual task send_rx_byte(byte data);
    int core_clk_period_ps = cfg.clk_rst_vif.clk_period_ps;

    // monitor doesn't filter glitch less than 1 core cycle, need to disable it
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    if (en_noise_filter) begin
      cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
      cfg.clk_rst_vif.wait_clks(100);
      if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b0);
      // uart clk is much slower than core clk
      // need large number to check if the glitch has no impact to uart
      repeat ($urandom_range(1, 10_000)) begin
        cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
            .max_glitch_ps(core_clk_period_ps / 2), // sub-cycle glitch (< 1 core clk)
            // need 4 core clk cycles to push out the glitch before next drive
            .stable_ps_after_glitch(core_clk_period_ps * 4));
      end
      if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b1);
      csr_rd_check(.ptr(ral.status.rxidle), .compare_value(1));
    end
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    super.send_rx_byte(data);
  endtask

endclass : uart_noise_filter_vseq
