// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test small glitch that can be filtered when noise filter is enabled
class uart_noise_filter_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_noise_filter_vseq)

  int total_noise_glitches_injected;

  `uvm_object_new

  constraint en_noise_filter_c {
    en_noise_filter == 1;
  }

  string cdc_sel_path = {"tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx",
                         ".u_caliptra_prim_cdc_rand_delay.gen_enable.data_sel"};

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Disable CDC randomization for rx_sync by forcing internal select signal
    if (cfg.en_dv_cdc && uvm_hdl_check_path(cdc_sel_path)) begin
      `DV_CHECK(uvm_hdl_force(cdc_sel_path, 0));
    end
  endtask

  virtual task dut_shutdown();
    super.dut_shutdown();
    // Enable CDC randomization for rx_sync by releasing internal select signal
    if (cfg.en_dv_cdc && uvm_hdl_check_path(cdc_sel_path)) begin
      `DV_CHECK(uvm_hdl_release(cdc_sel_path));
    end
  endtask

  virtual task pre_start();
    super.pre_start();
    total_noise_glitches_injected = 0;
  endtask

  // add noise before sending rx byte
  // check rxidle should be high after adding noise
  virtual task send_rx_byte(byte data);
    int core_clk_period_ps = cfg.clk_rst_vif.clk_period_ps;
    int num_glitches;

    // monitor doesn't filter glitch less than 1 core cycle, need to disable it
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    if (en_noise_filter) begin
      bit [TL_DW-1:0] status_val;
      // Wait for any previous in-flight rx byte to finish so line is idle before checking
      cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
      cfg.clk_rst_vif.wait_clks(100);

      num_glitches = $urandom_range(100, 500);
      repeat (num_glitches) begin
        cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
            .max_glitch_ps(core_clk_period_ps), // 1 core clk
            // need 3 core clk cycles to push out the glitch before next drive
            .stable_ps_after_glitch(core_clk_period_ps * 3));
      end
      total_noise_glitches_injected += num_glitches;
      csr_rd(.ptr(ral.status), .value(status_val));
      if (!cfg.under_reset) `DV_CHECK_EQ(get_field_val(ral.status.rxidle, status_val), 1'b1, "status.rxidle must be 1");
    end
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    super.send_rx_byte(data);
  endtask

  virtual task post_start();
    if (!cfg.under_reset && this.get_type_name() == "uart_noise_filter_vseq") begin
      `DV_CHECK_GT(total_noise_glitches_injected, 0, "Verify noise glitches were injected and filtered")
      `uvm_info(`gfn, $sformatf("Verified %0d noise glitches were successfully filtered!", total_noise_glitches_injected), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_noise_filter_vseq
