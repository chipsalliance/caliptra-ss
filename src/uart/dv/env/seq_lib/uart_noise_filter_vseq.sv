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

  virtual task body();
    super.body();
    if (this.get_type_name() == "uart_noise_filter_vseq" && do_apply_reset &&
        !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      verify_noise_filter_boundary_sweep();
    end
  endtask

  // Systematically sweep a 1-core-clock glitch across all 16 oversample positions (0..15) of a bit
  // period (including around the mid-bit sampling point pos=7,8) with CTRL.NF=1, and verify that
  // disabling CTRL.NF=0 allows the same 1-core-clock pulse to trigger false start-bit detection.
  virtual task verify_noise_filter_boundary_sweep();
    realtime slot_ps;

    clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(1));
    cfg.m_uart_agent_cfg.vif.wait_for_idle();

    en_tx                  = 1'b1;
    en_rx                  = 1'b1;
    en_parity              = 1'b0;
    odd_parity             = 1'b0;
    en_noise_filter        = 1'b1;
    uart_period_glitch_pct = 0;
    baud_rate              = BaudRate115200;
    do_interrupt           = 1'b1;
    en_intr                = '0;
    uart_init();
    clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(1));
    if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b0);

    slot_ps = cfg.m_uart_agent_cfg.vif.uart_clk_period / 16.0;
    csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));

    // 1. Sweep 1-core-clock glitch across all 16 oversample positions (pos = 0..15) with CTRL.NF=1
    //    across alternating 0/1-bit data patterns, plus start-bit and stop-bit mid-sample glitches.
    for (int pos = 0; pos < 16; pos++) begin
      byte exp_b = (pos[0] ? 8'h55 : 8'hAA) ^ byte'(pos);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) break;
      fork
        super.send_rx_byte(exp_b);
        begin
          wait(cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == 9 || cfg.under_reset);
          if (!cfg.under_reset) begin
            realtime offset_ps = (pos * slot_ps) + ((pos == 8) ? 20ns : 5ns);
            #(offset_ps);
            if (!cfg.under_reset) begin
              bit orig_rx = cfg.m_uart_agent_cfg.vif.uart_rx;
              @(posedge cfg.clk_rst_vif.clk);
              cfg.m_uart_agent_cfg.vif.uart_rx <= ~orig_rx;
              @(posedge cfg.clk_rst_vif.clk);
              cfg.m_uart_agent_cfg.vif.uart_rx <= orig_rx;
            end
          end
        end
      join
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        chk_rx_byte(exp_b);
      end
    end

    // Inject 1-core-clock glitches on start bit (pulse==10) and stop bit (pulse==1) at mid-bit slot 7
    begin
      int target_pulses[2] = '{10, 1};
      foreach (target_pulses[k]) begin
        byte exp_b = 8'hC3 ^ byte'(k);
        bit [TL_DW-1:0] intr_val;
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) break;
        fork
          super.send_rx_byte(exp_b);
          begin
            wait(cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == target_pulses[k] || cfg.under_reset);
            if (!cfg.under_reset) begin
              #(7 * slot_ps + 5ns);
              if (!cfg.under_reset) begin
                bit orig_rx = cfg.m_uart_agent_cfg.vif.uart_rx;
                @(posedge cfg.clk_rst_vif.clk);
                cfg.m_uart_agent_cfg.vif.uart_rx <= ~orig_rx;
                @(posedge cfg.clk_rst_vif.clk);
                cfg.m_uart_agent_cfg.vif.uart_rx <= orig_rx;
              end
            end
          end
        join
        if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
          chk_rx_byte(exp_b);
          csr_rd(.ptr(ral.intr_state), .value(intr_val));
          `DV_CHECK_EQ(intr_val[RxFrameErr], 1'b0,
                       "1-core-clock start/stop-bit glitch with CTRL.NF=1 must not cause RxFrameErr")
        end
      end
    end

    // 2. Pulse-width boundary sweep while idle:
    //    - CTRL.NF=1 + 1-core-clock low pulse -> filtered (STATUS.RXIDLE remains 1)
    //    - CTRL.NF=1 + 2-core-clock low pulse -> accepted by 3-tap majority filter (STATUS.RXIDLE drops to 0)
    //    - CTRL.NF=0 + 1-core-clock low pulse -> accepted without filter (STATUS.RXIDLE drops to 0)
    if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
      spinwait_rxidle();
      cfg.m_uart_agent_cfg.en_rx_monitor = 0;

      // 2a. With CTRL.NF=1, a 1-core-clock low pulse is filtered out (STATUS.RXIDLE remains 1)
      @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b0;
      @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b1;
      cfg.clk_rst_vif.wait_clks(4);
      if (!cfg.under_reset) csr_rd_check(.ptr(ral.status.rxidle), .compare_value(1));

      // 2b. With CTRL.NF=1, a 2-core-clock low pulse passes the 3-tap majority filter (STATUS.RXIDLE drops to 0)
      @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b0;
      repeat (2) @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b1;
      cfg.clk_rst_vif.wait_clks(4);
      if (!cfg.under_reset) csr_rd_check(.ptr(ral.status.rxidle), .compare_value(0));
      #(cfg.m_uart_agent_cfg.vif.uart_clk_period);
      spinwait_rxidle();

      // 2c. With CTRL.NF=0, a 1-core-clock low pulse triggers start-bit detection (STATUS.RXIDLE drops to 0)
      ral.ctrl.nf.set(0);
      csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
      void'(ral.ctrl.predict(ral.ctrl.get()));
      @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b0;
      @(posedge cfg.clk_rst_vif.clk);
      cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b1;
      cfg.clk_rst_vif.wait_clks(4);
      if (!cfg.under_reset) csr_rd_check(.ptr(ral.status.rxidle), .compare_value(0));

      // Wait for start-bit mid-sample glitch abort and restore CTRL.NF=1
      #(cfg.m_uart_agent_cfg.vif.uart_clk_period);
      spinwait_rxidle();
      ral.ctrl.nf.set(1);
      csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
      void'(ral.ctrl.predict(ral.ctrl.get()));
      cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    end

    if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b1);
  endtask : verify_noise_filter_boundary_sweep

endclass : uart_noise_filter_vseq
