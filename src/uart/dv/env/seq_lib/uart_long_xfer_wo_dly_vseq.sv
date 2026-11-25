// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// transfer large amount of data without delay between each transaction, in order to test clock
// offset is not over 1/4 of the period
class uart_long_xfer_wo_dly_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_long_xfer_wo_dly_vseq)

  `uvm_object_new

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      [101:1000] :/ 1
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      [101:1000] :/ 1
    };
  }

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo < 100;
  }

  constraint dly_to_next_rx_trans_c {
    dly_to_next_rx_trans == 0;
  }

  constraint dly_to_next_tx_trans_c {
    dly_to_next_tx_trans == 0;
  }

  constraint wait_for_rx_idle_c {
    wait_for_rx_idle == 0;
  }

  constraint wait_for_tx_idle_c {
    wait_for_tx_idle == 0;
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 1: skip
    weight_to_skip_rx_read == 1;
  }

  constraint dly_to_rx_read_c {
    dly_to_rx_read < 100;
  }

  // lower the freq as design freq isn't precise and agent has precise freq.
  // The delay in this test is small and running too fast will accumulate the diff, which may lead
  // to mis-aligned cycle
  constraint baud_rate_extra_c {
    baud_rate > BaudRate230400;
  }

  virtual task body();
    super.body();
    if (this.get_type_name() == "uart_long_xfer_wo_dly_vseq" && do_apply_reset &&
        !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      verify_baud_rate_tolerance();
    end
  endtask : body

  // Deterministically verify continuous back-to-back +/-3% (or +/-2% at 1 Mbps on <48 MHz clocks)
  // RX baud-rate tolerance across 8N1/8E1/8O1 and multiple baud rates, plus a negative +8.5%
  // out-of-tolerance drift check confirming RxFrameErr assertion and RX FIFO exclusion.
  virtual task verify_baud_rate_tolerance();
    bit [TL_DW-1:0] intr_val, fst_val;
    int             nco_width;
    realtime        nom_period;
    baud_rate_e     tol_bauds[3]  = '{BaudRate115200, BaudRate256Kbps, BaudRate1Mbps};
    byte            fast_bytes[4] = '{8'h55, 8'hAA, 8'hA5, 8'h5A};
    byte            slow_bytes[4] = '{8'h33, 8'hCC, 8'h0F, 8'hF0};

    // Clear any stale TX/RX FIFO bytes (e.g., queued when the last random run had en_tx == 0)
    // before enabling TX/RX in uart_init().
    clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(1));
    cfg.m_uart_agent_cfg.vif.wait_for_idle();

    en_tx                  = 1'b1;
    en_rx                  = 1'b1;
    baud_rate              = BaudRate115200;
    en_parity              = 1'b0;
    odd_parity             = 1'b0;
    en_noise_filter        = 1'b1;
    uart_period_glitch_pct = 0;
    uart_init();
    clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(1));
    csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));

    nco_width = ral.ctrl.nco.get_n_bits();
    foreach (tol_bauds[b_idx]) begin
      // When core clock is below 48x the baud rate (e.g., 1 Mbps on <48 MHz clocks), the RTL's
      // registered tick_baud_q + 16x oversampling + CDC rand-delay quantization uses ~12-17% of
      // a bit period, leaving +/-2.0% margin on 11-bit parity frames; >=48x sustains +/-3.0%.
      real drift_frac = (longint'(cfg.clk_freq_mhz) * 1_000_000 < longint'(tol_bauds[b_idx]) * 48)
                        ? 0.02 : 0.03;
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      // Skip baud rates that cannot be represented within the 16-bit NCO at the randomized core clock
      // (e.g., 1 Mbps at <=16 MHz yields NCO >= 2**16).
      if (`CALC_NCO(tol_bauds[b_idx], nco_width, cfg.clk_freq_mhz) >= (1 << nco_width)) continue;
      set_baud_rate(tol_bauds[b_idx]);
      for (int mode = 0; mode < 3; mode++) begin
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        set_parity(.en_parity(mode > 0), .odd_parity(mode == 2));
        nom_period = cfg.m_uart_agent_cfg.vif.uart_clk_period;

        // Fast transmitter (-drift_frac bit period) across 4 continuous back-to-back frames
        cfg.m_uart_agent_cfg.vif.uart_clk_period = nom_period * (1.0 - drift_frac);
        foreach (fast_bytes[k]) send_rx_byte(fast_bytes[k]);
        cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
        foreach (fast_bytes[k]) chk_rx_byte(fast_bytes[k]);
        csr_rd(.ptr(ral.intr_state), .value(intr_val));
        `DV_CHECK_EQ(intr_val[RxFrameErr], 1'b0,
                     "Fast (-drift) RX burst must not trigger RxFrameErr")
        `DV_CHECK_EQ(intr_val[RxParityErr], 1'b0,
                     "Fast (-drift) RX burst must not trigger RxParityErr")

        // Slow transmitter (+drift_frac bit period) across 4 continuous back-to-back frames
        cfg.m_uart_agent_cfg.vif.uart_clk_period = nom_period * (1.0 + drift_frac);
        foreach (slow_bytes[k]) send_rx_byte(slow_bytes[k]);
        cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
        foreach (slow_bytes[k]) chk_rx_byte(slow_bytes[k]);
        csr_rd(.ptr(ral.intr_state), .value(intr_val));
        `DV_CHECK_EQ(intr_val[RxFrameErr], 1'b0,
                     "Slow (+drift) RX burst must not trigger RxFrameErr")
        `DV_CHECK_EQ(intr_val[RxParityErr], 1'b0,
                     "Slow (+drift) RX burst must not trigger RxParityErr")

        cfg.m_uart_agent_cfg.vif.uart_clk_period = nom_period;
      end
    end

    // Negative out-of-tolerance drift check (+8.5% bit period on 0x00 shifts stop bit to
    // 9.765*T > 9.5*T so stop bit samples 0 -> RxFrameErr=1, while rising before 10.0*T
    // so no phantom frame starts)
    set_baud_rate(BaudRate115200);
    set_parity(1'b0, 1'b0);
    nom_period = cfg.m_uart_agent_cfg.vif.uart_clk_period;
    cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
    spinwait_rxidle();
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    cfg.disable_scb_rx_frame_check     = 1;
    @(posedge cfg.clk_rst_vif.clk);
    cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b0;
    #(9 * nom_period * 1.085);
    cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b1;
    #(2 * nom_period);
    spinwait_rxidle();
    csr_rd(.ptr(ral.intr_state), .value(intr_val));
    `DV_CHECK_EQ(intr_val[RxFrameErr], 1'b1,
                 "Excessive (+8.5% period) RX clock drift on 0x00 must trigger RxFrameErr")
    csr_rd(.ptr(ral.fifo_status), .value(fst_val));
    `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fst_val), 0,
                 "Frame-error byte from excessive RX drift must not enter RX FIFO")
    csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
    cfg.disable_scb_rx_frame_check     = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_checks  = 1;
    dut_shutdown();
  endtask : verify_baud_rate_tolerance

endclass : uart_long_xfer_wo_dly_vseq
