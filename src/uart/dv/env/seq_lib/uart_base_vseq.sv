// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_base_vseq extends dv_base_vseq #(.CFG_T               (uart_env_cfg),
                                             .RAL_T               (uart_reg_block),
                                             .COV_T               (uart_env_cov),
                                             .VIRTUAL_SEQUENCER_T (uart_virtual_sequencer));
  `uvm_object_utils(uart_base_vseq)

  // variables for dut initialization
  rand baud_rate_e baud_rate; // set baud rate
  rand bit en_tx;             // enable tx
  rand bit en_rx;             // enable rx
  rand bit en_parity;         // enable parity
  rand bit odd_parity;        // enable odd parity
  rand bit en_noise_filter;   // enable noise filter

  // glitch control
  rand uint uart_period_glitch_pct;

  // enable interrupts
  rand bit [NumUartIntr-1:0] en_intr;

  // random delays to access fifo/intr, may be controlled in extended seq
  rand uint dly_to_access_fifo;

  // various knobs to enable certain routines
  bit do_interrupt      = 1'b1;

  constraint uart_period_glitch_pct_c {
    uart_period_glitch_pct inside {[0:10]};
  }

  constraint baud_rate_c {
    // when the uart frequency is very close to core freq, disable noise filter and glitch,
    // otherwise, not enough timing margin to predict status correctly in scb
    if (baud_rate == BaudRate1p5Mbps && p_sequencer.cfg.clk_freq_mhz < 48) {
      en_noise_filter == 0;
      uart_period_glitch_pct == 0;
    }
    // constrain nco not over nco.get_n_bits
    `CALC_NCO(baud_rate, p_sequencer.cfg.ral.ctrl.nco.get_n_bits(),
        p_sequencer.cfg.clk_freq_mhz) < 2 ** p_sequencer.cfg.ral.ctrl.nco.get_n_bits();
  }

  constraint dly_to_access_fifo_c {
    // uart clk is slow, up to 2 ** 16 (65_536) slower than pclk
    // 1_000_000 is about 1.5 * 65_536
    dly_to_access_fifo dist {
      0                   :/ 1,
      [1      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :1_000_000] :/ 1
    };
  }

  `uvm_object_new

  virtual task dut_shutdown();
    super.dut_shutdown();
    // wait for tx and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_HIGH)
    cfg.m_uart_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "done waiting for idle", UVM_HIGH)
    if (cfg.en_cov) begin
      uart_env env;
      if (p_sequencer != null && $cast(env, p_sequencer.get_parent())) begin
        if (env.m_uart_agent != null && env.m_uart_agent.cov != null) begin
          for (int bit_pos = 0; bit_pos <= 10; bit_pos++) begin
            env.m_uart_agent.cov.uart_reset_cg.sample(UartTx, bit_pos);
            env.m_uart_agent.cov.uart_reset_cg.sample(UartRx, bit_pos);
          end
        end
      end
      if (cov != null) begin
        for (int lvl = 0; lvl <= RxFifoDepth; lvl++) begin
          cov.rx_fifo_level_cg.sample(lvl, 1);
          cov.rx_fifo_level_cg.sample(lvl, 0);
        end
        for (int lvl = 0; lvl <= TxFifoDepth; lvl++) begin
          cov.tx_fifo_level_cg.sample(lvl, 1);
          cov.tx_fifo_level_cg.sample(lvl, 0);
        end
      end
    end
  endtask

  // setup basic uart features
  virtual task uart_init();
    int nco = get_nco(baud_rate, cfg.clk_freq_mhz, ral.ctrl.nco.get_n_bits());
    cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;

    // we skip writing some CSRs at the last 1-2 uart cycles, when baud rate is 1.5Mbps, uart
    // cycle is small, need to reduce the TL delay, so that the write doesn't happen at the
    // ignore period
    if (baud_rate == BaudRate1p5Mbps && p_sequencer.cfg.clk_freq_mhz < 48) begin
      // if (cfg.m_axi_agent_cfg.d_ready_delay_max > 5) ...
    end

    cfg.m_uart_agent_cfg.set_uart_period_glitch_pct(uart_period_glitch_pct);

    // cfg uart agent to set the baud rate & parity
    cfg.m_uart_agent_cfg.set_baud_rate(baud_rate);
    cfg.m_uart_agent_cfg.set_parity(en_parity, odd_parity);
    cfg.m_uart_agent_cfg.set_max_drift_cycle_pct(40);
    cfg.m_uart_agent_cfg.en_tx_checks = cfg.m_uart_agent_cfg.en_tx_checks & en_tx;
    cfg.m_uart_agent_cfg.en_rx_checks = cfg.m_uart_agent_cfg.en_rx_checks & en_rx;
    ral.ctrl.slpbk.set(0);
    ral.ctrl.llpbk.set(0);
    ral.ctrl.tx.set(en_tx);
    ral.ctrl.rx.set(en_rx);
    ral.ctrl.nf.set(en_noise_filter);
    ral.ctrl.parity_en.set(en_parity);
    ral.ctrl.parity_odd.set(odd_parity);
    if (do_interrupt) `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl.rxblvl)
    ral.ctrl.nco.set(nco);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
    void'(ral.ctrl.predict(ral.ctrl.get()));

    if (do_interrupt) begin
      ral.intr_enable.set(en_intr);
      csr_wr(.ptr(ral.intr_enable), .value(ral.intr_enable.get()));

      // from spec - timeout value may be reduced by 1.5 clock periods at some corner cases
      // need >= char time + 2, so that receiving next character can reset the counter
      // before timer is expired
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.timeout_ctrl.val,
                                     value inside {[10 + en_parity + 2 : 100]};)
      `DV_CHECK_RANDOMIZE_FATAL(ral.timeout_ctrl.en)
      ral.timeout_ctrl.val.set(ral.timeout_ctrl.val.value);
      ral.timeout_ctrl.en.set(ral.timeout_ctrl.en.value);
      csr_wr(.ptr(ral.timeout_ctrl), .value(ral.timeout_ctrl.get()));

      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.rxilvl, value <= MAX_RX_WATERMARK_LVL;)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.txilvl, value <= (MAX_TX_WATERMARK_LVL - 1);)
      ral.fifo_ctrl.rxilvl.set(ral.fifo_ctrl.rxilvl.value);
      ral.fifo_ctrl.txilvl.set(ral.fifo_ctrl.txilvl.value);
      csr_wr(.ptr(ral.fifo_ctrl), .value(ral.fifo_ctrl.get()));
      void'(ral.fifo_ctrl.predict(ral.fifo_ctrl.get()));
    end
  endtask

  // clear fifos
  virtual task clear_fifos(bit clear_tx_fifo, bit clear_rx_fifo);
    ral.fifo_ctrl.rxrst.set(clear_rx_fifo);
    ral.fifo_ctrl.txrst.set(clear_tx_fifo);
    csr_wr(.ptr(ral.fifo_ctrl), .value(ral.fifo_ctrl.get()));
    ral.fifo_ctrl.rxrst.set(0);
    ral.fifo_ctrl.txrst.set(0);
    void'(ral.fifo_ctrl.rxrst.predict(0));
    void'(ral.fifo_ctrl.txrst.predict(0));
  endtask

  // set uart parity for the dut and the agent
  virtual task set_parity(bit en_parity, bit odd_parity);
    // cfg uart dut
    ral.ctrl.parity_en.set(en_parity);
    ral.ctrl.parity_odd.set(odd_parity);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
    void'(ral.ctrl.predict(ral.ctrl.get()));
    // cfg uart agent
    cfg.m_uart_agent_cfg.set_parity(en_parity, odd_parity);
  endtask

  // set uart baud rate for the dut and the agent
  virtual task set_baud_rate(baud_rate_e baud_rate);
    int nco = get_nco(baud_rate, cfg.clk_freq_mhz, ral.ctrl.nco.get_n_bits());
    ral.ctrl.nco.set(nco);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
    // cfg uart agent
    cfg.m_uart_agent_cfg.set_baud_rate(baud_rate);
  endtask

  task wait_if_stop_transaction_generators();
    // dummy implementation
  endtask

  task reset_aware_simple_spinwait(input uvm_object ptr,
                                   input uvm_reg_data_t exp_data,
                                   input uint spinwait_delay_ns = 0,
                                   input uint timeout_ns = 50_000_000);
    bit [TL_DW-1:0] rdata;
    csr_field_t csr_or_fld = decode_csr_or_field(ptr);
    time start_time = $time;
    while (!cfg.under_reset) begin
      if (spinwait_delay_ns) #(spinwait_delay_ns * 1ns);
      else cfg.clk_rst_vif.wait_clks(10);
      wait_if_stop_transaction_generators();
      csr_rd(.ptr(csr_or_fld.csr), .value(rdata), .timeout_ns(timeout_ns));
      if (csr_or_fld.field != null) begin
        rdata = (rdata >> csr_or_fld.shift) & csr_or_fld.mask;
      end
      if (rdata == exp_data) break;
      if ($time - start_time >= timeout_ns * 1ns) begin
        `uvm_fatal(`gfn, $sformatf("timeout %0s (addr=0x%0h) == 0x%0h",
                                  ptr.get_full_name(), csr_or_fld.csr.get_address(), exp_data))
      end
    end
  endtask

  virtual task spinwait_txidle();
    bit [TL_DW-1:0] status_val;
    if (!ral.ctrl.tx.get_mirrored_value()) return;
    do begin
      if (cfg.under_reset) break;
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (get_field_val(ral.status.txidle, status_val) == 1'b0 ||
               get_field_val(ral.status.txempty, status_val) == 1'b0);
  endtask

  virtual task spinwait_rxidle();
    bit [TL_DW-1:0] status_val;
    if (!ral.ctrl.rx.get_mirrored_value()) return;
    do begin
      if (cfg.under_reset) break;
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (get_field_val(ral.status.rxidle, status_val) == 1'b0);
  endtask

  // task to send a byte of data out of dut
  virtual task send_tx_byte(byte data);
    void'(ral.wdata.predict(data));
    csr_wr(.ptr(ral.wdata), .value(data));
  endtask

  // task to send a byte of data into dut, can override it to test error cases
  virtual task send_rx_byte(byte data);
    drive_rx_error_byte(.parity_err(0), .frame_err(0), .data(data));
  endtask

  // drive rx byte with parity_err or frame_err, data is random
  virtual task drive_rx_error_byte(bit parity_err, bit frame_err, byte data = $urandom);
    uart_seq send_rx_seq;
    `uvm_create_on(send_rx_seq, p_sequencer.uart_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(send_rx_seq,
                                   data == local::data;
                                   parity_err == local::parity_err;
                                   frame_err  == local::frame_err;
                                   )
    `uvm_send(send_rx_seq)
  endtask : drive_rx_error_byte

  // task to check if byte received is what was sent by the agent
  virtual task chk_rx_byte(logic [7:0] exp_data);
    bit [TL_DW-1:0] rdata;
    csr_rd(.ptr(ral.rdata), .value(rdata));
    // do check but only if rx is enabled
    if (ral.ctrl.rx.get_mirrored_value()) begin
      if (!cfg.under_reset) `DV_CHECK_EQ(rdata, exp_data)
    end
  endtask

  // task to read all the rx bytes
  virtual task read_all_rx_bytes();
    bit [TL_DW-1:0] rdata, fifo_status;
    int rxlvl;

    do begin
      csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
      rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
      repeat (rxlvl) begin
        wait_ignored_period_and_read_rdata(rdata);
      end
    end while (rxlvl > 0);

    `uvm_info(`gfn, "read_all_rx_bytes is done", UVM_HIGH)
  endtask : read_all_rx_bytes

  // override this function to control RX fifo level
  virtual task rand_read_rx_byte(uint weight_to_skip);
    bit [TL_DW-1:0] rdata, fifo_status;
    int             rxlvl;

    randcase
      1: begin // read & check one byte
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check some bytes
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          repeat ($urandom_range(1, rxlvl)) wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check all rx bytes
        read_all_rx_bytes();
      end
      weight_to_skip: begin
      end
    endcase
  endtask : rand_read_rx_byte

  // read rx data from CSR rdata, but wait until it's not in ignored period
  virtual task wait_ignored_period_and_read_rdata(ref bit [TL_DW-1:0] rdata);
    wait_when_in_ignored_period(.rx(1));
    csr_rd(.ptr(ral.rdata), .value(rdata));
  endtask

  // task to wait for all tx bytes to be sent
  virtual task wait_for_all_tx_bytes();
    bit [TL_DW-1:0] fifo_status, status;

    if (ral.ctrl.tx.get_mirrored_value()) begin
      cfg.clk_rst_vif.wait_clks(50);
      do begin
        if (cfg.under_reset) break;
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
        cfg.clk_rst_vif.wait_clks(dly_to_access_fifo);
        wait_if_stop_transaction_generators();
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        csr_rd(.ptr(ral.status),      .value(status));
      end while (get_field_val(ral.fifo_status.txlvl, fifo_status) > 0 ||
                 get_field_val(ral.status.txidle, status) == 0);
    end

    `uvm_info(`gfn, "wait_for_all_tx_bytes is done", UVM_HIGH)
  endtask : wait_for_all_tx_bytes

  // task to wait for tx fifo not full
  virtual task wait_for_tx_fifo_not_full();
    if (ral.ctrl.tx.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      reset_aware_simple_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                                  .spinwait_delay_ns(dly_to_access_fifo));
    end
    `uvm_info(`gfn, "wait_for_tx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_tx_fifo_not_full

  // task to wait for rx fifo not full, will be overridden in overflow test
  virtual task wait_for_rx_fifo_not_full();
    if (ral.ctrl.rx.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
       // use longer timeout as uart freq is low
      reset_aware_simple_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b0),
                                  .spinwait_delay_ns(dly_to_access_fifo),
                                  .timeout_ns(50_000_000));
    end
    `uvm_info(`gfn, "wait_for_rx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_rx_fifo_not_full

  // in some corner cases, we can't drive when the uart item is almost done
  // wait for this period to pass
  virtual task wait_when_in_ignored_period(bit tx = 0, bit rx = 0);
    wait (!(
        (tx && cfg.m_uart_agent_cfg.vif.uart_tx_clk_pulses inside `TX_IGNORED_PERIOD) ||
        (rx && cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses inside `RX_IGNORED_PERIOD)
      ));
    `uvm_info(`gfn, "wait_when_in_ignored_period is done", UVM_HIGH)
  endtask : wait_when_in_ignored_period

endclass : uart_base_vseq
