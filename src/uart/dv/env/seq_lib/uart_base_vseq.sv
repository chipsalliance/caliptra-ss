// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Multi-beat W-channel sequence for send_axi_write_custom(). Burst serialization and AW/W issue
// ordering are enforced via axi_seq_lock_mgr in axi_agent_pkg.
class uart_custom_write_data_seq extends axi_mgr_write_data_seq;
  `uvm_object_utils(uart_custom_write_data_seq)

  bit [31:0]   m_base_data;
  bit [3:0]    m_strb;
  bit          m_wuser;
  int unsigned m_beat_idx;

  function new(string name = "uart_custom_write_data_seq");
    super.new(name);
  endfunction

  virtual task body();
    m_beat_idx = 0;
    super.body();
  endtask

  virtual protected function void randomize_item(axi_write_data_item item, bit is_last);
    item.m_data = 1024'(m_base_data + m_beat_idx);
    item.m_strb = 128'(m_strb);
    item.m_last = is_last;
    item.m_user = 512'(m_wuser);
    m_beat_idx++;
  endfunction
endclass

// Beat-list W-channel sequence for tests requiring explicit per-beat data/strobe/last patterns
// and optional inter-beat clock delays while respecting axi_seq_lock_mgr and draining responses.
class uart_beat_list_write_data_seq extends axi_mgr_write_data_seq;
  `uvm_object_utils(uart_beat_list_write_data_seq)

  bit [31:0]         m_data_q[$];
  bit [3:0]          m_strb_q[$];
  bit                m_last_q[$];
  bit                m_user_q[$];
  int unsigned       m_pre_delay_clks_q[$];
  virtual clk_rst_if m_clk_rst_vif;

  function new(string name = "uart_beat_list_write_data_seq");
    super.new(name);
  endfunction

  function void add_beat(bit [31:0] data, bit [3:0] strb, bit last,
                         bit user = 1'b0, int unsigned pre_delay_clks = 0);
    m_data_q.push_back(data);
    m_strb_q.push_back(strb);
    m_last_q.push_back(last);
    m_user_q.push_back(user);
    m_pre_delay_clks_q.push_back(pre_delay_clks);
  endfunction

  virtual task body();
    if (m_data_q.size() == 0) return;

    axi_seq_lock_mgr::acquire_w_burst(m_sequencer);
    for (int unsigned i = 0; i < m_data_q.size(); i++) begin
      uvm_sequence_item   base_status_item;
      axi_write_data_item item;

      if (m_pre_delay_clks_q[i] > 0) begin
        if (m_clk_rst_vif == null) begin
          `uvm_fatal(get_full_name(), "m_clk_rst_vif must be set when pre_delay_clks > 0")
        end
        m_clk_rst_vif.wait_clks(m_pre_delay_clks_q[i]);
      end

      item = axi_write_data_item::type_id::create($sformatf("beat_%0d", i));
      start_item(item);
      item.m_data = 1024'(m_data_q[i]);
      item.m_strb = 128'(m_strb_q[i]);
      item.m_last = m_last_q[i];
      item.m_user = 512'(m_user_q[i]);
      finish_item(item);

      get_base_response(base_status_item);
      if (!$cast(rsp, base_status_item)) begin
        `uvm_fatal(get_full_name(), "Status response is not an axi_status_item")
      end
      if (!rsp.m_sending_complete) break;
    end
    axi_seq_lock_mgr::release_w_burst(m_sequencer);
  endtask
endclass

class uart_base_vseq extends dv_base_vseq #(.CFG_T               (uart_env_cfg),
                                             .RAL_T               (uart_reg_block),
                                             .COV_T               (uart_env_cov),
                                             .VIRTUAL_SEQUENCER_T (uart_virtual_sequencer));
  `uvm_object_utils(uart_base_vseq)

  // PRNG alignment with OpenTitan cip_base_vseq
  rand uint rand_reset_delay;
  rand uint csr_access_abort_pct;

  constraint rand_reset_delay_c {
    rand_reset_delay dist {
      [1 : 1000]          :/ 1,
      [1001 : 100_000]    :/ 2,
      [100_001 : 1_000_000] :/ 6,
      [1_000_001 : 5_000_000] :/ 1
    };
  }

  constraint csr_access_abort_pct_c {
    csr_access_abort_pct dist {
      0 :/ 50,
      [1:99] :/ 40,
      100 :/ 10
    };
  }

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
  bit do_interrupt         = 1'b1;
  bit en_tx_monitor_checks = 1'b1;
  bit en_rx_monitor_checks = 1'b1;
  bit in_uart_init         = 1'b0;

  // Expected RX FIFO queue and transfer byte counters for full transfer-length & byte comparisons
  byte         exp_rx_fifo_q[$];
  int unsigned tx_bytes_sent_cnt;
  int unsigned rx_bytes_pushed_cnt;
  int unsigned rx_bytes_read_cnt;

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

  virtual task pre_start();
    super.pre_start();
    if (ral.default_map.get_adapter() != null) begin
      ral.default_map.get_adapter().supports_byte_enable = 1;
    end
    ral.default_map.set_auto_predict(1);
  endtask

  virtual task dut_shutdown();
    super.dut_shutdown();
    // wait for tx and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_HIGH)
    cfg.m_uart_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "done waiting for idle", UVM_HIGH)
  endtask

  // setup basic uart features
  virtual task uart_init();
    int nco = get_nco(baud_rate, cfg.clk_freq_mhz, ral.ctrl.nco.get_n_bits());
    in_uart_init = 1'b1;
    cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
    exp_rx_fifo_q.delete();
    tx_bytes_sent_cnt   = 0;
    rx_bytes_pushed_cnt = 0;
    rx_bytes_read_cnt   = 0;

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
    // Keep TX checks enabled even when en_tx == 0 so unexpected DUT TX activity is caught.
    cfg.m_uart_agent_cfg.en_tx_checks = en_tx_monitor_checks;
    cfg.m_uart_agent_cfg.en_rx_checks = en_rx_monitor_checks & en_rx;
    cfg.disable_scb_rx_parity_check = 1'b0;
    cfg.disable_scb_rx_frame_check  = 1'b0;
    if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b1);
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
      csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
      ral.intr_enable.set(en_intr);
      csr_wr(.ptr(ral.intr_enable), .value(ral.intr_enable.get()));
      void'(ral.intr_enable.predict(ral.intr_enable.get()));

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
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.txilvl, value <= MAX_TX_WATERMARK_LVL;)
      ral.fifo_ctrl.rxilvl.set(ral.fifo_ctrl.rxilvl.value);
      ral.fifo_ctrl.txilvl.set(ral.fifo_ctrl.txilvl.value);
      csr_wr(.ptr(ral.fifo_ctrl), .value(ral.fifo_ctrl.get()));
      void'(ral.fifo_ctrl.predict(ral.fifo_ctrl.get()));
    end
    in_uart_init = 1'b0;
  endtask

  // clear fifos
  virtual task clear_fifos(bit clear_tx_fifo, bit clear_rx_fifo);
    if (clear_rx_fifo) begin
      exp_rx_fifo_q.delete();
      rx_bytes_pushed_cnt = rx_bytes_read_cnt;
    end
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
    while (cfg.stop_transaction_generators() || cfg.under_reset) begin
      wait (!cfg.under_reset);
      if (cfg.stop_transaction_generators()) cfg.clk_rst_vif.wait_clks(1);
    end
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
      if (cfg.under_reset) break;
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
    if (!cfg.under_reset) wait_when_in_ignored_period(.tx(1));
  endtask

  virtual task spinwait_rxidle();
    bit [TL_DW-1:0] status_val;
    if (!ral.ctrl.rx.get_mirrored_value()) return;
    do begin
      if (cfg.under_reset) break;
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (get_field_val(ral.status.rxidle, status_val) == 1'b0);
    if (!cfg.under_reset) wait_when_in_ignored_period(.rx(1));
  endtask

  // Helper to write a byte to WDATA with explicit byte_en mask propagated to both the bus
  // transaction (uvm_reg_bus_op.byte_en) and RAL/scoreboard prediction (pre_write + predict + post_write).
  virtual task write_wdata_with_mask(input byte               data,
                                     input bit [TL_DBW-1:0]   mask = 4'b0001,
                                     output uvm_status_e      status);
    uvm_reg_adapter     adapter = ral.default_map.get_adapter();
    uvm_sequencer_base  sqr     = ral.default_map.get_sequencer();
    uvm_reg_bus_op      rw;
    uvm_sequence_item   item, rsp_item;
    uvm_reg_cb_iter     cbs;
    uvm_reg_item        reg_item;
    axi_reg_op_item     ext;

    status = UVM_NOT_OK;
    wait_if_stop_transaction_generators();
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    rw.kind    = UVM_WRITE;
    rw.addr    = ral.wdata.get_address();
    rw.n_bits  = (mask == 4'b0001) ? 8 : 32;
    rw.byte_en = mask;
    rw.data    = {24'h0, data};

    ext        = axi_reg_op_item::type_id::create("wdata_mask_ext");
    ext.m_rw   = rw;

    reg_item             = new("wdata_masked_item");
    reg_item.element     = ral.wdata;
    reg_item.path        = UVM_FRONTDOOR;
    reg_item.kind        = UVM_WRITE;
    reg_item.value       = new[1];
    reg_item.value[0]    = rw.data;
    reg_item.extension   = ext;

    cbs = new(ral.wdata);
    for (uvm_reg_cbs cb = cbs.first(); cb != null; cb = cbs.next()) begin
      cb.pre_write(reg_item);
    end

    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    status = (!cfg.under_reset && cfg.clk_rst_vif.rst_n) ? rw.status : UVM_NOT_OK;
    reg_item.status = status;

    if (status == UVM_IS_OK) begin
      void'(ral.wdata.predict(.value(rw.data), .be(mask), .kind(UVM_PREDICT_DIRECT)));
      if (mask[0]) tx_bytes_sent_cnt++;
    end

    cbs = new(ral.wdata);
    for (uvm_reg_cbs cb = cbs.first(); cb != null; cb = cbs.next()) begin
      cb.post_write(reg_item);
    end
  endtask

  // Multi-byte FIFO helper that preserves the intended single-byte strobe (4'b0001) through both
  // the bus write and RAL/scoreboard prediction without inserting full-word padding zeros.
  virtual task access_data_fifo(ref byte data_q[$]);
    while (data_q.size() > 0 && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      uvm_status_e status;
      byte         b    = data_q.pop_front();
      bit [3:0]    mask = 4'b0001;
      wait_for_tx_fifo_not_full();
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      write_wdata_with_mask(.data(b), .mask(mask), .status(status));
    end
  endtask

  // task to send a byte of data out of dut with explicit single-byte strobe (4'b0001)
  // propagated through both bus write and RAL/scoreboard prediction via write_wdata_with_mask.
  virtual task send_tx_byte(byte data);
    uvm_status_e status;
    write_wdata_with_mask(.data(data), .mask(4'b0001), .status(status));
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
    if (!cfg.under_reset && ral.ctrl.rx.get_mirrored_value() &&
        !ral.ctrl.llpbk.get_mirrored_value() && !ral.ctrl.slpbk.get_mirrored_value() &&
        !(parity_err && ral.ctrl.parity_en.get_mirrored_value()) && !frame_err &&
        (exp_rx_fifo_q.size() < RxFifoDepth)) begin
      exp_rx_fifo_q.push_back(data);
      rx_bytes_pushed_cnt++;
    end
  endtask : drive_rx_error_byte

  // Drive an RX byte with a framing error (stop_bit = 0) and return uart_rx to idle (1)
  // at 75% of the stop-bit period (after both the monitor and DUT sample stop_bit=0 at the
  // 50% negedge of uart_rx_clk, and before the DUT's false-start-bit mid-sample check at 100%)
  // so the bad stop bit does not start a second phantom 0xFF frame.
  virtual task drive_rx_frame_err_byte(byte data = $urandom);
    fork
      drive_rx_error_byte(.parity_err(0), .frame_err(1), .data(data));
      begin
        wait(cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == 1 || cfg.under_reset);
        if (!cfg.under_reset) begin
          @(negedge cfg.m_uart_agent_cfg.vif.uart_rx_clk or posedge cfg.under_reset);
          if (!cfg.under_reset) begin
            #(cfg.m_uart_agent_cfg.vif.uart_clk_period / 4);
            if (!cfg.under_reset) cfg.m_uart_agent_cfg.vif.uart_rx <= 1'b1;
          end
        end
      end
    join
    if (!cfg.under_reset) #(cfg.m_uart_agent_cfg.vif.uart_clk_period);
  endtask : drive_rx_frame_err_byte

  // task to check if byte received is what was sent by the agent
  virtual task chk_rx_byte(logic [7:0] exp_data);
    bit [TL_DW-1:0] rdata;
    csr_rd(.ptr(ral.rdata), .value(rdata));
    if ($test$plusargs("inject_corrupt_byte")) begin
      rdata[7:0] ^= 8'hFF;
    end
    // do check but only if rx is enabled
    if (ral.ctrl.rx.get_mirrored_value()) begin
      if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
      rx_bytes_read_cnt++;
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(rdata[TL_DW-1:8], '0, "Upper bits [31:8] of RDATA must be 0")
        `DV_CHECK_EQ(rdata[7:0], exp_data, "RX FIFO rdata byte comparison")
      end
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
    bit [TL_DW-1:0] rdata, fifo_status, status_val;
    int             rxlvl;

    randcase
      1: begin // read & check one byte
        csr_rd(.ptr(ral.status), .value(status_val));
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check some bytes
        csr_rd(.ptr(ral.status), .value(status_val));
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          repeat ($urandom_range(1, rxlvl)) wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check all rx bytes
        csr_rd(.ptr(ral.status), .value(status_val));
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
    if ($test$plusargs("inject_corrupt_byte")) begin
      rdata[7:0] ^= 8'hFF;
    end
    if (!cfg.under_reset) begin
      rx_bytes_read_cnt++;
      `DV_CHECK_EQ(rdata[TL_DW-1:8], '0, "Upper bits [31:8] of RDATA must be 0")
      if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
      if (cfg.m_uart_agent_cfg.en_rx_checks && ral.ctrl.rx.get_mirrored_value()) begin
        `DV_CHECK_EQ(rdata[7:0], ral.rdata.get_mirrored_value()[7:0],
                     "RX FIFO rdata byte comparison against expected")
      end
    end
  endtask

  // Read intr_state CSR and compare against hardware interrupt output pins
  virtual task check_interrupts(output bit [TL_DW-1:0] intr_status);
    bit [NumUartIntr-1:0] pins_before, pins_after, pins_changed, en_intr_before, en_intr_val;
    bit init_active;
    if (cfg.under_reset) return;
    init_active    = in_uart_init;
    pins_before    = cfg.intr_vif.pins[NumUartIntr-1:0];
    en_intr_before = ral.intr_enable.get_mirrored_value()[NumUartIntr-1:0];
    pins_changed   = '0;
    fork
      begin : isolation_fork
        fork
          csr_rd(.ptr(ral.intr_state), .value(intr_status));
          forever begin
            @(cfg.intr_vif.pins);
            pins_changed |= (cfg.intr_vif.pins[NumUartIntr-1:0] ^ pins_before);
          end
        join_any
        disable fork;
      end : isolation_fork
    join
    pins_after  = cfg.intr_vif.pins[NumUartIntr-1:0];
    pins_changed |= (pins_after ^ pins_before);
    en_intr_val = ral.intr_enable.get_mirrored_value()[NumUartIntr-1:0];
    init_active |= in_uart_init | (en_intr_before != en_intr_val) |
                   (ral.intr_enable.get()[NumUartIntr-1:0] != en_intr_val);
    if (!cfg.under_reset && cfg.clk_rst_vif.rst_n && !init_active) begin
      `DV_CHECK_EQ(intr_status[TL_DW-1:NumUartIntr], '0, "Upper bits of intr_state must be 0")
      for (int i = 0; i < NumUartIntr; i++) begin
        if (!pins_changed[i]) begin
          uart_intr_e intr = uart_intr_e'(i);
          `DV_CHECK_EQ(pins_after[i], (intr_status[i] & en_intr_val[i]),
                       $sformatf("Interrupt output pin mismatch for %0s", intr.name()))
        end
      end
    end
  endtask : check_interrupts

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

  // Resolve the AXI manager agent handle from p_sequencer, failing closed if disconnected.
  virtual function axi_mgr_agent get_axi_agent();
    if (p_sequencer == null || p_sequencer.axi_agent_h == null) begin
      `uvm_fatal(`gfn, "p_sequencer.axi_agent_h is null; cannot issue raw AXI transactions")
    end
    return p_sequencer.axi_agent_h;
  endfunction : get_axi_agent

  // Shared helper: send custom AXI write supporting burst, size, len, lock, id, wuser, and
  // bready_delay. Uses a multi-beat W-burst sequence serialized via axi_seq_lock_mgr (preserving
  // AW/W ordering and preventing W-beat interleaving across concurrent writes) and routes B
  // responses through m_write_response_router with reset-epoch tracking.
  virtual task send_axi_write_custom(bit [63:0] addr, bit [31:0] data, bit [3:0] strb,
                                     bit [2:0] size = 3'd2, burst_e burst = BurstFixed,
                                     int bready_delay = 0, bit [7:0] len = 8'd0,
                                     bit lock = 1'b0, bit [7:0] id = 8'h0,
                                     bit [31:0] user = 32'h0,
                                     bit check_err = 1'b0, bit exp_err = 1'b1,
                                     bit wuser = 1'b0);
    axi_mgr_agent              axi_agent = get_axi_agent();
    axi_mgr_txn_request_seq    aw_seq;
    uart_custom_write_data_seq w_seq;
    axi_mgr_write_response_seq b_seq;
    axi_write_response_item    write_rsp;
    int unsigned               start_epoch;

    aw_seq = axi_mgr_txn_request_seq::type_id::create("aw_seq_c");
    aw_seq.m_use_fixed_id     = 1'b1;
    aw_seq.m_fixed_id         = id;
    aw_seq.m_use_fixed_addr   = 1'b1;
    aw_seq.m_fixed_addr       = addr;
    aw_seq.m_use_fixed_len    = 1'b1;
    aw_seq.m_fixed_len        = len;
    aw_seq.m_use_fixed_size   = 1'b1;
    aw_seq.m_fixed_size       = size;
    aw_seq.m_use_fixed_burst  = 1'b1;
    aw_seq.m_fixed_burst      = burst;
    aw_seq.m_use_fixed_lock   = 1'b1;
    aw_seq.m_fixed_lock       = lock;
    aw_seq.m_use_fixed_user   = 1'b1;
    aw_seq.m_fixed_user       = 128'(user);

    w_seq = uart_custom_write_data_seq::type_id::create("w_seq_c");
    w_seq.m_base_data = data;
    w_seq.m_strb      = strb;
    w_seq.m_wuser     = wuser;
    if (!w_seq.randomize() with { m_number_of_items == local::len + 1; }) begin
      `uvm_fatal(`gfn, "Failed to randomize w_seq_c.")
    end

    b_seq = axi_mgr_write_response_seq::type_id::create("b_seq_c");
    b_seq.m_use_fixed_valid_to_ready_delay    = 1'b1;
    b_seq.m_fixed_valid_to_ready_delay        = (bready_delay > 0) ? bready_delay : 0;
    b_seq.m_use_fixed_ready_without_valid_pct = 1'b1;
    b_seq.m_fixed_ready_without_valid_pct     = 0;

    begin
      bit rsp_done    = 1'b0;
      bit req_aborted = 1'b0;
      axi_seq_lock_mgr::acquire_aw_w_issue(axi_agent.get_write_request_sequencer());
      start_epoch = axi_agent.get_write_response_router().get_reset_epoch();
      axi_agent.get_write_response_router().register_waiter(id, start_epoch);

      fork begin
        if (!req_aborted && (axi_agent.get_write_response_router().get_reset_epoch() == start_epoch)) begin
          b_seq.start(axi_agent.get_write_response_sequencer());
          if (b_seq.rsp != null) begin
            axi_agent.get_write_response_router().on_response(b_seq.rsp.m_id, b_seq.rsp);
          end
        end
        rsp_done = 1'b1;
      end join_none

      fork
        aw_seq.start(axi_agent.get_write_request_sequencer());
        w_seq.start(axi_agent.get_write_data_sequencer());
      join
      axi_seq_lock_mgr::release_aw_w_issue(axi_agent.get_write_request_sequencer());

      if (aw_seq.rsp != null && aw_seq.rsp.m_sending_complete &&
          w_seq.rsp != null && w_seq.rsp.m_sending_complete) begin
        uvm_sequence_item raw_b_rsp;
        axi_agent.get_write_response_router().wait_for_response(
            id, raw_b_rsp,
            .use_start_epoch(1'b1), .start_epoch(start_epoch),
            .pre_registered(1'b1), .release_waiter(1'b1));
        if (raw_b_rsp != null) void'($cast(write_rsp, raw_b_rsp));
      end else begin
        req_aborted = 1'b1;
        axi_agent.get_write_response_router().unregister_waiter(id);
      end
      wait (rsp_done || (axi_agent.get_write_response_router().get_reset_epoch() != start_epoch));
    end

    if (check_err && !cfg.under_reset && cfg.clk_rst_vif.rst_n && write_rsp != null) begin
      axi_write_response_item::bresp_e exp_bresp = exp_err ?
          axi_write_response_item::BRespSlverr : axi_write_response_item::BRespOkay;
      `DV_CHECK_EQ(write_rsp.m_resp, exp_bresp,
                   $sformatf("Write response mismatch at addr=0x%0h (bready_delay=%0d)", addr, bready_delay))
    end
  endtask : send_axi_write_custom

  // Shared helper: send raw AXI read supporting burst, size, len, lock, id, and rready_delay.
  // Serializes AR issue with burst-level router waiter registration and demand-driven token
  // conservation so concurrent multi-beat same-ID and multi-ID raw reads stay ordered cleanly.
  virtual task send_axi_read_raw(bit [63:0] addr, bit exclusive_lock = 1'b0, bit [2:0] size = 3'd2,
                                 bit [3:0] mask = 4'hF, int rready_delay = 0,
                                 burst_e burst = BurstFixed, bit [7:0] len = 8'd0,
                                 bit [7:0] id = 8'h0, bit user_lsb = 1'b0,
                                 bit check_err = 1'b0, bit exp_err = 1'b1);
    axi_mgr_agent           axi_agent      = get_axi_agent();
    axi_mgr_txn_request_seq ar_seq         = axi_mgr_txn_request_seq::type_id::create("ar_seq_raw");
    int unsigned            num_beats      = len + 1;
    bit                     reset_seen     = 1'b0;
    bit                     done           = 1'b0;
    int unsigned            tokens_allowed = 1;
    int unsigned            tokens_started = 0;
    int unsigned            start_epoch;

    ar_seq.m_use_fixed_id      = 1'b1;
    ar_seq.m_fixed_id          = id;
    ar_seq.m_use_fixed_addr    = 1'b1;
    ar_seq.m_fixed_addr        = addr;
    ar_seq.m_use_fixed_len     = 1'b1;
    ar_seq.m_fixed_len         = len;
    ar_seq.m_use_fixed_burst   = 1'b1;
    ar_seq.m_fixed_burst       = burst;
    ar_seq.m_use_fixed_size    = 1'b1;
    ar_seq.m_fixed_size        = size;
    ar_seq.m_use_fixed_lock    = 1'b1;
    ar_seq.m_fixed_lock        = exclusive_lock;
    ar_seq.m_use_fixed_user    = 1'b1;
    ar_seq.m_fixed_user        = 128'h0;
    ar_seq.m_fixed_user[21:18] = mask;
    ar_seq.m_fixed_user[0]     = user_lsb;

    axi_seq_lock_mgr::acquire_ar_issue(axi_agent.get_read_request_sequencer());
    start_epoch = axi_agent.get_read_response_router().get_reset_epoch();
    axi_agent.get_read_response_router().register_waiter(id, start_epoch);

    begin
      bit r_loop_done = 1'b0;
      fork begin
        forever begin
          axi_mgr_read_data_seq cur_r_seq;
          wait (reset_seen ||
                (axi_agent.get_read_response_router().get_reset_epoch() != start_epoch) ||
                (tokens_started < tokens_allowed) ||
                (done && (tokens_started >= tokens_allowed)));
          if (reset_seen ||
              (axi_agent.get_read_response_router().get_reset_epoch() != start_epoch) ||
              (done && (tokens_started >= tokens_allowed))) break;
          cur_r_seq = axi_mgr_read_data_seq::type_id::create($sformatf("r_seq_%0d", tokens_started));
          if (rready_delay > 0) begin
            cur_r_seq.m_use_fixed_valid_to_ready_delay    = 1'b1;
            cur_r_seq.m_fixed_valid_to_ready_delay        = rready_delay;
            cur_r_seq.m_use_fixed_ready_without_valid_pct = 1'b1;
            cur_r_seq.m_fixed_ready_without_valid_pct     = 0;
          end
          tokens_started++;
          cur_r_seq.start(axi_agent.get_read_data_sequencer());
          if (cur_r_seq.rsp != null) begin
            axi_agent.get_read_response_router().on_response(cur_r_seq.rsp.m_id, cur_r_seq.rsp);
            if (reset_seen ||
                (axi_agent.get_read_response_router().get_reset_epoch() != start_epoch) ||
                (done && (tokens_started >= tokens_allowed))) break;
          end else begin
            reset_seen = 1'b1;
            break;
          end
        end
        r_loop_done = 1'b1;
      end join_none

      ar_seq.start(axi_agent.get_read_request_sequencer());
      axi_seq_lock_mgr::release_ar_issue(axi_agent.get_read_request_sequencer());

      if (ar_seq.rsp != null && ar_seq.rsp.m_sending_complete) begin
        for (int unsigned i = 0; i < num_beats; i++) begin
          uvm_sequence_item  raw_r_rsp;
          axi_read_data_item beat_item;
          bit                is_final_beat = (i + 1 == num_beats);
          axi_agent.get_read_response_router().wait_for_response(
              id, raw_r_rsp,
              .use_start_epoch(1'b1), .start_epoch(start_epoch),
              .pre_registered(1'b1), .release_waiter(is_final_beat));
          if (raw_r_rsp == null) begin
            reset_seen = 1'b1;
            break;
          end
          if ($cast(beat_item, raw_r_rsp)) begin
            if (check_err && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
              axi_read_data_item::rresp_e exp_rresp = exp_err ?
                  axi_read_data_item::RRespSlverr : axi_read_data_item::RRespOkay;
              `DV_CHECK_EQ(beat_item.m_resp, exp_rresp,
                           $sformatf("Read response mismatch at addr=0x%0h (rready_delay=%0d)", addr, rready_delay))
            end
            if (beat_item.m_last && !is_final_beat) begin
              tokens_allowed = i + 1;
              axi_agent.get_read_response_router().unregister_waiter(id);
              break;
            end else if (!beat_item.m_last && !is_final_beat) begin
              tokens_allowed = i + 2;
            end
          end
        end
      end else begin
        reset_seen = 1'b1;
        axi_agent.get_read_response_router().unregister_waiter(id);
      end
      done = 1'b1;
      wait (r_loop_done || (axi_agent.get_read_response_router().get_reset_epoch() != start_epoch));
    end
  endtask : send_axi_read_raw

endclass : uart_base_vseq
