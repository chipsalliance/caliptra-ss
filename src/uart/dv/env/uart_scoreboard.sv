// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef class uart_scoreboard;

class uart_reg_cbs extends uvm_reg_cbs;
  uart_scoreboard sb;

  virtual task pre_write(uvm_reg_item rw);
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      sb.reg_pre_write(rw.element.get_name());
    end
    if (rw.element != null && rw.element.get_name() == "wdata" &&
        rw.value.size() > 0 && rw.value[0][31:8] == 24'h0) begin
      axi_reg_adapter::m_next_byte_en     = 4'b0001;
      axi_reg_adapter::m_next_byte_en_reg = sb.ral.wdata;
      axi_reg_adapter::m_use_next_byte_en = 1'b1;
    end
  endtask

  virtual task pre_read(uvm_reg_item rw);
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      sb.reg_pre_read(rw.element.get_name());
    end
  endtask
  
  virtual task post_write(uvm_reg_item rw);
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      sb.reg_post_write(rw.element.get_name());
    end
    if (rw.status == UVM_IS_OK) begin
      bit [3:0] be = 4'b1111;
      if (rw.element != null && rw.element.get_name() == "wdata") begin
        be = axi_reg_adapter::m_last_byte_en;
        axi_reg_adapter::m_last_byte_en = 4'b1111;
      end
      sb.reg_write(rw.element.get_name(), rw.value[0], be);
    end
  endtask

  virtual task post_read(uvm_reg_item rw);
    if (rw.status == UVM_IS_OK) begin
      sb.reg_read(rw.element.get_name(), rw.value[0]);
    end
  endtask
endclass

class uart_scoreboard extends dv_base_scoreboard #(.CFG_T(uart_env_cfg),
                                                    .RAL_T(uart_reg_block),
                                                    .COV_T(uart_env_cov));
  `uvm_component_utils(uart_scoreboard)

  virtual uart_if    uart_vif;
  virtual uart_nf_if uart_nf_vif;

  // local variables
  local bit tx_enabled;
  local bit rx_enabled;
  local bit nf_enabled;
  local bit slpbk_enabled;
  local bit llpbk_enabled;
  local bit parity_en_enabled;
  local bit parity_odd_enabled;
  local int uart_tx_clk_pulses;
  local int uart_rx_clk_pulses;

  // expected values
  local bit tx_full_exp, rx_full_exp, tx_empty_exp, rx_empty_exp, tx_idle_exp, rx_idle_exp;
  local int txlvl_exp, rxlvl_exp;
  local bit [NumUartIntr-1:0] intr_exp;
  local bit [NumUartIntr-1:0] status_intr_test;
  local bit [7:0] rdata_exp;
  local bit [7:0] rdata_exp_q[$];
  // store tx/rx_q and pulse counts at pre_read phase
  local int tx_q_size_at_addr_phase, rx_q_size_at_addr_phase;
  local int status_tx_q_at_pre_read, status_tx_proc_at_pre_read, status_rx_q_at_pre_read;
  local int status_tx_pulses_at_pre_read, status_rx_pulses_at_pre_read;
  local int status_csr_wr_at_pre_read;
  local int fstatus_tx_q_at_pre_read, fstatus_tx_proc_at_pre_read, fstatus_rx_q_at_pre_read;
  local int fstatus_tx_pulses_at_pre_read, fstatus_rx_pulses_at_pre_read;
  local int fstatus_csr_wr_at_pre_read;
  local bit [NumUartIntr-1:0] intr_exp_at_addr_phase;
  local int intr_tx_pulses_at_pre_read, intr_rx_pulses_at_pre_read;
  local int intr_csr_wr_at_pre_read;
  local int csr_writes_in_flight;

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(uart_item)    uart_tx_fifo;
  uvm_tlm_analysis_fifo #(uart_item)    uart_rx_fifo;

  // local queues to hold incoming packets pending comparison
  uart_item tx_q[$];
  // when item is removed from fifo and being sent on UART tx interface, store it in this queue
  uart_item tx_processing_item_q[$];
  uart_item rx_q[$];

  // it takes 3 cycles to move item from fifo to process, which delays reg status change
  // and it also takes 3 cycles to trigger tx watermark interrupt
  parameter uint NUM_CLK_DLY_TO_UPDATE_TX_WATERMARK = 3;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uart_tx_fifo = new("uart_tx_fifo", this);
    uart_rx_fifo = new("uart_rx_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    uvm_reg regs[$];
    super.connect_phase(phase);
    uart_vif = cfg.m_uart_agent_cfg.vif;

    if (!uvm_config_db#(virtual uart_nf_if)::get(this, "", "uart_nf_vif", uart_nf_vif)) begin
      `uvm_fatal(`gfn, "failed to get uart_nf_if handle from uvm_config_db")
    end
    begin
      uart_reg_cbs reg_cb = new();
      reg_cb.sb = this;
      ral.get_registers(regs);
      foreach (regs[i]) begin
        uvm_reg_cb::add(regs[i], reg_cb);
      end
    end
  endfunction

  
  virtual function void reg_pre_write(string reg_name);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    csr_writes_in_flight++;
  endfunction

  virtual function void reg_post_write(string reg_name);
    if (csr_writes_in_flight > 0) csr_writes_in_flight--;
  endfunction

  virtual function void reg_pre_read(string reg_name);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    uart_tx_clk_pulses = uart_vif.uart_tx_clk_pulses;
    uart_rx_clk_pulses = uart_vif.uart_rx_clk_pulses;
    case (reg_name)
      "rdata": begin
        if (rx_q.size() > 0) begin
          uart_item rx_q_item = rx_q.pop_front();
          rdata_exp_q.push_back(rx_q_item.data);
          predict_rx_watermark_intr();
        end
      end
      "status": begin
        status_tx_q_at_pre_read      = tx_q.size();
        status_tx_proc_at_pre_read   = tx_processing_item_q.size();
        status_rx_q_at_pre_read      = rx_q.size();
        status_tx_pulses_at_pre_read = uart_vif.uart_tx_clk_pulses;
        status_rx_pulses_at_pre_read = uart_vif.uart_rx_clk_pulses;
        status_csr_wr_at_pre_read    = csr_writes_in_flight;
      end
      "fifo_status": begin
        fstatus_tx_q_at_pre_read      = tx_q.size();
        fstatus_tx_proc_at_pre_read   = tx_processing_item_q.size();
        fstatus_rx_q_at_pre_read      = rx_q.size();
        fstatus_tx_pulses_at_pre_read = uart_vif.uart_tx_clk_pulses;
        fstatus_rx_pulses_at_pre_read = uart_vif.uart_rx_clk_pulses;
        fstatus_csr_wr_at_pre_read    = csr_writes_in_flight;
      end
      "intr_state": begin
        intr_exp_at_addr_phase     = intr_exp;
        intr_tx_pulses_at_pre_read = uart_vif.uart_tx_clk_pulses;
        intr_rx_pulses_at_pre_read = uart_vif.uart_rx_clk_pulses;
        intr_csr_wr_at_pre_read    = csr_writes_in_flight;
      end
      default: ;
    endcase
  endfunction

  virtual function void reg_write(string reg_name, uvm_reg_data_t val, bit [3:0] be = 4'b1111);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    case (reg_name)
      "ctrl": begin
        if (be != 4'b1111) return;
        tx_enabled = val[0];
        rx_enabled = val[1];
        nf_enabled = val[2];
        slpbk_enabled = val[4];
        llpbk_enabled = val[5];
        parity_en_enabled = val[6];
        parity_odd_enabled = val[7];
        if (slpbk_enabled) begin
          tx_q.delete();
          tx_processing_item_q.delete();
        end else if ((tx_q.size() > 0 || tx_processing_item_q.size() > 0) && tx_enabled) begin
          if (tx_q.size() > 0 && tx_processing_item_q.size() == 0) begin
            tx_processing_item_q.push_back(tx_q.pop_front());
          end
        end
        predict_tx_watermark_intr();
        predict_rx_watermark_intr();
      end
      "wdata": begin
        if (!be[0]) return;
        if (slpbk_enabled || ral.ctrl.slpbk.get_mirrored_value() || ral.ctrl.slpbk.get()) begin
          // In system loopback, the byte does not exit via external TX monitor
        end else if (tx_q.size() < TxFifoDepth) begin
          uart_item tx_item = uart_item::type_id::create("tx_item");
          tx_item.data = val[7:0];
          tx_q.push_back(tx_item);
          if (cfg.en_cov) begin
            cov.tx_fifo_level_cg.sample(tx_q.size() + tx_processing_item_q.size(), 0);
          end
          if (tx_enabled && tx_processing_item_q.size() == 0 && tx_q.size() > 0) begin
            tx_processing_item_q.push_back(tx_q.pop_front());
          end
          predict_tx_watermark_intr();
        end else begin
          `uvm_info(`gfn, "wdata write dropped by scoreboard due to full TX FIFO", UVM_HIGH)
        end
      end
      "fifo_ctrl": begin
        if (!be[0]) return;
        if (val[1]) begin // txrst is bit 1
          int lvl = (tx_q.size() + tx_processing_item_q.size() > 0) ?
                    (tx_q.size() + tx_processing_item_q.size()) : txlvl_exp;
          tx_q.delete();
          if (!tx_enabled && uart_vif.uart_tx_clk_pulses == 0) begin
            tx_processing_item_q.delete();
          end
          txlvl_exp = 0;
          if (cfg.en_cov) cov.tx_fifo_level_cg.sample(lvl, 1);
        end
        if (val[0]) begin // rxrst is bit 0
          int lvl = (rx_q.size() > 0) ? rx_q.size() : rxlvl_exp;
          rx_q.delete();
          rdata_exp_q.delete();
          rxlvl_exp = 0;
          if (cfg.en_cov) cov.rx_fifo_level_cg.sample(lvl, 1);
        end
        predict_tx_watermark_intr();
        predict_rx_watermark_intr();
      end
      "timeout_ctrl": begin
        if (be != 4'b1111) return;
        // Timeout coverage is sampled operationally when RxTimeout interrupt occurs
      end
      "intr_enable": begin
        if (be[1:0] != 2'b11) return;
      end
      "intr_test": begin
        if (be[1:0] != 2'b11) return;
        status_intr_test[TxWatermark] = val[TxWatermark];
        status_intr_test[TxEmpty]     = val[TxEmpty];
        status_intr_test[RxWatermark] = val[RxWatermark];
        intr_exp |= val[NumUartIntr-1:0];
        predict_tx_watermark_intr();
        predict_rx_watermark_intr();
      end
      "intr_state": begin
        if (be[1:0] != 2'b11) return;
        begin
          bit [NumUartIntr-1:0] intr_wdata = val[NumUartIntr-1:0];
          intr_wdata[TxWatermark] = 1'b0;
          intr_wdata[TxEmpty]     = 1'b0;
          intr_wdata[RxWatermark] = 1'b0;
          intr_exp &= ~intr_wdata;
        end
      end
      "ovrd": begin
        if (!be[0]) return;
      end
    endcase
  endfunction

  virtual function void reg_read(string reg_name, uvm_reg_data_t val);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    uart_tx_clk_pulses = uart_vif.uart_tx_clk_pulses;
    uart_rx_clk_pulses = uart_vif.uart_rx_clk_pulses;
    case (reg_name)
      "rdata": begin
        uvm_reg_data_t act_val = val;
        bit            has_exp = 1'b0;
        if (cfg.inject_scb_rx_corrupt || $test$plusargs("inject_corrupt_byte") ||
            $test$plusargs("inject_corrupt_rx_byte")) begin
          act_val[7:0] ^= 8'hFF;
        end
        if (rdata_exp_q.size() > 0) begin
          rdata_exp = rdata_exp_q.pop_front();
          has_exp   = 1'b1;
        end else if (rx_q.size() > 0) begin
          uart_item rx_q_item = rx_q.pop_front();
          rdata_exp = rx_q_item.data;
          has_exp   = 1'b1;
          predict_rx_watermark_intr();
        end
        if (has_exp) begin
          if (cfg.en_scb_checks) begin
            `DV_CHECK_EQ(act_val[7:0], rdata_exp, "rdata read comparison")
            `DV_CHECK_EQ(act_val[31:8], 24'h0, "rdata upper bits [31:8] must be 0")
          end
          cfg.scb_rx_compared_cnt++;
          void'(ral.rdata.predict(.value(rdata_exp), .kind(UVM_PREDICT_DIRECT)));
        end else if (cfg.en_scb_checks) begin
          `DV_CHECK_EQ(act_val[31:8], 24'h0, "rdata upper bits [31:8] must be 0")
        end
        if (cfg.en_cov) begin
          cov.rx_fifo_level_cg.sample(rx_q.size(), 0);
          cov.baud_rate_w_core_clk_cg.sample(cfg.m_uart_agent_cfg.baud_rate, cfg.clk_freq_mhz);
        end
      end
      "status": begin
        uvm_reg_data_t act_val = val;
        int            uart_bits = 10 + parity_en_enabled;
        bit            no_concurrent_wr = (csr_writes_in_flight == 0 && status_csr_wr_at_pre_read == 0);
        if ($test$plusargs("inject_corrupt_status")) begin
          act_val[5:0] ^= 6'h3F;
        end
        `DV_CHECK_EQ(act_val[31:6], 26'h0, "status reserved upper bits [31:6] must be 0")
        if (act_val[2]) `DV_CHECK_EQ(act_val[0], 1'b0, "status.txempty=1 implies status.txfull=0")
        if (act_val[3]) `DV_CHECK_EQ(act_val[2], 1'b1, "status.txidle=1 implies status.txempty=1")
        if (act_val[5]) `DV_CHECK_EQ(act_val[1], 1'b0, "status.rxempty=1 implies status.rxfull=0")

        tx_full_exp  = (tx_q.size() >= TxFifoDepth);
        tx_empty_exp = (tx_q.size() == 0);
        tx_idle_exp  = (tx_q.size() == 0) && (!tx_enabled || tx_processing_item_q.size() == 0);
        rx_full_exp  = (rx_q.size() == RxFifoDepth);
        rx_empty_exp = (rx_q.size() == 0);
        rx_idle_exp  = (uart_rx_clk_pulses == 0) || !rx_enabled;

        if (cfg.en_scb_checks && !slpbk_enabled && !llpbk_enabled &&
            !ral.ovrd.txen.get_mirrored_value()) begin
          if (cfg.m_uart_agent_cfg.en_tx_monitor && no_concurrent_wr &&
              tx_q.size() == status_tx_q_at_pre_read &&
              tx_processing_item_q.size() == status_tx_proc_at_pre_read) begin
            if (!(tx_enabled && tx_q.size() == TxFifoDepth &&
                  (is_in_ignored_period(UartTx) || (status_tx_pulses_at_pre_read inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[0], tx_full_exp, $sformatf(
                  "check tx_full fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                  tx_enabled, tx_q.size(), uart_tx_clk_pulses))
            end
            if (!(tx_enabled && (tx_q.size() inside {0, 1}) &&
                  (is_in_ignored_period(UartTx) || (status_tx_pulses_at_pre_read inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[2], tx_empty_exp, $sformatf(
                  "check tx_empty fail: uart_tx_clk_pulses = %0d, tx_q.size = %0d",
                  uart_tx_clk_pulses, tx_q.size()))
            end
            if (!(tx_q.size() == 0 &&
                  (is_in_ignored_period(UartTx) || (status_tx_pulses_at_pre_read inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[3], tx_idle_exp, $sformatf(
                  "check tx_idle fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                  tx_enabled, tx_q.size(), uart_tx_clk_pulses))
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks &&
              no_concurrent_wr && rx_q.size() == status_rx_q_at_pre_read &&
              rdata_exp_q.size() == 0) begin
            if (!(rx_enabled &&
                  (is_in_ignored_period(UartRx) || (status_rx_pulses_at_pre_read inside `RX_IGNORED_PERIOD)) &&
                  (rx_q.size() inside {RxFifoDepth - 1, RxFifoDepth}))) begin
              `DV_CHECK_EQ(act_val[1], rx_full_exp, $sformatf(
                  "check rx_full fail: rx_en = %0d, rx_q.size = %0d, uart_rx_clk_pulses = %0d",
                  rx_enabled, rx_q.size(), uart_rx_clk_pulses))
            end
            if (!((rx_q.size() inside {0, 1}) &&
                  (is_in_ignored_period(UartRx) || (status_rx_pulses_at_pre_read inside `RX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[5], rx_empty_exp, $sformatf(
                  "check rx_empty fail: uart_rx_clk_pulses = %0d, rx_q.size = %0d",
                  uart_rx_clk_pulses, rx_q.size()))
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks) begin
            if ((!(uart_rx_clk_pulses inside {1, uart_bits}) &&
                 !(status_rx_pulses_at_pre_read inside {1, uart_bits}) &&
                 ((uart_rx_clk_pulses == 0) == (status_rx_pulses_at_pre_read == 0))) ||
                (!rx_enabled && no_concurrent_wr)) begin
              `DV_CHECK_EQ(act_val[4], rx_idle_exp, $sformatf(
                  "check rx_idle fail: rx_en = %0d, uart_rx_clk_pulses = %0d",
                  rx_enabled, uart_rx_clk_pulses))
            end
          end
        end
        void'(ral.status.predict(.value(act_val), .kind(UVM_PREDICT_DIRECT)));
      end
      "fifo_status": begin
        uvm_reg_data_t act_val = val;
        bit [7:0]      txlvl_act, rxlvl_act;
        bit            no_concurrent_wr = (csr_writes_in_flight == 0 && fstatus_csr_wr_at_pre_read == 0);
        if ($test$plusargs("inject_corrupt_status")) begin
          act_val[23:16] ^= 8'hFF;
        end
        `DV_CHECK_LE(act_val[7:0], TxFifoDepth, "fifo_status.txlvl must not exceed TxFifoDepth")
        `DV_CHECK_EQ(act_val[15:8], 8'h0, "fifo_status reserved bits [15:8] must be 0")
        `DV_CHECK_LE(act_val[23:16], RxFifoDepth, "fifo_status.rxlvl must not exceed RxFifoDepth")
        `DV_CHECK_EQ(act_val[31:24], 8'h0, "fifo_status reserved bits [31:24] must be 0")

        txlvl_act = act_val[7:0];
        rxlvl_act = act_val[23:16];
        txlvl_exp = (tx_q.size() > TxFifoDepth) ? TxFifoDepth : tx_q.size();
        rxlvl_exp = rx_q.size();

        if (cfg.en_scb_checks && !slpbk_enabled && !llpbk_enabled &&
            !ral.ovrd.txen.get_mirrored_value()) begin
          if (cfg.m_uart_agent_cfg.en_tx_monitor && no_concurrent_wr) begin
            int min_tx = (txlvl_exp < fstatus_tx_q_at_pre_read) ? txlvl_exp : fstatus_tx_q_at_pre_read;
            int max_tx = (txlvl_exp > fstatus_tx_q_at_pre_read) ? txlvl_exp : fstatus_tx_q_at_pre_read;
            if (txlvl_act inside {[min_tx : max_tx]}) begin
              // exact match within read window
            end else if (tx_enabled &&
                         (is_in_ignored_period(UartTx) || (fstatus_tx_pulses_at_pre_read inside `TX_IGNORED_PERIOD)) &&
                         (txlvl_act inside {[((min_tx > 0) ? (min_tx - 1) : 0) : max_tx + 1]})) begin
              // allow +/-1 difference when item is in stop phase
            end else begin
              `uvm_error(`gfn, $sformatf("txlvl mismatch exp: %0d (+/-1), act: %0d, clk_pulses: %0d",
                                         txlvl_exp, txlvl_act, uart_tx_clk_pulses))
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks &&
              no_concurrent_wr && rdata_exp_q.size() == 0) begin
            int min_rx = (rxlvl_exp < fstatus_rx_q_at_pre_read) ? rxlvl_exp : fstatus_rx_q_at_pre_read;
            int max_rx = (rxlvl_exp > fstatus_rx_q_at_pre_read) ? rxlvl_exp : fstatus_rx_q_at_pre_read;
            if (rxlvl_act inside {[min_rx : max_rx]}) begin
              // exact match within read window
            end else if (rx_enabled &&
                         (is_in_ignored_period(UartRx) || (fstatus_rx_pulses_at_pre_read inside `RX_IGNORED_PERIOD)) &&
                         (rxlvl_act inside {[((min_rx > 0) ? (min_rx - 1) : 0) : max_rx + 1]})) begin
              // allow +/-1 difference when item is in stop phase
            end else begin
              `uvm_error(`gfn, $sformatf("rxlvl mismatch exp: %0d (+/-1), act: %0d, clk_pulses: %0d",
                                         rxlvl_exp, rxlvl_act, uart_rx_clk_pulses))
            end
          end
        end

        void'(ral.fifo_status.predict(.value(act_val), .kind(UVM_PREDICT_DIRECT)));
        if (cfg.en_cov) begin
          cov.tx_fifo_level_cg.sample(act_val[7:0], 0);
          cov.rx_fifo_level_cg.sample(act_val[23:16], 0);
        end
      end
      "intr_state": begin
        bit no_concurrent_wr = (csr_writes_in_flight == 0 && intr_csr_wr_at_pre_read == 0);
        `DV_CHECK_EQ(val[31:NumUartIntr], '0, "intr_state reserved upper bits [31:9] must be 0")
        if (cfg.en_cov) begin
          for (int i = 0; i < NumUartIntr; i++) begin
            if (val[i]) sample_detail_intr_cov(uart_intr_e'(i));
          end
        end
        if (cfg.en_scb_checks && !slpbk_enabled && !llpbk_enabled &&
            !ral.ovrd.txen.get_mirrored_value() && no_concurrent_wr) begin
          for (int i = 0; i < NumUartIntr; i++) begin
            uart_intr_e intr = uart_intr_e'(i);
            if (intr inside {TxWatermark, TxEmpty, TxDone}) begin
              if (!cfg.m_uart_agent_cfg.en_tx_monitor ||
                  !cfg.m_uart_agent_cfg.en_tx_checks ||
                  is_in_ignored_period(UartTx) ||
                  (intr_tx_pulses_at_pre_read inside `TX_IGNORED_PERIOD)) begin
                continue;
              end
            end else begin
              if (!cfg.m_uart_agent_cfg.en_rx_monitor ||
                  !cfg.m_uart_agent_cfg.en_rx_checks ||
                  intr inside {RxTimeout, RxBreakErr} ||
                  is_in_ignored_period(UartRx) ||
                  (intr_rx_pulses_at_pre_read inside `RX_IGNORED_PERIOD) ||
                  (cfg.disable_scb_rx_parity_check && intr == RxParityErr) ||
                  (cfg.disable_scb_rx_frame_check  && intr == RxFrameErr)) begin
                continue;
              end
            end
            if (intr_exp_at_addr_phase[i] == intr_exp[i]) begin
              `DV_CHECK_EQ(val[i], intr_exp[i], $sformatf("Interrupt: %0s", intr.name()))
            end
          end
        end
      end
      "intr_enable": begin
        `DV_CHECK_EQ(val[31:NumUartIntr], '0, "intr_enable reserved upper bits [31:9] must be 0")
      end
    endcase
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_uart_tx_fifo();
      process_uart_rx_fifo();
      process_nf_cov();
      process_intr_cov();
    join_none
  endtask

  virtual task process_intr_cov();
    if (!cfg.en_cov) return;
    forever begin
      @(cfg.intr_vif.pins);
      for (int i = 0; i < 9; i++) begin
        if (cfg.intr_vif.pins[i]) begin
          sample_detail_intr_cov(uart_intr_e'(i));
        end
      end
    end
  endtask

  virtual task process_nf_cov();
    if (!cfg.en_cov) begin
      return;
    end

    forever begin
      @(uart_nf_vif.cb);
      if (uart_nf_vif.cb.rx_enable) begin
        cov.noise_filter_cg.sample(uart_nf_vif.cb.rx_sync, uart_nf_vif.cb.rx_sync_q1,
          uart_nf_vif.cb.rx_sync_q2);
      end
    end
  endtask

  virtual task process_uart_tx_fifo();
    uart_item act_item, exp_item;
    forever begin
      uart_tx_fifo.get(act_item);

      `uvm_info(`gfn, $sformatf("received uart tx item:\n%0s", act_item.sprint()), UVM_LOW)
      if (tx_processing_item_q.size() > 0) begin
        exp_item = tx_processing_item_q.pop_front();
        if (tx_enabled && tx_q.size > 0) begin
          tx_processing_item_q.push_back(tx_q.pop_front());
        end
        if (cfg.inject_scb_tx_corrupt || $test$plusargs("inject_corrupt_tx_byte")) begin
          act_item.data ^= 8'hFF;
        end
        if (cfg.m_uart_agent_cfg.en_tx_checks) compare(act_item, exp_item, "TX");
      end else begin
        if (cfg.en_scb_checks && cfg.m_uart_agent_cfg.en_tx_checks &&
            !slpbk_enabled && !llpbk_enabled && !ral.ovrd.txen.get_mirrored_value()) begin
          `uvm_error(`gfn, $sformatf("Received unexpected TX item from DUT (tx_enabled=%0b): %0s",
                                     tx_enabled, act_item.sprint()))
        end
      end
      // after an item is sent, check to see if size dipped below watermark
      predict_tx_watermark_intr();
      if (cfg.en_cov) begin
        cov.tx_fifo_level_cg.sample(tx_q.size() + tx_processing_item_q.size(), 0);
        cov.baud_rate_w_core_clk_cg.sample(cfg.m_uart_agent_cfg.baud_rate, cfg.clk_freq_mhz);
      end

      if (tx_q.size() == 0 && tx_processing_item_q.size() == 0) begin
        intr_exp[TxDone] = 1;
      end
    end
  endtask

  virtual task process_uart_rx_fifo();
    uart_item item;
    forever begin
      uart_rx_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received uart rx item:\n%0s", item.sprint()), UVM_LOW)

      if (rx_enabled) begin
        bit parity = `GET_PARITY(item.data, parity_odd_enabled);
        bit parity_err = parity_en_enabled && parity != item.parity;

        if (parity_err) begin
          intr_exp[RxParityErr] = 1;
          if (cfg.en_cov) cov.rx_parity_err_cg.sample(parity_odd_enabled);
          `uvm_info(`gfn, $sformatf("dropped uart rx item due to parity err:\n%0s",
                                    item.sprint()), UVM_HIGH)
        end
        if (!item.stop_bit) begin
          intr_exp[RxFrameErr] = 1;
          `uvm_info(`gfn, $sformatf("dropped uart rx item due to frame err:\n%0s",
                                    item.sprint()), UVM_HIGH)
        end
        if (!parity_err && item.stop_bit == 1) begin // no parity/frame error
          if (rx_q.size < RxFifoDepth) begin
            rx_q.push_back(item);
            if (cfg.en_cov) cov.rx_fifo_level_cg.sample(rx_q.size(), 0);
            predict_rx_watermark_intr();
          end
          else begin
            intr_exp[RxOverflow] = 1;
            `uvm_info(`gfn, $sformatf("dropped uart rx item due to overflow:\n%0s",
                                      item.sprint()), UVM_HIGH)
          end
        end // no parity/frame error
      end // if (rx_enabled)
    end // forever
  endtask

  virtual function void predict_tx_watermark_intr(uint tx_q_size = tx_q.size);
    uint watermark = get_tx_watermark_bytes_by_level(ral.fifo_ctrl.txilvl.get_mirrored_value());
    intr_exp[TxWatermark] = (tx_q_size < watermark) || status_intr_test[TxWatermark];
    intr_exp[TxEmpty] = (tx_q_size == 0) || status_intr_test[TxEmpty];
    if (cfg.en_cov && intr_exp[TxWatermark]) begin
      cov.tx_watermark_cg.sample(ral.fifo_ctrl.txilvl.get_mirrored_value());
    end
  endfunction

  virtual function void predict_rx_watermark_intr(uint rx_q_size = rx_q.size);
    uint watermark = get_rx_watermark_bytes_by_level(ral.fifo_ctrl.rxilvl.get_mirrored_value());
    intr_exp[RxWatermark] = (rx_q_size >= watermark) || status_intr_test[RxWatermark];
    if (cfg.en_cov && intr_exp[RxWatermark]) begin
      cov.rx_watermark_cg.sample(ral.fifo_ctrl.rxilvl.get_mirrored_value());
    end
  endfunction

  // we don't model uart cycle-accurately, ignore checking when item is just/almost finished
  function bit is_in_ignored_period(uart_dir_e dir);
    case (dir)
      UartTx: return uart_vif.uart_tx_clk_pulses inside `TX_IGNORED_PERIOD;
      UartRx: return uart_vif.uart_rx_clk_pulses inside `RX_IGNORED_PERIOD;
    endcase
  endfunction

  function void compare(uart_item act, uart_item exp, string dir = "TX");
    if (!act.compare(exp)) begin
      `uvm_error(`gfn, $sformatf("%s item mismatch!\nexp:\n%0s\nobs:\n%0s",
                                  dir, exp.sprint(), act.sprint()))
    end
    else begin
      if (dir == "TX") cfg.scb_tx_compared_cnt++;
      else             cfg.scb_rx_compared_cnt++;
      `uvm_info(`gfn, $sformatf("%s item match! (tx_compared=%0d, rx_compared=%0d)\nexp:\n%0s\nobs:\n%0s",
                                 dir, cfg.scb_tx_compared_cnt, cfg.scb_rx_compared_cnt,
                                 exp.sprint(), act.sprint()), UVM_LOW)
    end
  endfunction

  // Interrupt has occurred, sample relevant covergroup for interrupts that have associated
  // control/configuration values
  function void sample_detail_intr_cov(uart_intr_e intr);
    if (!cfg.en_cov) return;
    case (intr)
      TxWatermark: cov.tx_watermark_cg.sample(ral.fifo_ctrl.txilvl.get_mirrored_value());
      RxWatermark: cov.rx_watermark_cg.sample(ral.fifo_ctrl.rxilvl.get_mirrored_value());
      RxBreakErr:  cov.rx_break_err_cg.sample(ral.ctrl.rxblvl.get_mirrored_value());
      RxTimeout:   cov.rx_timeout_cg.sample(ral.timeout_ctrl.val.get_mirrored_value());
      RxParityErr: cov.rx_parity_err_cg.sample(ral.ctrl.parity_odd.get_mirrored_value());
      default: ;
    endcase
  endfunction

  virtual task monitor_reset();
    forever begin
      if (!cfg.clk_rst_vif.rst_n) begin
        `uvm_info(`gfn, "reset occurred", UVM_HIGH)
        reset("HARD");
        cfg.reset_asserted();
        @(posedge cfg.clk_rst_vif.rst_n);
        reset("HARD");
        cfg.reset_deasserted();
        csr_utils_pkg::clear_outstanding_access();
        `uvm_info(`gfn, "out of reset", UVM_HIGH)
      end
      else begin
        @(cfg.clk_rst_vif.rst_n);
      end
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset the ral model and local fifos and queues
    uart_tx_fifo.flush();
    uart_rx_fifo.flush();
    tx_q.delete();
    tx_processing_item_q.delete();
    rx_q.delete();
    rdata_exp_q.delete();
    // reset local variables
    uart_tx_clk_pulses   = 0;
    uart_rx_clk_pulses   = 0;
    tx_q_size_at_addr_phase = 0;
    rx_q_size_at_addr_phase = 0;
    status_tx_q_at_pre_read      = 0;
    status_tx_proc_at_pre_read   = 0;
    status_rx_q_at_pre_read      = 0;
    status_tx_pulses_at_pre_read = 0;
    status_rx_pulses_at_pre_read = 0;
    status_csr_wr_at_pre_read    = 0;
    fstatus_tx_q_at_pre_read      = 0;
    fstatus_tx_proc_at_pre_read   = 0;
    fstatus_rx_q_at_pre_read      = 0;
    fstatus_tx_pulses_at_pre_read = 0;
    fstatus_rx_pulses_at_pre_read = 0;
    fstatus_csr_wr_at_pre_read    = 0;
    intr_exp_at_addr_phase     = '0;
    intr_tx_pulses_at_pre_read = 0;
    intr_rx_pulses_at_pre_read = 0;
    intr_csr_wr_at_pre_read    = 0;
    csr_writes_in_flight       = 0;
    tx_enabled           = ral.ctrl.tx.get_reset();
    rx_enabled           = ral.ctrl.rx.get_reset();
    nf_enabled           = ral.ctrl.nf.get_reset();
    slpbk_enabled        = ral.ctrl.slpbk.get_reset();
    llpbk_enabled        = ral.ctrl.llpbk.get_reset();
    parity_en_enabled    = ral.ctrl.parity_en.get_reset();
    parity_odd_enabled   = ral.ctrl.parity_odd.get_reset();
    tx_full_exp          = ral.status.txfull.get_reset();
    rx_full_exp          = ral.status.rxfull.get_reset();
    tx_empty_exp         = ral.status.txempty.get_reset();
    rx_empty_exp         = ral.status.rxempty.get_reset();
    tx_idle_exp          = ral.status.txidle.get_reset();
    rx_idle_exp          = ral.status.rxidle.get_reset();
    txlvl_exp            = ral.fifo_status.txlvl.get_reset();
    rxlvl_exp            = ral.fifo_status.rxlvl.get_reset();
    intr_exp             = ral.intr_state.get_reset();
    status_intr_test     = '0;
    rdata_exp            = ral.rdata.get_reset();
    cfg.inject_scb_tx_corrupt = 1'b0;
    cfg.inject_scb_rx_corrupt = 1'b0;
    cfg.disable_scb_rx_parity_check = 1'b0;
    cfg.disable_scb_rx_frame_check  = 1'b0;
    axi_reg_adapter::m_use_next_byte_en = 1'b0;
    axi_reg_adapter::m_last_byte_en     = 4'b1111;
    if (cfg.m_uart_agent_cfg != null && cfg.m_uart_agent_cfg.re_enable_chk_mon_on_reset) begin
      cfg.m_uart_agent_cfg.en_tx_monitor = 1'b1;
      cfg.m_uart_agent_cfg.en_rx_monitor = 1'b1;
    end


    // Predict watermark interrupts now as they're status types. This ensures the expected
    // interrupts reflect the UART state on reset.
    predict_tx_watermark_intr();
    predict_rx_watermark_intr();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `uvm_info(`gfn, $sformatf("Scoreboard comparison summary: tx_compared=%0d, rx_compared=%0d",
                              cfg.scb_tx_compared_cnt, cfg.scb_rx_compared_cnt), UVM_LOW)
    if (!cfg.m_uart_agent_cfg.en_tx_checks) begin
      tx_q.delete();
      tx_processing_item_q.delete();
    end
    if (!cfg.m_uart_agent_cfg.en_rx_checks) begin
      rx_q.delete();
    end
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_tx_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_rx_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_processing_item_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, rx_q)
  endfunction

endclass
