// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef class uart_scoreboard;

class uart_reg_cbs extends uvm_reg_cbs;
  uart_scoreboard sb;

  virtual task pre_write(uvm_reg_item rw);
    if (sb == null || sb.cfg == null || !sb.cfg.en_scb) return;
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      bit [3:0]       be = 4'b1111;
      axi_reg_op_item ext_op;
      uvm_reg_data_t  wr_val = (rw.value.size() > 0) ? rw.value[0] : '0;
      if (rw.extension != null && $cast(ext_op, rw.extension)) begin
        be = ext_op.m_rw.byte_en[3:0];
      end
      sb.reg_pre_write(rw.element.get_name(), wr_val, be, rw);
    end
  endtask

  virtual task pre_read(uvm_reg_item rw);
    if (sb == null || sb.cfg == null || !sb.cfg.en_scb) return;
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      sb.reg_pre_read(rw.element.get_name(), rw);
    end
  endtask
  
  virtual task post_write(uvm_reg_item rw);
    if (sb == null || sb.cfg == null || !sb.cfg.en_scb) return;
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      if (rw.status == UVM_IS_OK && rw.value.size() > 0) begin
        bit [3:0]       be = 4'b1111;
        axi_reg_op_item ext_op;
        if (rw.extension != null && $cast(ext_op, rw.extension)) begin
          be = ext_op.m_rw.byte_en[3:0];
        end
        sb.reg_write(rw.element.get_name(), rw.value[0], be);
      end
      sb.reg_post_write(rw.element.get_name(), (rw.status == UVM_IS_OK), rw);
    end
  endtask

  virtual task post_read(uvm_reg_item rw);
    if (sb == null || sb.cfg == null || !sb.cfg.en_scb) return;
    if (rw.element != null && rw.path == UVM_FRONTDOOR) begin
      if (rw.status == UVM_IS_OK && rw.value.size() > 0) begin
        sb.reg_read(rw.element.get_name(), rw.value[0], rw);
      end else begin
        sb.reg_read_failed(rw.element.get_name(), rw);
      end
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
  local bit timeout_en_enabled;
  local bit rx_timeout_may_be_sticky;
  local bit rx_break_may_be_sticky;
  local int rx_break_allzero_cnt;
  local bit rx_break_wait;
  local int uart_tx_clk_pulses;
  local int uart_rx_clk_pulses;

  typedef struct {
    uvm_reg_item rw_item;
    bit          ar_stamped;
    int          tx_q_sz;
    int          tx_proc_sz;
    int          rx_q_sz;
    int          rdata_q_sz;
    int          tx_pulses;
    int          rx_pulses;
    int          tx_csr_wr;
    int          rx_csr_wr;
    int          tx_wr_epoch;
    int          rx_wr_epoch;
    bit          tx_full_exp;
    bit          tx_empty_exp;
    bit          tx_idle_exp;
    bit          rx_full_exp;
    bit          rx_empty_exp;
    bit          rx_idle_exp;
  } status_pre_read_t;

  typedef struct {
    uvm_reg_item rw_item;
    int          tx_q_sz;
    int          tx_proc_sz;
    int          rx_q_sz;
    int          rdata_q_sz;
    int          tx_pulses;
    int          rx_pulses;
    int          tx_csr_wr;
    int          rx_csr_wr;
    int          tx_wr_epoch;
    int          rx_wr_epoch;
  } fstatus_pre_read_t;

  typedef struct {
    uvm_reg_item            rw_item;
    bit [NumUartIntr-1:0]   intr_exp;
    bit [NumUartIntr-1:0]   intr_en;
    logic [NumUartIntr-1:0] intr_pins;
    bit [NumUartIntr-1:0]   status_intr_test;
    bit [NumUartIntr-1:0]   event_intr_test;
    int                     tx_q_sz;
    int                     tx_proc_sz;
    int                     rx_q_sz;
    int                     rdata_q_sz;
    int                     tx_pulses;
    int                     rx_pulses;
    int                     intr_csr_wr;
    int                     tx_csr_wr;
    int                     rx_csr_wr;
    int                     intr_wr_epoch;
    int                     tx_wr_epoch;
    int                     rx_wr_epoch;
  } intr_pre_read_t;

  typedef struct {
    uvm_reg_item rw_item;
    bit [7:0]    data;
    uart_item    item;
    bit          valid;
  } rdata_exp_entry_t;

  typedef struct {
    uvm_reg_item          rw_item;
    bit [NumUartIntr-1:0] set_status_mask;
    bit [NumUartIntr-1:0] set_event_mask;
  } intr_test_pre_wr_t;

  localparam bit [NumUartIntr-1:0] EVENT_INTR_MASK =
      (1 << TxDone) | (1 << RxOverflow) | (1 << RxFrameErr) |
      (1 << RxBreakErr) | (1 << RxTimeout) | (1 << RxParityErr);

  // expected values
  local bit tx_full_exp, rx_full_exp, tx_empty_exp, rx_empty_exp, tx_idle_exp, rx_idle_exp;
  local int txlvl_exp, rxlvl_exp;
  local int unsigned last_rxlvl_act;
  local bit [NumUartIntr-1:0] intr_exp;
  local bit [NumUartIntr-1:0] committed_status_intr_test;
  local bit [NumUartIntr-1:0] committed_event_intr_test;
  local bit [NumUartIntr-1:0] status_intr_test;
  local bit [NumUartIntr-1:0] event_intr_test;
  local int                   intr_test_wr_in_flight;
  local intr_test_pre_wr_t    intr_test_pre_wr_q[$];
  local bit [7:0] rdata_exp;
  // per-transaction pre-read snapshot queues (safe under concurrent CSR reads)
  local rdata_exp_entry_t  rdata_exp_q[$];
  local status_pre_read_t  status_pre_read_q[$];
  local fstatus_pre_read_t fstatus_pre_read_q[$];
  local intr_pre_read_t    intr_pre_read_q[$];
  local int tx_csr_writes_in_flight;
  local int rx_csr_writes_in_flight;
  local int intr_csr_writes_in_flight;
  local bit active_pre_wr_map[uvm_reg_item];
  local int tx_wr_epoch;
  local int rx_wr_epoch;
  local int intr_wr_epoch;

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

  
  local function int num_valid_rdata_exp();
    int cnt = 0;
    foreach (rdata_exp_q[i]) begin
      if (rdata_exp_q[i].valid) cnt++;
    end
    return cnt;
  endfunction

  virtual function void reg_pre_write(string reg_name, uvm_reg_data_t val = '0,
                                      bit [3:0] be = 4'b1111, uvm_reg_item rw = null);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    if (rw != null) active_pre_wr_map[rw] = 1'b1;
    case (reg_name)
      "wdata", "ovrd": begin
        tx_csr_writes_in_flight++;
        tx_wr_epoch++;
      end
      "ctrl", "fifo_ctrl": begin
        tx_csr_writes_in_flight++;
        rx_csr_writes_in_flight++;
        intr_csr_writes_in_flight++;
        tx_wr_epoch++;
        rx_wr_epoch++;
        intr_wr_epoch++;
      end
      "intr_test": begin
        intr_test_pre_wr_t snap;
        intr_csr_writes_in_flight++;
        intr_wr_epoch++;
        intr_test_wr_in_flight++;
        snap.rw_item         = rw;
        snap.set_status_mask = '0;
        snap.set_event_mask  = '0;
        // Mark software-forced interrupts BEFORE the AXI write reaches the DUT so
        // process_intr_cov() cannot sample natural interrupt covergroups on intr_vif.pins
        // before post_write() runs. Use |= here so clearing bits stay guarded until post_write.
        if (be[1:0] == 2'b11) begin
          snap.set_status_mask[TxWatermark] = val[TxWatermark];
          snap.set_status_mask[TxEmpty]     = val[TxEmpty];
          snap.set_status_mask[RxWatermark] = val[RxWatermark];
          snap.set_event_mask               = (val[NumUartIntr-1:0] & EVENT_INTR_MASK);
          status_intr_test                 |= snap.set_status_mask;
          event_intr_test                  |= snap.set_event_mask;
        end
        intr_test_pre_wr_q.push_back(snap);
      end
      "intr_state", "intr_enable", "timeout_ctrl": begin
        intr_csr_writes_in_flight++;
        intr_wr_epoch++;
      end
      default: ;
    endcase
  endfunction

  local function void recompute_intr_test_masks();
    status_intr_test = committed_status_intr_test;
    event_intr_test  = committed_event_intr_test;
    foreach (intr_test_pre_wr_q[i]) begin
      status_intr_test |= intr_test_pre_wr_q[i].set_status_mask;
      event_intr_test  |= intr_test_pre_wr_q[i].set_event_mask;
    end
  endfunction

  virtual function void reg_post_write(string reg_name, bit write_ok = 1'b1,
                                       uvm_reg_item rw = null);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    if (rw != null) begin
      if (!active_pre_wr_map.exists(rw)) return;
      active_pre_wr_map.delete(rw);
    end
    case (reg_name)
      "wdata", "ovrd": begin
        if (tx_csr_writes_in_flight > 0) tx_csr_writes_in_flight--;
        tx_wr_epoch++;
      end
      "ctrl", "fifo_ctrl": begin
        if (tx_csr_writes_in_flight > 0)   tx_csr_writes_in_flight--;
        if (rx_csr_writes_in_flight > 0)   rx_csr_writes_in_flight--;
        if (intr_csr_writes_in_flight > 0) intr_csr_writes_in_flight--;
        tx_wr_epoch++;
        rx_wr_epoch++;
        intr_wr_epoch++;
      end
      "intr_test": begin
        int idx = -1;
        if (rw != null) begin
          foreach (intr_test_pre_wr_q[i]) begin
            if (intr_test_pre_wr_q[i].rw_item == rw) begin
              idx = i;
              break;
            end
          end
        end else if (intr_test_pre_wr_q.size() > 0) begin
          idx = 0;
        end
        if (idx >= 0) begin
          intr_test_pre_wr_q.delete(idx);
        end
        recompute_intr_test_masks();
        if (intr_test_wr_in_flight > 0)    intr_test_wr_in_flight--;
        if (intr_csr_writes_in_flight > 0) intr_csr_writes_in_flight--;
        intr_wr_epoch++;
      end
      "intr_state", "intr_enable", "timeout_ctrl": begin
        if (intr_csr_writes_in_flight > 0) intr_csr_writes_in_flight--;
        intr_wr_epoch++;
      end
      default: ;
    endcase
  endfunction

  virtual function void reg_pre_read(string reg_name, uvm_reg_item rw = null);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    uart_tx_clk_pulses = uart_vif.uart_tx_clk_pulses;
    uart_rx_clk_pulses = uart_vif.uart_rx_clk_pulses;
    case (reg_name)
      "rdata": begin
        rdata_exp_entry_t entry;
        rx_wr_epoch++;
        entry.rw_item = rw;
        if (rx_q.size() > 0) begin
          uart_item rx_q_item = rx_q.pop_front();
          entry.data  = rx_q_item.data;
          entry.item  = rx_q_item;
          entry.valid = 1'b1;
        end else begin
          entry.data  = 8'h0;
          entry.item  = null;
          entry.valid = 1'b0;
        end
        rdata_exp_q.push_back(entry);
      end
      "status": begin
        status_pre_read_t snap;
        snap.rw_item      = rw;
        snap.ar_stamped   = 1'b0;
        snap.tx_q_sz      = tx_q.size();
        snap.tx_proc_sz   = tx_processing_item_q.size();
        snap.rx_q_sz      = rx_q.size();
        snap.rdata_q_sz   = rdata_exp_q.size();
        snap.tx_pulses    = uart_vif.uart_tx_clk_pulses;
        snap.rx_pulses    = uart_vif.uart_rx_clk_pulses;
        snap.tx_csr_wr    = tx_csr_writes_in_flight;
        snap.rx_csr_wr    = rx_csr_writes_in_flight;
        snap.tx_wr_epoch  = tx_wr_epoch;
        snap.rx_wr_epoch  = rx_wr_epoch;
        snap.tx_full_exp  = (tx_q.size() >= TxFifoDepth);
        snap.tx_empty_exp = (tx_q.size() == 0);
        snap.tx_idle_exp  = (tx_q.size() == 0) && (!tx_enabled || tx_processing_item_q.size() == 0);
        snap.rx_full_exp  = (rx_q.size() == RxFifoDepth);
        snap.rx_empty_exp = (rx_q.size() == 0);
        snap.rx_idle_exp  = (uart_vif.uart_rx_clk_pulses == 0) || !rx_enabled;
        status_pre_read_q.push_back(snap);
      end
      "fifo_status": begin
        fstatus_pre_read_t snap;
        snap.rw_item     = rw;
        snap.tx_q_sz     = tx_q.size();
        snap.tx_proc_sz  = tx_processing_item_q.size();
        snap.rx_q_sz     = rx_q.size();
        snap.rdata_q_sz  = rdata_exp_q.size();
        snap.tx_pulses   = uart_vif.uart_tx_clk_pulses;
        snap.rx_pulses   = uart_vif.uart_rx_clk_pulses;
        snap.tx_csr_wr   = tx_csr_writes_in_flight;
        snap.rx_csr_wr   = rx_csr_writes_in_flight;
        snap.tx_wr_epoch = tx_wr_epoch;
        snap.rx_wr_epoch = rx_wr_epoch;
        fstatus_pre_read_q.push_back(snap);
      end
      "intr_state": begin
        intr_pre_read_t snap;
        snap.rw_item          = rw;
        snap.intr_exp         = intr_exp;
        snap.intr_en          = ral.intr_enable.get_mirrored_value()[NumUartIntr-1:0];
        snap.intr_pins        = cfg.intr_vif.pins[NumUartIntr-1:0];
        snap.status_intr_test = status_intr_test;
        snap.event_intr_test  = event_intr_test;
        snap.tx_q_sz       = tx_q.size();
        snap.tx_proc_sz    = tx_processing_item_q.size();
        snap.rx_q_sz       = rx_q.size();
        snap.rdata_q_sz    = rdata_exp_q.size();
        snap.tx_pulses     = uart_vif.uart_tx_clk_pulses;
        snap.rx_pulses     = uart_vif.uart_rx_clk_pulses;
        snap.intr_csr_wr   = intr_csr_writes_in_flight;
        snap.tx_csr_wr     = tx_csr_writes_in_flight;
        snap.rx_csr_wr     = rx_csr_writes_in_flight;
        snap.intr_wr_epoch = intr_wr_epoch;
        snap.tx_wr_epoch   = tx_wr_epoch;
        snap.rx_wr_epoch   = rx_wr_epoch;
        intr_pre_read_q.push_back(snap);
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
        end else if (!tx_enabled) begin
          tx_processing_item_q.delete();
        end else if (tx_q.size() > 0 || tx_processing_item_q.size() > 0) begin
          if (tx_q.size() > 0 && tx_processing_item_q.size() == 0) begin
            tx_processing_item_q.push_back(tx_q.pop_front());
          end
        end
        predict_tx_watermark_intr();
        predict_rx_watermark_intr();
      end
      "wdata": begin
        if (!be[0]) return;
        if (slpbk_enabled || ral.ctrl.slpbk.get_mirrored_value()) begin
          // In system loopback, the byte does not exit via external TX monitor
        end else if (tx_q.size() < TxFifoDepth) begin
          uart_item tx_item = uart_item::type_id::create("tx_item");
          tx_item.data = val[7:0];
          tx_q.push_back(tx_item);
          if (cfg.en_cov) begin
            cov.tx_fifo_level_cg.sample(tx_q.size(), 0);
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
          int lvl = (tx_q.size() > TxFifoDepth) ? TxFifoDepth : tx_q.size();
          tx_q.delete();
          if (!tx_enabled && uart_vif.uart_tx_clk_pulses == 0) begin
            tx_processing_item_q.delete();
          end
          txlvl_exp = 0;
          if (cfg.en_cov) cov.tx_fifo_level_cg.sample(lvl, 1);
        end
        if (val[0]) begin // rxrst is bit 0
          int lvl = (slpbk_enabled || llpbk_enabled)
                    ? last_rxlvl_act
                    : ((rx_q.size() > RxFifoDepth) ? RxFifoDepth : rx_q.size());
          rx_q.delete();
          rdata_exp_q.delete();
          rxlvl_exp      = 0;
          last_rxlvl_act = 0;
          if (cfg.en_cov) cov.rx_fifo_level_cg.sample(lvl, 1);
        end
        predict_tx_watermark_intr();
        predict_rx_watermark_intr();
      end
      "timeout_ctrl": begin
        if (be != 4'b1111) return;
        timeout_en_enabled = val[31];
        if (timeout_en_enabled) rx_timeout_may_be_sticky = 1'b1;
        // Timeout coverage is sampled operationally when RxTimeout interrupt occurs
      end
      "intr_enable": begin
        if (be[1:0] != 2'b11) return;
      end
      "intr_test": begin
        if (be[1:0] != 2'b11) return;
        committed_status_intr_test[TxWatermark] = val[TxWatermark];
        committed_status_intr_test[TxEmpty]     = val[TxEmpty];
        committed_status_intr_test[RxWatermark] = val[RxWatermark];
        committed_event_intr_test              |= (val[NumUartIntr-1:0] & EVENT_INTR_MASK);
        recompute_intr_test_masks();
        intr_exp |= val[NumUartIntr-1:0];
        if (cfg.en_cov) begin
          for (int i = 0; i < NumUartIntr; i++) begin
            if (val[i]) cov.intr_test_cg.sample(i);
          end
        end
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
          intr_exp                  &= ~intr_wdata;
          committed_event_intr_test &= ~intr_wdata;
          recompute_intr_test_masks();
          if (val[RxTimeout] && !timeout_en_enabled) begin
            rx_timeout_may_be_sticky = 1'b0;
          end
          if (val[RxBreakErr] && !cfg.disable_scb_rx_frame_check) begin
            rx_break_may_be_sticky = 1'b0;
          end
        end
      end
      "ovrd": begin
        if (!be[0]) return;
      end
    endcase
  endfunction

  virtual function void reg_read_failed(string reg_name, uvm_reg_item rw = null);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    case (reg_name)
      "rdata": begin
        int idx = -1;
        rx_wr_epoch++;
        if (rw != null) begin
          foreach (rdata_exp_q[i]) begin
            if (rdata_exp_q[i].rw_item == rw) begin
              idx = i;
              break;
            end
          end
        end else if (rdata_exp_q.size() > 0) begin
          idx = rdata_exp_q.size() - 1;
        end
        if (idx >= 0) begin
          if (rdata_exp_q[idx].valid) begin
            // Roll back speculative pop while preserving strict FIFO order across any
            // other concurrent valid rdata reads still in flight.
            int valid_idxs[$];
            for (int j = idx; j < rdata_exp_q.size(); j++) begin
              if (rdata_exp_q[j].valid) valid_idxs.push_back(j);
            end
            begin
              int       last_v  = valid_idxs[valid_idxs.size() - 1];
              uart_item rb_item = rdata_exp_q[last_v].item;
              for (int k = valid_idxs.size() - 1; k > 0; k--) begin
                rdata_exp_q[valid_idxs[k]].data = rdata_exp_q[valid_idxs[k - 1]].data;
                rdata_exp_q[valid_idxs[k]].item = rdata_exp_q[valid_idxs[k - 1]].item;
              end
              rdata_exp_q.delete(idx);
              if (rb_item != null) begin
                rx_q.push_front(rb_item);
              end
              predict_rx_watermark_intr();
            end
          end else begin
            rdata_exp_q.delete(idx);
          end
        end
      end
      "status": begin
        if (rw != null) begin
          foreach (status_pre_read_q[i]) begin
            if (status_pre_read_q[i].rw_item == rw) begin
              status_pre_read_q.delete(i);
              break;
            end
          end
        end else if (status_pre_read_q.size() > 0) begin
          void'(status_pre_read_q.pop_front());
        end
      end
      "fifo_status": begin
        if (rw != null) begin
          foreach (fstatus_pre_read_q[i]) begin
            if (fstatus_pre_read_q[i].rw_item == rw) begin
              fstatus_pre_read_q.delete(i);
              break;
            end
          end
        end else if (fstatus_pre_read_q.size() > 0) begin
          void'(fstatus_pre_read_q.pop_front());
        end
      end
      "intr_state": begin
        if (rw != null) begin
          foreach (intr_pre_read_q[i]) begin
            if (intr_pre_read_q[i].rw_item == rw) begin
              intr_pre_read_q.delete(i);
              break;
            end
          end
        end else if (intr_pre_read_q.size() > 0) begin
          void'(intr_pre_read_q.pop_front());
        end
      end
      default: ;
    endcase
  endfunction

  virtual function void reg_read(string reg_name, uvm_reg_data_t val, uvm_reg_item rw = null);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    uart_tx_clk_pulses = uart_vif.uart_tx_clk_pulses;
    uart_rx_clk_pulses = uart_vif.uart_rx_clk_pulses;
    case (reg_name)
      "rdata": begin
        uvm_reg_data_t act_val    = val;
        bit            rx_corrupt = cfg.inject_scb_rx_corrupt ||
                                    $test$plusargs("inject_corrupt_byte") ||
                                    $test$plusargs("inject_corrupt_rx_byte");
        bit            has_exp    = 1'b0;
        int            idx        = -1;
        rx_wr_epoch++;
        if (last_rxlvl_act > 0) last_rxlvl_act--;
        if (rx_corrupt) begin
          act_val[7:0] ^= 8'hFF;
        end
        if (rw != null) begin
          foreach (rdata_exp_q[i]) begin
            if (rdata_exp_q[i].rw_item == rw) begin
              idx = i;
              break;
            end
          end
        end
        if (idx < 0 && rdata_exp_q.size() > 0) idx = 0;
        if (idx >= 0) begin
          bit entry_valid = rdata_exp_q[idx].valid;
          if (entry_valid) begin
            rdata_exp = rdata_exp_q[idx].data;
            has_exp   = 1'b1;
          end
          rdata_exp_q.delete(idx);
          if (entry_valid) begin
            predict_rx_watermark_intr();
          end
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
        if (cfg.en_cov && !rx_corrupt && has_exp) begin
          cov.rx_fifo_level_cg.sample(rx_q.size(), 0);
          cov.baud_rate_w_core_clk_cg.sample(cfg.m_uart_agent_cfg.baud_rate, cfg.clk_freq_mhz);
        end
      end
      "status": begin
        status_pre_read_t pre;
        bit               has_pre = 1'b0;
        uvm_reg_data_t    act_val = val;
        int               uart_bits = 10 + parity_en_enabled;
        bit               no_concurrent_tx_wr;
        bit               no_concurrent_rx_wr;
        bit               status_checked = 1'b0;

        if (rw != null) begin
          foreach (status_pre_read_q[i]) begin
            if (status_pre_read_q[i].rw_item == rw) begin
              pre     = status_pre_read_q[i];
              has_pre = 1'b1;
              status_pre_read_q.delete(i);
              break;
            end
          end
        end
        if (!has_pre && status_pre_read_q.size() > 0) begin
          pre     = status_pre_read_q.pop_front();
          has_pre = 1'b1;
        end
        if (!has_pre) begin
          pre.tx_q_sz      = tx_q.size();
          pre.tx_proc_sz   = tx_processing_item_q.size();
          pre.rx_q_sz      = rx_q.size();
          pre.rdata_q_sz   = rdata_exp_q.size();
          pre.tx_pulses    = uart_tx_clk_pulses;
          pre.rx_pulses    = uart_rx_clk_pulses;
          pre.tx_csr_wr    = tx_csr_writes_in_flight;
          pre.rx_csr_wr    = rx_csr_writes_in_flight;
          pre.tx_wr_epoch  = tx_wr_epoch;
          pre.rx_wr_epoch  = rx_wr_epoch;
          pre.tx_full_exp  = (tx_q.size() >= TxFifoDepth);
          pre.tx_empty_exp = (tx_q.size() == 0);
          pre.tx_idle_exp  = (tx_q.size() == 0) && (!tx_enabled || tx_processing_item_q.size() == 0);
          pre.rx_full_exp  = (rx_q.size() == RxFifoDepth);
          pre.rx_empty_exp = (rx_q.size() == 0);
          pre.rx_idle_exp  = (uart_rx_clk_pulses == 0) || !rx_enabled;
        end

        no_concurrent_tx_wr = (tx_csr_writes_in_flight == 0 &&
                               pre.tx_csr_wr == 0 &&
                               tx_wr_epoch == pre.tx_wr_epoch);
        no_concurrent_rx_wr = (rx_csr_writes_in_flight == 0 &&
                               pre.rx_csr_wr == 0 &&
                               rx_wr_epoch == pre.rx_wr_epoch);
        if (cfg.inject_scb_status_corrupt || $test$plusargs("inject_corrupt_status")) begin
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
          if (cfg.m_uart_agent_cfg.en_tx_monitor && no_concurrent_tx_wr &&
              tx_q.size() == pre.tx_q_sz &&
              tx_processing_item_q.size() == pre.tx_proc_sz) begin
            if ((tx_full_exp == pre.tx_full_exp) &&
                !(tx_enabled &&
                  ((tx_q.size() == TxFifoDepth - 1) || (pre.tx_q_sz == TxFifoDepth - 1)) &&
                  ((tx_processing_item_q.size() > 0 && uart_tx_clk_pulses == 0) ||
                   (pre.tx_proc_sz > 0 && pre.tx_pulses == 0))) &&
                !(tx_enabled &&
                  ((tx_q.size() inside {TxFifoDepth - 1, TxFifoDepth}) ||
                   (pre.tx_q_sz inside {TxFifoDepth - 1, TxFifoDepth})) &&
                  (is_in_ignored_period(UartTx) || (pre.tx_pulses inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[0], tx_full_exp, $sformatf(
                  "check tx_full fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                  tx_enabled, tx_q.size(), uart_tx_clk_pulses))
              status_checked = 1'b1;
            end
            if ((tx_empty_exp == pre.tx_empty_exp) &&
                !(tx_enabled &&
                  ((tx_processing_item_q.size() > 0 && uart_tx_clk_pulses == 0) ||
                   (pre.tx_proc_sz > 0 && pre.tx_pulses == 0))) &&
                !(tx_enabled &&
                  ((tx_q.size() inside {0, 1}) || (pre.tx_q_sz inside {0, 1})) &&
                  (is_in_ignored_period(UartTx) || (pre.tx_pulses inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[2], tx_empty_exp, $sformatf(
                  "check tx_empty fail: uart_tx_clk_pulses = %0d, tx_q.size = %0d",
                  uart_tx_clk_pulses, tx_q.size()))
              status_checked = 1'b1;
            end
            if ((tx_idle_exp == pre.tx_idle_exp) &&
                !(((tx_q.size() == 0) || (pre.tx_q_sz == 0)) &&
                  (is_in_ignored_period(UartTx) || (pre.tx_pulses inside `TX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[3], tx_idle_exp, $sformatf(
                  "check tx_idle fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                  tx_enabled, tx_q.size(), uart_tx_clk_pulses))
              status_checked = 1'b1;
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks &&
              no_concurrent_rx_wr && rdata_exp_q.size() == 0 && pre.rdata_q_sz == 0) begin
            if ((rx_full_exp == pre.rx_full_exp) &&
                !(rx_enabled &&
                  (is_in_ignored_period(UartRx) || (pre.rx_pulses inside `RX_IGNORED_PERIOD)) &&
                  ((rx_q.size() inside {RxFifoDepth - 1, RxFifoDepth}) ||
                   (pre.rx_q_sz inside {RxFifoDepth - 1, RxFifoDepth})))) begin
              `DV_CHECK_EQ(act_val[1], rx_full_exp, $sformatf(
                  "check rx_full fail: rx_en = %0d, rx_q.size = %0d, uart_rx_clk_pulses = %0d",
                  rx_enabled, rx_q.size(), uart_rx_clk_pulses))
              status_checked = 1'b1;
            end
            if ((rx_empty_exp == pre.rx_empty_exp) &&
                !(((rx_q.size() inside {0, 1}) || (pre.rx_q_sz inside {0, 1})) &&
                  (is_in_ignored_period(UartRx) || (pre.rx_pulses inside `RX_IGNORED_PERIOD)))) begin
              `DV_CHECK_EQ(act_val[5], rx_empty_exp, $sformatf(
                  "check rx_empty fail: uart_rx_clk_pulses = %0d, rx_q.size = %0d",
                  uart_rx_clk_pulses, rx_q.size()))
              status_checked = 1'b1;
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks) begin
            if ((rx_enabled && (uart_rx_clk_pulses inside {[2 : uart_bits - 1]}) && no_concurrent_rx_wr) ||
                (!(uart_rx_clk_pulses inside {1, uart_bits}) &&
                 !(pre.rx_pulses inside {1, uart_bits}) &&
                 ((uart_rx_clk_pulses == 0) == (pre.rx_pulses == 0)) &&
                 (rx_idle_exp == pre.rx_idle_exp)) ||
                (!rx_enabled && no_concurrent_rx_wr)) begin
              `DV_CHECK_EQ(act_val[4], rx_idle_exp, $sformatf(
                  "check rx_idle fail: rx_en = %0d, uart_rx_clk_pulses = %0d",
                  rx_enabled, uart_rx_clk_pulses))
              status_checked = 1'b1;
            end
          end
          if (status_checked) cfg.scb_status_compared_cnt++;
        end
        if (cfg.en_scb && cfg.en_scb_checks) begin
          // Always mirror the uncorrupted bus read so self-test corruption cannot poison RAL.
          void'(ral.status.predict(.value(val), .kind(UVM_PREDICT_DIRECT)));
        end
      end
      "fifo_status": begin
        fstatus_pre_read_t pre;
        bit                has_pre         = 1'b0;
        uvm_reg_data_t     act_val         = val;
        bit                fstatus_corrupt = cfg.inject_scb_fifo_status_corrupt ||
                                             $test$plusargs("inject_corrupt_status");
        bit [7:0]          txlvl_act, rxlvl_act;
        bit                no_concurrent_tx_wr;
        bit                no_concurrent_rx_wr;
        bit                fstatus_checked = 1'b0;

        if (rw != null) begin
          foreach (fstatus_pre_read_q[i]) begin
            if (fstatus_pre_read_q[i].rw_item == rw) begin
              pre     = fstatus_pre_read_q[i];
              has_pre = 1'b1;
              fstatus_pre_read_q.delete(i);
              break;
            end
          end
        end
        if (!has_pre && fstatus_pre_read_q.size() > 0) begin
          pre     = fstatus_pre_read_q.pop_front();
          has_pre = 1'b1;
        end
        if (!has_pre) begin
          pre.tx_q_sz     = tx_q.size();
          pre.tx_proc_sz  = tx_processing_item_q.size();
          pre.rx_q_sz     = rx_q.size();
          pre.rdata_q_sz  = rdata_exp_q.size();
          pre.tx_pulses   = uart_tx_clk_pulses;
          pre.rx_pulses   = uart_rx_clk_pulses;
          pre.tx_csr_wr   = tx_csr_writes_in_flight;
          pre.rx_csr_wr   = rx_csr_writes_in_flight;
          pre.tx_wr_epoch = tx_wr_epoch;
          pre.rx_wr_epoch = rx_wr_epoch;
        end

        no_concurrent_tx_wr = (tx_csr_writes_in_flight == 0 &&
                               pre.tx_csr_wr == 0 &&
                               tx_wr_epoch == pre.tx_wr_epoch);
        no_concurrent_rx_wr = (rx_csr_writes_in_flight == 0 &&
                               pre.rx_csr_wr == 0 &&
                               rx_wr_epoch == pre.rx_wr_epoch);
        if (fstatus_corrupt) begin
          act_val[23:16] = (act_val[23:16] <= RxFifoDepth - 2) ? (act_val[23:16] + 8'd2) : 8'd0;
        end
        `DV_CHECK_LE(act_val[7:0], TxFifoDepth, "fifo_status.txlvl must not exceed TxFifoDepth")
        `DV_CHECK_EQ(act_val[15:8], 8'h0, "fifo_status reserved bits [15:8] must be 0")
        `DV_CHECK_LE(act_val[23:16], RxFifoDepth, "fifo_status.rxlvl must not exceed RxFifoDepth")
        `DV_CHECK_EQ(act_val[31:24], 8'h0, "fifo_status reserved bits [31:24] must be 0")

        txlvl_act = act_val[7:0];
        rxlvl_act = act_val[23:16];
        last_rxlvl_act = val[23:16];
        txlvl_exp = (tx_q.size() > TxFifoDepth) ? TxFifoDepth : tx_q.size();
        rxlvl_exp = rx_q.size();

        if (cfg.en_scb_checks && !slpbk_enabled && !llpbk_enabled &&
            !ral.ovrd.txen.get_mirrored_value()) begin
          if (cfg.m_uart_agent_cfg.en_tx_monitor && no_concurrent_tx_wr) begin
            int min_tx = (txlvl_exp < pre.tx_q_sz) ? txlvl_exp : pre.tx_q_sz;
            int max_tx = (txlvl_exp > pre.tx_q_sz) ? txlvl_exp : pre.tx_q_sz;
            fstatus_checked = 1'b1;
            if (txlvl_act inside {[min_tx : max_tx]}) begin
              // exact match within read window
            end else if (tx_enabled &&
                         (is_in_ignored_period(UartTx) ||
                          (pre.tx_pulses inside `TX_IGNORED_PERIOD) ||
                          (tx_processing_item_q.size() > 0 && uart_tx_clk_pulses == 0) ||
                          (pre.tx_proc_sz > 0 && pre.tx_pulses == 0)) &&
                         (txlvl_act inside {[((min_tx > 0) ? (min_tx - 1) : 0) : max_tx + 1]})) begin
              // allow +/-1 difference when item is in stop phase or pre-start-bit FIFO pop handoff
            end else begin
              `uvm_error(`gfn, $sformatf("txlvl mismatch exp: %0d (+/-1), act: %0d, clk_pulses: %0d",
                                         txlvl_exp, txlvl_act, uart_tx_clk_pulses))
            end
          end

          if (cfg.m_uart_agent_cfg.en_rx_monitor && cfg.m_uart_agent_cfg.en_rx_checks &&
              no_concurrent_rx_wr && rdata_exp_q.size() == 0 && pre.rdata_q_sz == 0) begin
            int min_rx = (rxlvl_exp < pre.rx_q_sz) ? rxlvl_exp : pre.rx_q_sz;
            int max_rx = (rxlvl_exp > pre.rx_q_sz) ? rxlvl_exp : pre.rx_q_sz;
            fstatus_checked = 1'b1;
            if (rxlvl_act inside {[min_rx : max_rx]}) begin
              // exact match within read window
            end else if (rx_enabled &&
                         (is_in_ignored_period(UartRx) || (pre.rx_pulses inside `RX_IGNORED_PERIOD)) &&
                         (rxlvl_act inside {[((min_rx > 0) ? (min_rx - 1) : 0) : max_rx + 1]})) begin
              // allow +/-1 difference when item is in stop phase
            end else begin
              `uvm_error(`gfn, $sformatf("rxlvl mismatch exp: %0d (+/-1), act: %0d, clk_pulses: %0d",
                                         rxlvl_exp, rxlvl_act, uart_rx_clk_pulses))
            end
          end
          if (fstatus_checked) cfg.scb_fifo_status_compared_cnt++;
        end

        if (cfg.en_scb && cfg.en_scb_checks) begin
          // Mirror the uncorrupted bus read so self-test corruption cannot poison RAL.
          void'(ral.fifo_status.predict(.value(val), .kind(UVM_PREDICT_DIRECT)));
        end
        if (cfg.en_cov && !fstatus_corrupt) begin
          cov.tx_fifo_level_cg.sample(val[7:0], 0);
          cov.rx_fifo_level_cg.sample(val[23:16], 0);
        end
      end
      "intr_state": begin
        intr_pre_read_t       pre;
        bit                   has_pre = 1'b0;
        uvm_reg_data_t        act_val = val;
        bit [NumUartIntr-1:0] intr_en = ral.intr_enable.get_mirrored_value()[NumUartIntr-1:0];
        bit                   no_concurrent_wr;
        bit                   intr_checked = 1'b0;

        if (rw != null) begin
          foreach (intr_pre_read_q[i]) begin
            if (intr_pre_read_q[i].rw_item == rw) begin
              pre     = intr_pre_read_q[i];
              has_pre = 1'b1;
              intr_pre_read_q.delete(i);
              break;
            end
          end
        end
        if (!has_pre && intr_pre_read_q.size() > 0) begin
          pre     = intr_pre_read_q.pop_front();
          has_pre = 1'b1;
        end
        if (!has_pre) begin
          pre.intr_exp         = intr_exp;
          pre.intr_en          = intr_en;
          pre.intr_pins        = cfg.intr_vif.pins[NumUartIntr-1:0];
          pre.status_intr_test = status_intr_test;
          pre.event_intr_test  = event_intr_test;
          pre.tx_q_sz          = tx_q.size();
          pre.tx_proc_sz       = tx_processing_item_q.size();
          pre.rx_q_sz          = rx_q.size();
          pre.rdata_q_sz       = rdata_exp_q.size();
          pre.tx_pulses        = uart_tx_clk_pulses;
          pre.rx_pulses        = uart_rx_clk_pulses;
          pre.intr_csr_wr      = intr_csr_writes_in_flight;
          pre.tx_csr_wr        = tx_csr_writes_in_flight;
          pre.rx_csr_wr        = rx_csr_writes_in_flight;
          pre.intr_wr_epoch    = intr_wr_epoch;
          pre.tx_wr_epoch      = tx_wr_epoch;
          pre.rx_wr_epoch      = rx_wr_epoch;
        end

        no_concurrent_wr = (intr_csr_writes_in_flight == 0 &&
                            pre.intr_csr_wr == 0 &&
                            intr_wr_epoch == pre.intr_wr_epoch);
        if (cfg.inject_scb_intr_corrupt) begin
          act_val[NumUartIntr-1:0] ^= {NumUartIntr{1'b1}};
        end
        `DV_CHECK_EQ(act_val[31:NumUartIntr], '0, "intr_state reserved upper bits [31:9] must be 0")
        // Sample natural interrupt detail coverage from uncorrupted bus value only, gated against
        // concurrent interrupt-CSR writes (e.g., INTR_TEST=0) and pre-read software-forced masks.
        if (cfg.en_cov && !cfg.inject_scb_intr_corrupt && no_concurrent_wr) begin
          for (int i = 0; i < NumUartIntr; i++) begin
            if (val[i] && !pre.status_intr_test[i] && !pre.event_intr_test[i]) begin
              sample_detail_intr_cov(uart_intr_e'(i));
            end
          end
        end
        if (cfg.en_scb_checks && !slpbk_enabled && !llpbk_enabled &&
            !ral.ovrd.txen.get_mirrored_value() && no_concurrent_wr) begin
          for (int i = 0; i < NumUartIntr; i++) begin
            uart_intr_e intr = uart_intr_e'(i);
            if (intr inside {TxWatermark, TxEmpty, TxDone}) begin
              if (!cfg.m_uart_agent_cfg.en_tx_monitor ||
                  !cfg.m_uart_agent_cfg.en_tx_checks ||
                  (tx_csr_writes_in_flight > 0) ||
                  (pre.tx_csr_wr > 0) ||
                  (tx_wr_epoch != pre.tx_wr_epoch) ||
                  (tx_q.size() != pre.tx_q_sz) ||
                  (tx_processing_item_q.size() != pre.tx_proc_sz) ||
                  ((intr inside {TxWatermark, TxEmpty}) &&
                   tx_enabled &&
                   ((tx_processing_item_q.size() > 0 && uart_tx_clk_pulses == 0) ||
                    (pre.tx_proc_sz > 0 && pre.tx_pulses == 0))) ||
                  is_in_ignored_period(UartTx) ||
                  (pre.tx_pulses inside `TX_IGNORED_PERIOD)) begin
                continue;
              end
            end else begin
              if (!cfg.m_uart_agent_cfg.en_rx_monitor ||
                  !cfg.m_uart_agent_cfg.en_rx_checks ||
                  (rx_csr_writes_in_flight > 0) ||
                  (pre.rx_csr_wr > 0) ||
                  (intr == RxWatermark &&
                   (rdata_exp_q.size() > 0 ||
                    pre.rdata_q_sz > 0 ||
                    rx_wr_epoch != pre.rx_wr_epoch ||
                    rx_q.size() != pre.rx_q_sz)) ||
                  (intr == RxTimeout  && (timeout_en_enabled || rx_timeout_may_be_sticky)) ||
                  (intr == RxBreakErr && (cfg.disable_scb_rx_frame_check || rx_break_may_be_sticky)) ||
                  is_in_ignored_period(UartRx) ||
                  (pre.rx_pulses inside `RX_IGNORED_PERIOD) ||
                  (cfg.disable_scb_rx_parity_check && intr == RxParityErr) ||
                  (cfg.disable_scb_rx_frame_check  && intr == RxFrameErr)) begin
                continue;
              end
            end
            if (pre.intr_exp[i] == intr_exp[i]) begin
              `DV_CHECK_EQ(act_val[i], intr_exp[i], $sformatf("Interrupt: %0s", intr.name()))
              intr_checked = 1'b1;
              if ((pre.intr_en[i] == intr_en[i]) &&
                  (pre.intr_pins[i] === cfg.intr_vif.pins[i])) begin
                `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
                                  $sformatf("Interrupt_pin: %0s", intr.name()))
              end
            end
          end
          if (intr_checked) cfg.scb_intr_compared_cnt++;
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
      process_uart_rx_break_exit();
      process_nf_cov();
      process_intr_cov();
      process_axi_read_addr_phase();
    join_none
  endtask

  // Mirror uart_core.sv BRK_WAIT -> BRK_CHK exit whenever rx_in returns high.
  virtual task process_uart_rx_break_exit();
    if (uart_vif == null) return;
    forever begin
      @(posedge uart_vif.uart_rx);
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        rx_break_wait = 1'b0;
      end
    end
  endtask

  virtual task process_axi_read_addr_phase();
    if (cfg.m_axi_agent_cfg == null || cfg.m_axi_agent_cfg.read_request_vif == null) return;
    forever begin
      @(cfg.m_axi_agent_cfg.read_request_vif.mon_cb);
      if (cfg.en_scb && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
          cfg.m_axi_agent_cfg.read_request_vif.mon_cb.arvalid === 1'b1 &&
          cfg.m_axi_agent_cfg.read_request_vif.mon_cb.arready === 1'b1) begin
        bit [63:0] masked_araddr = cfg.m_axi_agent_cfg.read_request_vif.mon_cb.araddr &
                                   cfg.m_axi_agent_cfg.read_request_vif.araddr_mask;
        // Match only RAL single-beat reads to the exact STATUS register address so overlapping
        // raw AXI bursts or upper-address aliases whose araddr[5:0] == 6'h10 do not stamp an
        // unrelated RAL pre-read snapshot.
        if (masked_araddr == ral.status.get_address() &&
            cfg.m_axi_agent_cfg.read_request_vif.mon_cb.arlen == 8'd0) begin
          foreach (status_pre_read_q[i]) begin
            if (!status_pre_read_q[i].ar_stamped) begin
              status_pre_read_q[i].rx_pulses   = uart_vif.uart_rx_clk_pulses;
              status_pre_read_q[i].rx_idle_exp = (uart_vif.uart_rx_clk_pulses == 0) || !rx_enabled;
              status_pre_read_q[i].ar_stamped  = 1'b1;
              break;
            end
          end
        end
      end
    end
  endtask

  virtual task process_intr_cov();
    if (!cfg.en_cov) return;
    forever begin
      @(cfg.intr_vif.pins);
      if (!cfg.en_scb || cfg.under_reset || !cfg.clk_rst_vif.rst_n ||
          (intr_test_wr_in_flight > 0) || cfg.inject_scb_intr_corrupt) begin
        continue;
      end
      for (int i = 0; i < NumUartIntr; i++) begin
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
      if (cfg.en_scb && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
          nf_enabled && uart_nf_vif.cb.rx_enable && uart_nf_vif.cb.rxnf_enable) begin
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
        bit tx_corrupt = cfg.inject_scb_tx_corrupt || $test$plusargs("inject_corrupt_tx_byte");
        exp_item = tx_processing_item_q.pop_front();
        if (tx_enabled && tx_q.size > 0) begin
          tx_processing_item_q.push_back(tx_q.pop_front());
        end
        if (tx_corrupt) begin
          act_item.data ^= 8'hFF;
        end
        if (cfg.m_uart_agent_cfg.en_tx_checks) compare(act_item, exp_item, "TX");
        // after an expected item is sent, check to see if size dipped below watermark
        predict_tx_watermark_intr();
        if (cfg.en_cov && !tx_corrupt) begin
          cov.tx_fifo_level_cg.sample(tx_q.size(), 0);
          cov.baud_rate_w_core_clk_cg.sample(cfg.m_uart_agent_cfg.baud_rate, cfg.clk_freq_mhz);
        end
        if (tx_q.size() == 0 && tx_processing_item_q.size() == 0) begin
          intr_exp[TxDone] = 1;
        end
      end else begin
        if (cfg.en_scb_checks && cfg.m_uart_agent_cfg.en_tx_checks &&
            !slpbk_enabled && !llpbk_enabled && !ral.ovrd.txen.get_mirrored_value()) begin
          `uvm_error(`gfn, $sformatf("Received unexpected TX item from DUT (tx_enabled=%0b): %0s",
                                     tx_enabled, act_item.sprint()))
        end
      end
    end
  endtask

  virtual task process_uart_rx_fifo();
    uart_item item;
    forever begin
      uart_rx_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received uart rx item:\n%0s", item.sprint()), UVM_LOW)

      if (rx_enabled && !slpbk_enabled && !llpbk_enabled) begin
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
        if (cfg.disable_scb_rx_frame_check) begin
          rx_break_may_be_sticky = 1'b1;
        end else if (!item.stop_bit && item.data == 8'h00) begin
          if (!rx_break_wait) begin
            int break_bytes = get_break_bytes_by_level(ral.ctrl.rxblvl.get_mirrored_value());
            rx_break_allzero_cnt++;
            if (rx_break_allzero_cnt >= break_bytes) begin
              intr_exp[RxBreakErr] = 1'b1;
              rx_break_allzero_cnt = 0;
              rx_break_wait        = 1'b1;
            end
          end
        end else begin
          rx_break_allzero_cnt = 0;
          rx_break_wait        = 1'b0;
        end
        if (!parity_err && item.stop_bit == 1) begin // no parity/frame error
          if ((rx_q.size() + num_valid_rdata_exp()) < RxFifoDepth) begin
            rx_q.push_back(item);
            if (cfg.en_cov) cov.rx_fifo_level_cg.sample(rx_q.size() + num_valid_rdata_exp(), 0);
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
    if (cfg.en_cov && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
        (intr_test_wr_in_flight == 0) && !status_intr_test[TxWatermark] &&
        !cfg.inject_scb_intr_corrupt && (tx_q_size < watermark)) begin
      cov.tx_watermark_cg.sample(ral.fifo_ctrl.txilvl.get_mirrored_value());
    end
  endfunction

  virtual function void predict_rx_watermark_intr(int rx_q_size = -1);
    uint eff_rx_q_size = (rx_q_size < 0) ? (rx_q.size() + num_valid_rdata_exp()) : uint'(rx_q_size);
    uint watermark = get_rx_watermark_bytes_by_level(ral.fifo_ctrl.rxilvl.get_mirrored_value());
    intr_exp[RxWatermark] = (eff_rx_q_size >= watermark) || status_intr_test[RxWatermark];
    if (cfg.en_cov && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
        (intr_test_wr_in_flight == 0) && !status_intr_test[RxWatermark] &&
        !cfg.inject_scb_intr_corrupt && (eff_rx_q_size >= watermark)) begin
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

  // Natural hardware interrupt has occurred; sample relevant covergroup strictly when NOT
  // software-forced via INTR_TEST, NOT under self-test corruption injection, and operational
  // hardware preconditions are met.
  function void sample_detail_intr_cov(uart_intr_e intr);
    if (!cfg.en_cov || !cfg.en_scb || cfg.under_reset || !cfg.clk_rst_vif.rst_n ||
        (intr_test_wr_in_flight > 0) || cfg.inject_scb_intr_corrupt) begin
      return;
    end
    case (intr)
      TxWatermark: begin
        uint txilvl = ral.fifo_ctrl.txilvl.get_mirrored_value();
        if (!status_intr_test[TxWatermark] &&
            (slpbk_enabled || llpbk_enabled ||
             (tx_q.size() < get_tx_watermark_bytes_by_level(txilvl)))) begin
          cov.tx_watermark_cg.sample(txilvl);
        end
      end
      RxWatermark: begin
        uint rxilvl = ral.fifo_ctrl.rxilvl.get_mirrored_value();
        if (!status_intr_test[RxWatermark] &&
            (slpbk_enabled || llpbk_enabled ||
             ((rx_q.size() + num_valid_rdata_exp()) >= get_rx_watermark_bytes_by_level(rxilvl)))) begin
          cov.rx_watermark_cg.sample(rxilvl);
        end
      end
      RxBreakErr: begin
        if (!event_intr_test[RxBreakErr] && rx_enabled && !slpbk_enabled && !llpbk_enabled) begin
          cov.rx_break_err_cg.sample(ral.ctrl.rxblvl.get_mirrored_value());
        end
      end
      RxTimeout: begin
        if (!event_intr_test[RxTimeout] && rx_enabled && timeout_en_enabled) begin
          cov.rx_timeout_cg.sample(ral.timeout_ctrl.val.get_mirrored_value());
        end
      end
      RxParityErr: begin
        if (!event_intr_test[RxParityErr] && rx_enabled && parity_en_enabled) begin
          cov.rx_parity_err_cg.sample(ral.ctrl.parity_odd.get_mirrored_value());
        end
      end
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
    status_pre_read_q.delete();
    fstatus_pre_read_q.delete();
    intr_pre_read_q.delete();
    // reset local variables
    uart_tx_clk_pulses        = 0;
    uart_rx_clk_pulses        = 0;
    tx_csr_writes_in_flight   = 0;
    rx_csr_writes_in_flight   = 0;
    intr_csr_writes_in_flight = 0;
    active_pre_wr_map.delete();
    tx_wr_epoch               = 0;
    rx_wr_epoch               = 0;
    intr_wr_epoch             = 0;
    tx_enabled                = ral.ctrl.tx.get_reset();
    rx_enabled                = ral.ctrl.rx.get_reset();
    nf_enabled                = ral.ctrl.nf.get_reset();
    slpbk_enabled             = ral.ctrl.slpbk.get_reset();
    llpbk_enabled             = ral.ctrl.llpbk.get_reset();
    parity_en_enabled         = ral.ctrl.parity_en.get_reset();
    parity_odd_enabled        = ral.ctrl.parity_odd.get_reset();
    timeout_en_enabled        = ral.timeout_ctrl.en.get_reset();
    rx_timeout_may_be_sticky  = 1'b0;
    rx_break_may_be_sticky    = 1'b0;
    rx_break_allzero_cnt      = 0;
    rx_break_wait             = 1'b0;
    tx_full_exp               = ral.status.txfull.get_reset();
    rx_full_exp               = ral.status.rxfull.get_reset();
    tx_empty_exp              = ral.status.txempty.get_reset();
    rx_empty_exp              = ral.status.rxempty.get_reset();
    tx_idle_exp               = ral.status.txidle.get_reset();
    rx_idle_exp               = ral.status.rxidle.get_reset();
    txlvl_exp                 = ral.fifo_status.txlvl.get_reset();
    rxlvl_exp                 = ral.fifo_status.rxlvl.get_reset();
    last_rxlvl_act            = 0;
    intr_exp                   = ral.intr_state.get_reset();
    committed_status_intr_test = '0;
    committed_event_intr_test  = '0;
    status_intr_test           = '0;
    event_intr_test            = '0;
    intr_test_wr_in_flight     = 0;
    intr_test_pre_wr_q.delete();
    rdata_exp              = ral.rdata.get_reset();
    cfg.inject_scb_tx_corrupt          = 1'b0;
    cfg.inject_scb_rx_corrupt          = 1'b0;
    cfg.inject_scb_status_corrupt      = 1'b0;
    cfg.inject_scb_fifo_status_corrupt = 1'b0;
    cfg.inject_scb_intr_corrupt        = 1'b0;
    cfg.disable_scb_rx_parity_check = 1'b0;
    cfg.disable_scb_rx_frame_check  = 1'b0;
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
    `uvm_info(`gfn, $sformatf(
        "Scoreboard comparison summary: tx_compared=%0d, rx_compared=%0d, status_compared=%0d, fifo_status_compared=%0d, intr_compared=%0d",
        cfg.scb_tx_compared_cnt, cfg.scb_rx_compared_cnt, cfg.scb_status_compared_cnt,
        cfg.scb_fifo_status_compared_cnt, cfg.scb_intr_compared_cnt), UVM_LOW)
    if (!cfg.en_scb || !cfg.en_scb_checks || !cfg.m_uart_agent_cfg.en_tx_checks) begin
      uart_tx_fifo.flush();
      tx_q.delete();
      tx_processing_item_q.delete();
    end
    if (!cfg.en_scb || !cfg.en_scb_checks || !cfg.m_uart_agent_cfg.en_rx_checks) begin
      uart_rx_fifo.flush();
      rx_q.delete();
      rdata_exp_q.delete();
    end
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_tx_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_rx_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_processing_item_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, rx_q)
    `DV_CHECK_EQ(rdata_exp_q.size(), 0, "Expected rdata_exp_q to be empty at end of test")
  endfunction

endclass
