// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_tx_rx_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_tx_rx_vseq)

  rand uint num_tx_bytes;
  rand uint num_rx_bytes;
  rand uint dly_to_next_rx_trans;
  rand uint dly_to_next_tx_trans;
  rand uint dly_to_access_intr;
  rand bit  wait_for_rx_idle;
  rand bit  wait_for_tx_idle;
  rand uint weight_to_skip_rx_read;
  rand uint dly_to_rx_read;

  // Derived sequences that explicitly observe/clear RxParityErr can set this to avoid W1C races
  // with process_interrupts().
  bit skip_rx_parity_err_clear = 1'b0;


  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint dly_to_next_rx_trans_c {
    dly_to_next_rx_trans dist {
      0           :/ 5,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_next_tx_trans_c {
    dly_to_next_tx_trans dist {
      0           :/ 5,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 1,
      [1      :100]       :/ 5,
      [101    :10_000]    :/ 3,
      [10_001 :1_000_000] :/ 1
    };
  }

  constraint wait_for_rx_idle_c {
    wait_for_rx_idle dist {
      1       :/ 1,
      0       :/ 10
    };
  }

  constraint wait_for_tx_idle_c {
    wait_for_tx_idle dist {
      1       :/ 1,
      0       :/ 10
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 7: skip
    weight_to_skip_rx_read == 7;
  }

  constraint dly_to_rx_read_c {
    dly_to_rx_read dist {0           :/ 1,
                         [1:100]     :/ 1,
                         [100:10000] :/ 2};
  }

  bit stop_intr_thread;

  `uvm_object_new


  task pre_start();
    super.pre_start();
    num_trans.rand_mode(0);
    // dly to send a_valid is controlled in uart vseq level. Don't add additional delay in tl
    // driver as it may make tl happens at ignore period
    // cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
    // cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
  endtask

  task body();
    stop_intr_thread = 1'b0;
    fork
      begin
        while (do_interrupt && !stop_intr_thread) process_interrupts();
      end
      begin
        bit seen_active_tx = 1'b0;
        bit seen_active_rx = 1'b0;
        // repeat test sequencing upto 50 times
        for (int i = 1; i <= num_trans; i++) begin
          if (cfg.stop_transaction_generators()) break;
          // start each new run by randomizing dut parameters
          `DV_CHECK_RANDOMIZE_FATAL(this)
          if (en_tx) seen_active_tx = 1'b1;
          if (en_rx) seen_active_rx = 1'b1;
          if (this.get_type_name() == "uart_tx_rx_vseq" && i == num_trans) begin
            if (!seen_active_tx) en_tx = 1'b1;
            if (!seen_active_rx) en_rx = 1'b1;
          end

          uart_init();

          `uvm_info(`gfn, $sformatf("starting run %0d/%0d", i, num_trans), UVM_MEDIUM)
          fork
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d tx bytes", num_tx_bytes), UVM_MEDIUM)
              process_tx();
              `uvm_info(`gfn, $sformatf("done sending %0d tx bytes", num_tx_bytes), UVM_HIGH)
            end
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d rx bytes", num_rx_bytes), UVM_MEDIUM)
              process_rx();
              `uvm_info(`gfn, $sformatf("done sending %0d rx bytes", num_rx_bytes), UVM_HIGH)
            end
          join

          process_remaining_data();
          `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
        end
        stop_intr_thread = 1'b1; // to end thread process_interrupts gracefully while keeping do_interrupt for post_start
      end
    join

    if (this.get_type_name() == "uart_tx_rx_vseq" && do_apply_reset &&
        !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      verify_tx_ctrl_and_nco_corners();
    end
  endtask : body

  // Deterministically verify TX FIFO buffering while CTRL.TX == 0 (drain on re-enable) and
  // CTRL.NCO == 0 baud-tick gating with CTRL.TX == 1.
  virtual task verify_tx_ctrl_and_nco_corners();
    bit [TL_DW-1:0] st_val, fst_val, ctrl_save;
    byte            queued_bytes[4] = '{8'h11, 8'h22, 8'h33, 8'h44};

    // Drain/clear any stale bytes queued while CTRL.TX == 0 in the final random run before
    // enabling TX in uart_init().
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

    // 1. TX FIFO buffering while CTRL.TX == 0 & clean drain on re-enable
    ctrl_save = ral.ctrl.get_mirrored_value();
    csr_wr(.ptr(ral.ctrl), .value(ctrl_save & ~32'h1));
    foreach (queued_bytes[idx]) begin
      send_tx_byte(queued_bytes[idx]);
    end
    cfg.clk_rst_vif.wait_clks(2);
    `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, 1'b1,
                 "uart_tx pin must remain idle (1) while CTRL.TX == 0")
    `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx_clk_pulses, 0,
                 "No TX frame may start while CTRL.TX == 0")
    csr_rd(.ptr(ral.status), .value(st_val));
    `DV_CHECK_EQ(get_field_val(ral.status.txempty, st_val), 1'b0,
                 "txempty must be 0 with 4 queued bytes")
    `DV_CHECK_EQ(get_field_val(ral.status.txidle, st_val), 1'b0,
                 "txidle must be 0 when TX FIFO is non-empty")
    csr_rd(.ptr(ral.fifo_status), .value(fst_val));
    `DV_CHECK_EQ(get_field_val(ral.fifo_status.txlvl, fst_val), 4,
                 "txlvl must equal 4 before CTRL.TX is re-enabled")
    csr_wr(.ptr(ral.ctrl), .value(ctrl_save));
    cfg.clk_rst_vif.wait_clks(2);
    spinwait_txidle();
    csr_rd(.ptr(ral.status), .value(st_val));
    `DV_CHECK_EQ(get_field_val(ral.status.txempty, st_val), 1'b1,
                 "txempty must be 1 after draining 4 queued bytes")
    csr_rd(.ptr(ral.fifo_status), .value(fst_val));
    `DV_CHECK_EQ(get_field_val(ral.fifo_status.txlvl, fst_val), 0,
                 "txlvl must be 0 after draining 4 queued bytes")

    // 2. CTRL.NCO == 0 with CTRL.TX == 1 -> no baud ticks generated until NCO is restored
    ctrl_save = ral.ctrl.get_mirrored_value();
    ral.ctrl.nco.set(16'h0000);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()));
    void'(ral.ctrl.predict(ral.ctrl.get()));
    send_tx_byte(8'h3C);
    cfg.clk_rst_vif.wait_clks(100);
    `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, 1'b1,
                 "uart_tx must stay idle (1) while CTRL.NCO == 0")
    csr_rd(.ptr(ral.status), .value(st_val));
    `DV_CHECK_EQ(get_field_val(ral.status.txidle, st_val), 1'b0,
                 "txidle must be 0 when byte is loaded into uart_tx with CTRL.NCO == 0")
    ral.ctrl.set(ctrl_save);
    csr_wr(.ptr(ral.ctrl), .value(ctrl_save));
    void'(ral.ctrl.predict(ctrl_save));
    spinwait_txidle();
    dut_shutdown();
  endtask : verify_tx_ctrl_and_nco_corners

  task post_start();
    bit [TL_DW-1:0] intr_status;
    // dut_shutdown is must for each iteration, it's called in body
    do_dut_shutdown = 0;
    // need to clear fifo when tx is disabled as data isn't sent out
    if (ral.ctrl.tx.get_mirrored_value() == 0) begin
      clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(0));
      // wait for 1 cycle to allow tx_empty occur and be cleared later at super.post_start()
      cfg.clk_rst_vif.wait_clks(1);
    end
    if (!cfg.under_reset && do_interrupt) begin
      check_interrupts(intr_status);
    end
    super.post_start();
  endtask

  // read interrupts and randomly clear interrupts if set
  task process_interrupts();
    bit [TL_DW-1:0] intr_status, clear_intr;
    bit clear_rx_intr, clear_tx_intr;

    // avoid zero delay loop during reset, but exit immediately if main loop finishes
    wait (!cfg.under_reset || stop_intr_thread);
    if (stop_intr_thread) return;

    // read and check interrupt state and output pins
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    fork : wait_intr_rd_dly begin
      fork
        cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
        wait (stop_intr_thread || cfg.under_reset);
      join_any
      disable fork;
    end join
    if (stop_intr_thread || cfg.under_reset) return;
    check_interrupts(intr_status);
    if (stop_intr_thread || cfg.under_reset) return;

    // clear interrupt, randomly clear the interrupt that is set, and
    // don't clear the interrupt which isn't set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clear_intr,
                                       foreach (clear_intr[i]) {
                                           clear_intr[i] -> intr_status[i] == 1;
                                       }
                                       if (skip_rx_parity_err_clear) {
                                           clear_intr[RxParityErr] == 1'b0;
                                       })
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    fork : wait_intr_clr_dly begin
      fork
        cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
        wait (stop_intr_thread || cfg.under_reset);
      join_any
      disable fork;
    end join
    if (stop_intr_thread || cfg.under_reset) return;

    // for fifo interrupt, parity/frame error, don't clear it at ignored period
    // as it hasn't been checked
    clear_tx_intr = clear_intr[TxWatermark] | clear_intr[TxEmpty] | clear_intr[TxDone];
    clear_rx_intr = clear_intr[RxWatermark] | clear_intr[RxOverflow] | clear_intr[RxFrameErr] |
                    clear_intr[RxParityErr];
    wait_when_in_ignored_period(clear_tx_intr, clear_rx_intr);
    wait_if_stop_transaction_generators();
    if (!stop_intr_thread && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      csr_wr(.ptr(ral.intr_state), .value(clear_intr));
    end
  endtask

  virtual task process_tx();
    for (int j = 1; j <= num_tx_bytes; j++) begin
      byte tx_byte;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_tx_trans)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wait_for_tx_idle)

      cfg.clk_rst_vif.wait_clks(dly_to_next_tx_trans);
      wait_for_tx_fifo_not_full();
      wait_when_in_ignored_period(.tx(1));
      `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
      send_tx_byte(tx_byte);
      if (wait_for_tx_idle) spinwait_txidle();
    end
  endtask : process_tx

  // control RX data from both sides independently
  //   1. uart device
  //   2. register
  virtual task process_rx();
    bit send_rx_done = 0;
    fork
      begin // drive from uart RX interface
        for (int j = 1; j <= num_rx_bytes; j++) begin
          byte rx_byte;
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_rx_trans)
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wait_for_rx_idle)
          `DV_CHECK_STD_RANDOMIZE_FATAL(rx_byte)

          cfg.clk_rst_vif.wait_clks(dly_to_next_rx_trans);
          wait_for_rx_fifo_not_full();
          if (j == 1 && ral.ctrl.rx.get_mirrored_value() &&
              !ral.ctrl.slpbk.get_mirrored_value() && !ral.ctrl.llpbk.get_mirrored_value()) begin
            fork
              send_rx_byte(rx_byte);
              begin
                bit [TL_DW-1:0] mid_status_val, mid_fstatus_val;
                wait (cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == 5 || cfg.under_reset);
                if (!cfg.under_reset) begin
                  csr_rd(.ptr(ral.status), .value(mid_status_val));
                  csr_rd(.ptr(ral.fifo_status), .value(mid_fstatus_val));
                end
              end
            join
          end else begin
            send_rx_byte(rx_byte);
          end
          if (wait_for_rx_idle) spinwait_rxidle();
        end
        send_rx_done = 1; // to end reading RX thread
      end
      begin // read RX data through register
        while (!send_rx_done && !cfg.under_reset) begin
          // csr read is much faster than uart transfer, use bigger delay
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_rx_read)
          cfg.clk_rst_vif.wait_clks(dly_to_rx_read);
          wait_if_stop_transaction_generators();
          rand_read_rx_byte(weight_to_skip_rx_read);
        end
      end
    join
  endtask : process_rx

  virtual task process_remaining_data();

    fork
      begin // TX
        wait_for_all_tx_bytes();
        // tx fifo is empty but still need to wait for last tx item to be flushed out
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(tx_bytes_sent_cnt, num_tx_bytes,
                       "Full TX transfer byte length check (including partial words)")
          if (ral.ctrl.tx.get_mirrored_value() && cfg.m_uart_agent_cfg.en_tx_checks &&
              !ral.ctrl.slpbk.get_mirrored_value() && !ral.ctrl.llpbk.get_mirrored_value() &&
              (num_tx_bytes > 0)) begin
            `DV_CHECK_GT(cfg.scb_tx_compared_cnt, 0,
                         "Scoreboard TX byte comparisons must be exercised during active TX transfer")
          end
        end
      end
      begin // RX
        // wait for last rx item to be completed before read all of them
        cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
        read_all_rx_bytes();
        if (!cfg.under_reset && ral.ctrl.rx.get_mirrored_value() &&
            cfg.m_uart_agent_cfg.en_rx_checks && (num_rx_bytes <= RxFifoDepth)) begin
          `DV_CHECK_EQ(rx_bytes_read_cnt, rx_bytes_pushed_cnt,
                       "Full RX transfer byte length check (including partial words)")
          if (rx_bytes_pushed_cnt > 0 && !ral.ctrl.slpbk.get_mirrored_value() &&
              !ral.ctrl.llpbk.get_mirrored_value()) begin
            `DV_CHECK_GT(cfg.scb_rx_compared_cnt, 0,
                         "Scoreboard RX byte comparisons must be exercised during active RX transfer")
          end
        end
      end
    join

  endtask : process_remaining_data

endclass : uart_tx_rx_vseq
