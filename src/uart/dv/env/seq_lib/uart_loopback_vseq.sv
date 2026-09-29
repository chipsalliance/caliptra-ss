// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test 2 kinds of loopback
// 1. system loopback, any outgoing bits to TX are received through RX
// 2. Line loopback, incoming bits (on RX) are forwarded to TX
class uart_loopback_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_loopback_vseq)

  int total_sys_loopback_runs;
  int total_line_loopback_runs;

  constraint en_tx_c {
    en_tx == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    total_sys_loopback_runs = 0;
    total_line_loopback_runs = 0;
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();

      randcase
        1: drive_system_loopback();
        1: drive_line_loopback();
      endcase
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

  virtual task drive_system_loopback();
    byte unsigned tx_byte;
    bit [TL_DW-1:0] status_val;
    `uvm_info(`gfn, "Start system loopback", UVM_HIGH)
    total_sys_loopback_runs++;

    ral.ctrl.slpbk.set(1);
    csr_update(ral.ctrl);

    `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_tx_trans)
    cfg.clk_rst_vif.wait_clks(dly_to_next_tx_trans);

    // drive tx data and expect to receive it in rx fifo
    send_tx_byte(tx_byte);
    // wait for loopback to complete: wait until RX FIFO has data (rxempty == 0) and TX & RX are idle
    // Verify that during system loopback, external UART TX pin remains isolated (tied to 1'b1 idle)
    do begin
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, 1'b1,
                     "System loopback must keep external UART TX pin at 1'b1 (idle)")
      end
    end while (status_val[5] == 1'b1 || status_val[3] == 1'b0 || status_val[4] == 1'b0);

    cfg.clk_rst_vif.wait_clks(2);
    csr_rd_check(.ptr(ral.rdata), .compare_value(tx_byte));
    // clear TxDone interrupt
    csr_wr(.ptr(ral.intr_state), .value(1 << TxDone));
    // check status is default value
    csr_rd_check(.ptr(ral.status), .compare_value(ral.status.get_reset()));

    ral.ctrl.slpbk.set(0);
    csr_update(ral.ctrl);
  endtask

  // when line loopback is enabled, RX data will be wired to TX w/o any synchronizer
  // drive RX with random data and random delay, and check same value at TX
  virtual task drive_line_loopback();
    `uvm_info(`gfn, "Start line loopback", UVM_HIGH)
    total_line_loopback_runs++;

    ral.ctrl.llpbk.set(1);
    csr_update(ral.ctrl);

    // disable monitor, as it can't handle these random data
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    fork
      begin // isolation_fork
        fork
          // drive RX with random data and random delay
          repeat ($urandom_range(100, 1000)) begin
            cfg.m_uart_agent_cfg.vif.uart_rx = $urandom_range(0, 1);
            `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dly_to_next_rx_trans,
                                                  dly_to_next_rx_trans > 0;)
            #(dly_to_next_rx_trans * 1ns);
          end
          // RX has same value as TX without any synchronizer in the data path
          forever begin
            @(cfg.m_uart_agent_cfg.vif.uart_tx || cfg.m_uart_agent_cfg.vif.uart_rx);
            #1ps; // avoid race condition
            if (!cfg.under_reset) begin
              `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, cfg.m_uart_agent_cfg.vif.uart_rx)
            end
          end
        join_any
        disable fork;
      end // isolation_fork
    join

    cfg.m_uart_agent_cfg.vif.uart_rx = 1; // back to default value
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;

    // CDC sync on RX input adds propagation delay, so wait some cycles to ensure the internal RX
    // value is 1 before disabling line loopback. Otherwise, unexpected value (0) may be propagated
    // to RX datapath and be falsely interpreted as the beginning of a START bit.
    cfg.clk_rst_vif.wait_clks(2);
    // If noise filter is on, need an additional cycle of delay.
    if (en_noise_filter) cfg.clk_rst_vif.wait_clks(1);

    ral.ctrl.llpbk.set(0);
    ral.fifo_ctrl.rxrst.set(1);
    csr_update(ral.ctrl);
    csr_update(ral.fifo_ctrl);
  endtask

  virtual task post_start();
    if (this.get_type_name() == "uart_loopback_vseq") begin
      `DV_CHECK_GT(total_sys_loopback_runs + total_line_loopback_runs, 0,
                   "Verify loopback transfers occurred")
      `uvm_info(`gfn, $sformatf("Verified loopback: %0d system loopback runs (TX pin isolation checked), %0d line loopback runs",
                                total_sys_loopback_runs, total_line_loopback_runs), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_loopback_vseq
