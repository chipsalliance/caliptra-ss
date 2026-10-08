// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_reset_vseq extends uart_fifo_overflow_vseq;
  `uvm_object_utils(uart_fifo_reset_vseq)

  static bit rx_drain_init        = 1'b0;
  static int next_rx_drain_target = 0;

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      [0:1]    :/ 1,
      [2:63]   :/ 1,
      [64:100] :/ 10
    };
  }

  `uvm_object_new

  virtual task process_remaining_data();
    bit do_clear_tx_fifo;
    bit do_clear_rx_fifo;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(do_clear_tx_fifo,
                                       do_clear_tx_fifo dist {0 :/ 1, 1 :/ 4};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(do_clear_rx_fifo,
                                       do_clear_rx_fifo dist {0 :/ 1, 1 :/ 4};)

    // When clearing the RX FIFO, drain the RX FIFO to a per-seed offset target level (0..RxFifoDepth)
    // via real RDATA reads after RX is idle so rxrst exercises all RX FIFO levels (0..64) operationally.
    if (do_clear_rx_fifo && !cfg.under_reset) begin
      bit [TL_DW-1:0] fifo_status, rdata;
      int             rxlvl;
      int             target_lvl;
      if (!rx_drain_init) begin
        next_rx_drain_target = $urandom_range(0, RxFifoDepth);
        rx_drain_init        = 1'b1;
      end
      target_lvl = next_rx_drain_target % (RxFifoDepth + 1);
      cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
      csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
      rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
      if (rxlvl >= target_lvl) begin
        next_rx_drain_target++;
        while (rxlvl > target_lvl && !cfg.under_reset) begin
          wait_ignored_period_and_read_rdata(rdata);
          rxlvl--;
        end
      end
    end

    fork
      begin
        bit [TL_DW-1:0] status_val;
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
        cfg.clk_rst_vif.wait_clks(dly_to_access_fifo);
        // can't predict if the item is clear or not, when reset fifo at almost done period
        wait_when_in_ignored_period(.tx(do_clear_tx_fifo), .rx(do_clear_rx_fifo));
        clear_fifos(.clear_tx_fifo(do_clear_tx_fifo), .clear_rx_fifo(do_clear_rx_fifo));
        if (do_clear_tx_fifo && !cfg.under_reset) begin
          csr_rd(.ptr(ral.fifo_status), .value(status_val));
          if (!cfg.under_reset) begin
            `DV_CHECK_EQ(get_field_val(ral.fifo_status.txlvl, status_val), 0,
                         "TX FIFO level must be 0 after txrst");
          end
        end
        if (do_clear_rx_fifo && !cfg.under_reset) begin
          csr_rd(.ptr(ral.fifo_status), .value(status_val));
          if (!cfg.under_reset) begin
            `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, status_val), 0,
                         "RX FIFO level must be 0 after rxrst");
          end
        end
      end
      begin
        if (!do_clear_tx_fifo) begin
          wait_for_all_tx_bytes();
        end else begin
          spinwait_txidle();
        end
      end
      begin
        if (!do_clear_rx_fifo) begin
          read_all_rx_bytes();
        end else begin
          spinwait_rxidle();
        end
      end
    join

    dut_shutdown();
  endtask : process_remaining_data

endclass : uart_fifo_reset_vseq
