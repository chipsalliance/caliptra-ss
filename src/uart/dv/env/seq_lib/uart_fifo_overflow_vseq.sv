// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_overflow_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_fifo_overflow_vseq)

  bit rx_overflow_seen;
  int total_rx_overflow_seen;

  `uvm_object_new

  constraint num_rx_bytes_c {
    num_rx_bytes inside {[RxFifoDepth + 4 : RxFifoDepth + 12]};
  }

  constraint weight_to_skip_rx_read_c {
    weight_to_skip_rx_read == 10000;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  virtual task pre_start();
    super.pre_start();
    cfg.m_uart_agent_cfg.en_tx_checks = 0;
    total_rx_overflow_seen = 0;
  endtask

  virtual task uart_init();
    rx_overflow_seen = 0;
    super.uart_init();
  endtask

  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_status;
    csr_rd(.ptr(ral.intr_state), .value(intr_status));
    if (intr_status[RxOverflow]) begin
      rx_overflow_seen = 1;
      total_rx_overflow_seen++;
    end
    super.process_interrupts();
  endtask

  virtual task process_remaining_data();
    fork
      begin // TX
        wait_for_all_tx_bytes();
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end
      begin // RX
        bit [TL_DW-1:0] intr_status;
        cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
        csr_rd(.ptr(ral.intr_state), .value(intr_status));
        if (intr_status[RxOverflow]) begin
          rx_overflow_seen = 1;
          total_rx_overflow_seen++;
        end
        read_all_rx_bytes();
      end
    join
  endtask : process_remaining_data

  virtual task post_start();
    if (this.get_type_name() == "uart_fifo_overflow_vseq") begin
      `DV_CHECK_GT(total_rx_overflow_seen, 0, "Verify RX FIFO overflow occurred and was detected")
      `uvm_info(`gfn, $sformatf("Total RX overflow events verified: %0d", total_rx_overflow_seen), UVM_LOW)
    end
    super.post_start();
  endtask

  // don't wait for fifo not full
  virtual task wait_for_tx_fifo_not_full();
  endtask : wait_for_tx_fifo_not_full

  // don't wait for fifo not full
  virtual task wait_for_rx_fifo_not_full();
  endtask : wait_for_rx_fifo_not_full

endclass : uart_fifo_overflow_vseq
