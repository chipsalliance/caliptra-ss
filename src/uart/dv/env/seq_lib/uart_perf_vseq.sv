// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// performance test with 0 delay to access fifo, less delay to access interrupts
class uart_perf_vseq extends uart_fifo_full_vseq;
  `uvm_object_utils(uart_perf_vseq)

  `uvm_object_new

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo == 0;
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

  constraint dly_to_rx_read_c {
    dly_to_rx_read == 0;
  }

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 5,
      [1      :100]       :/ 4,
      [101    :10_000]    :/ 1
    };
  }

  // don't use the slowest baud rate, otherwise, it may take over 1hr
  constraint baud_rate_extra_c {
    baud_rate >= BaudRate115200;
  }

  virtual task body();
    // Run back-to-back mixed Read/Write bursts for sub2tlul FSM transition coverage
    `uvm_info(`gfn, "Running back-to-back mixed AXI Read/Write bursts for FSM transition coverage", UVM_LOW)
    for (int i = 0; i < 30; i++) begin
      uvm_reg_data_t rdata;
      // Read (Get) immediately followed by Write (Put)
      csr_rd(.ptr(ral.status), .value(rdata));
      csr_wr(.ptr(ral.intr_state), .value(rdata));
      // Write (Put) immediately followed by Read (Get)
      csr_wr(.ptr(ral.intr_state), .value(9'h1FF));
      csr_rd(.ptr(ral.status), .value(rdata));
    end

    // Run parent body (back-to-back performance traffic)
    super.body();
  endtask : body

endclass : uart_perf_vseq
