// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_full_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_fifo_full_vseq)

  int total_tx_full_seen;
  int total_rx_full_seen;

  constraint num_trans_c {
    num_trans inside {[5:10]};
  }

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      [0:1]    :/ 2,
      [2:32]   :/ 2,
      [33:100] :/ 2
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      [0:1]    :/ 2,
      [2:32]   :/ 2,
      [33:100] :/ 2
    };
  }

  constraint dly_to_next_rx_trans_c {
    dly_to_next_rx_trans dist {
      0           :/ RxFifoDepth - 2,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_next_tx_trans_c {
    dly_to_next_tx_trans dist {
      0           :/ TxFifoDepth - 2,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint wait_for_rx_idle_c {
    // ratio of wait/not_wait depends upon RxFifoDepth to ensure we're very likely to get a run
    // of transactions to fill the FIFO
    wait_for_rx_idle dist {
      1       :/ 1,
      0       :/ RxFifoDepth + 10
    };
  }

  constraint wait_for_tx_idle_c {
    // ratio of wait/not_wait depends upon TxFifoDepth to ensure we're very likely to get a run
    // of transactions to fill the FIFO
    wait_for_tx_idle dist {
      1       :/ 1,
      0       :/ TxFifoDepth + 10
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 50: skip
    weight_to_skip_rx_read == 50;
  }

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    total_tx_full_seen = 0;
    total_rx_full_seen = 0;
  endtask

  virtual task wait_for_tx_fifo_not_full();
    bit [TL_DW-1:0] status_val;
    bit [TL_DW-1:0] fifo_status_val;
    csr_rd(.ptr(ral.status), .value(status_val));
    if (status_val[0] == 1'b1) begin
      total_tx_full_seen++;
      csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
      if (!cfg.under_reset) begin
        int txlvl = get_field_val(ral.fifo_status.txlvl, fifo_status_val);
        if (txlvl != TxFifoDepth) begin
          // In high-baud/low-delay scenarios (e.g. uart_perf), a byte may pop from the FIFO
          // into the transmitter during the AXI read of fifo_status.
          // Re-reading status should confirm txfull is no longer 1 and txlvl is TxFifoDepth - 1.
          bit [TL_DW-1:0] status_val2;
          csr_rd(.ptr(ral.status), .value(status_val2));
          `DV_CHECK_EQ(txlvl, TxFifoDepth - 1, "If status was full and drained, txlvl must be TxFifoDepth-1")
          `DV_CHECK_EQ(status_val2[0], 1'b0, "When drained, status.txfull must have cleared to 0")
        end else begin
          `DV_CHECK_EQ(txlvl, TxFifoDepth, "When status.txfull is 1, txlvl must equal TxFifoDepth")
        end
      end
    end
    super.wait_for_tx_fifo_not_full();
  endtask

  virtual task wait_for_rx_fifo_not_full();
    bit [TL_DW-1:0] status_val;
    bit [TL_DW-1:0] fifo_status_val;
    csr_rd(.ptr(ral.status), .value(status_val));
    if (status_val[1] == 1'b1) begin
      total_rx_full_seen++;
      csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
      if (!cfg.under_reset) begin
        int rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status_val);
        if (rxlvl != RxFifoDepth) begin
          // In concurrent RX read scenarios, a byte may be read from the FIFO
          // during the AXI read of fifo_status.
          // Re-reading status should confirm rxfull is no longer 1 and rxlvl is RxFifoDepth - 1.
          bit [TL_DW-1:0] status_val2;
          csr_rd(.ptr(ral.status), .value(status_val2));
          `DV_CHECK_EQ(rxlvl, RxFifoDepth - 1, "If status was full and drained, rxlvl must be RxFifoDepth-1")
          `DV_CHECK_EQ(status_val2[1], 1'b0, "When drained, status.rxfull must have cleared to 0")
        end else begin
          `DV_CHECK_EQ(rxlvl, RxFifoDepth, "When status.rxfull is 1, rxlvl must equal RxFifoDepth")
        end
      end
    end
    super.wait_for_rx_fifo_not_full();
  endtask

  virtual task post_start();
    if (this.get_type_name() == "uart_fifo_full_vseq") begin
      `uvm_info(`gfn, $sformatf("Verified FIFO full checks: total_tx_full_seen=%0d, total_rx_full_seen=%0d",
                                total_tx_full_seen, total_rx_full_seen), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_fifo_full_vseq
