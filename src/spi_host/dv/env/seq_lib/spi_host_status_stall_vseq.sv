// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Force the DUT to stall on both a rx and a tx transaction.
// This occurs when the RXFIFO and TXFIFO are full/empty respectively, and we
// try to continue a transaction.
// First create read transactions, without emptying the fifo, until we see rxfull
// and rxstall.
// Then, create a write transaction without adding data to the txfifo, and check
// for txempty and txstall.
class spi_host_status_stall_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_status_stall_vseq)
  `uvm_object_new

  bit [7:0] rxqd;
  spi_host_command_t command_q[$];
  spi_segment_item segment_q[$];

  constraint spi_config_regs_latency_c {
    spi_config_regs.clkdiv inside {[0 : 1]};
    spi_config_regs.csnlead inside {[0 : 2]};
    spi_config_regs.csntrail inside {[0 : 2]};
    spi_config_regs.csnidle inside {[0 : 2]};
  }

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
  endtask : pre_start

  virtual task body();
    spi_segment_item segment_snd;
    segment_snd = spi_segment_item::type_id::create("segment_snd");

    fork
      start_agent_reactive_seqs();
    join_none

    program_spi_host_regs();
    wait_ready_for_command();

    // 1. Test RX stall: issue a Read command that exceeds RX FIFO (64) + packer (1) capacity (66 words > 65)
    `uvm_info(`gfn, "Step 1: Programming read command to trigger RX stall", UVM_LOW)
    segment_snd.command_reg.direction = RxOnly;
    segment_snd.command_reg.mode = Standard;
    segment_snd.command_reg.csaat = 0;
    segment_snd.command_reg.len = (SPI_HOST_RX_DEPTH + 2) * 4 - 1;
    program_command_reg(segment_snd.command_reg);

    // Wait for DUT to assert rxfull and rxstall
    `uvm_info(`gfn, "Step 1a: Waiting for rxfull", UVM_LOW)
    csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b1));
    `uvm_info(`gfn, "Step 1b: Waiting for rxstall", UVM_LOW)
    csr_spinwait(.ptr(ral.status.rxstall), .exp_data(1'b1));

    // Drain RX FIFO to allow the read transaction to finish
    `uvm_info(`gfn, "Step 1c: Draining RX FIFO", UVM_LOW)
    while (1) begin
      spi_host_status_t status;
      csr_rd(.ptr(ral.status), .value(status));
      if (status.rx_qd > 0) begin
        for (int i = 0; i < status.rx_qd; i++) begin
          access_data_fifo(segment_snd.spi_data, RxFifo, 0);
        end
      end
      if (status.rxempty && (status.rx_qd == 0) && !status.active) break;
      #100ns;
    end

    // 2. Test TX stall: issue a Write command without adding data to TX FIFO
    `uvm_info(`gfn, "Step 2: Programming write command to trigger TX stall", UVM_LOW)
    cfg.tx_stall_check = 1'b1;
    segment_snd.command_reg.direction = TxOnly;
    segment_snd.command_reg.mode = Standard;
    segment_snd.command_reg.csaat = 0;
    segment_snd.command_reg.len = 3;
    segment_snd.spi_data = '{8'h11, 8'h22, 8'h33, 8'h44};

    wait_ready_for_command();
    program_command_reg(segment_snd.command_reg);

    // Wait until DUT asserts txstall
    `uvm_info(`gfn, "Step 2a: Waiting for txstall", UVM_LOW)
    csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b1));

    // Now write data into TX FIFO to allow command to complete
    `uvm_info(`gfn, "Step 2b: Supplying data to TX FIFO", UVM_LOW)
    access_data_fifo(segment_snd.spi_data, TxFifo, 0);
    csr_spinwait(.ptr(ral.status.cmdqd), .exp_data(0));
    csr_spinwait(.ptr(ral.status.active), .exp_data(0));
    cfg.tx_stall_check = 1'b0;

    // 3. Verify final status: not stalled and inactive
    `uvm_info(`gfn, "Step 3: Checking final status (active=0, rxstall=0, txstall=0)", UVM_LOW)
    csr_spinwait(.ptr(ral.status.rxstall), .exp_data(1'b0));
    csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b0));
    // 4. Fill TX FIFO to depth to sample txfull=1 and tx_qd=full
    `uvm_info(`gfn, "Step 4: Filling TX FIFO to capacity to hit txfull and tx_qd full", UVM_LOW)
    for (int i = 0; i < SPI_HOST_TX_DEPTH + 2; i++) begin
      uvm_status_e status_wr;
      spi_host_status_t st;
      ral.txdata.write(status_wr, 0, 32'hA5A5A5A5);
      csr_rd(.ptr(ral.status), .value(st));
    end
    apply_reset("HARD");
    spi_host_init();

    `uvm_info(`gfn, "Finished 'spi_host_status_stall_vseq' successfully", UVM_LOW)
  endtask : body

  // Drive all segments of the read transaction. Return when we run out of
  // segments, or the RXQD indicates we are full.
  // Drive segments of the read transaction until full/stalled or segments exhaust.
  virtual task rd_trans(spi_transaction_item trans, bit wait_ready = 1'b1);
    spi_segment_item segment;
    spi_host_status_t status;

    while (trans.segments.size() > 0) begin
      csr_rd(.ptr(ral.status), .value(status), .backdoor(1));
      if (status.rxstall || status.rxfull || status.rx_qd >= SPI_HOST_RX_DEPTH) begin
        rxqd = SPI_HOST_RX_DEPTH;
        break;
      end
      if (wait_ready && !status.ready) begin
        csr_spinwait(.ptr(ral.status.ready), .exp_data(1'b1));
      end
      spi_host_atomic.get(1); begin : locked_fifo_access
        segment = trans.segments.pop_back();
        if (segment.command_reg.direction != RxOnly) begin
          access_data_fifo(segment.spi_data, TxFifo);
        end
        program_command_reg(segment.command_reg);
      end spi_host_atomic.put(1);

      csr_rd(.ptr(ral.status.rxqd), .value(rxqd), .backdoor(1));
      if (rxqd >= SPI_HOST_RX_DEPTH) break;
    end
  endtask : rd_trans

  // Randomize the transaction item to allow us to create stalls.
  virtual task generate_stall_transaction(bit readonly = 1'b1);
    transaction_init();
    if (readonly) begin
      transaction.tx_only_weight = 0;
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         cmd == ReadStd;)
    end else begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
         cmd == WriteStd;)
    end
  endtask : generate_stall_transaction

endclass : spi_host_status_stall_vseq
