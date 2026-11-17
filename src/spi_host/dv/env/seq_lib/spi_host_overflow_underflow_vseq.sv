// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies RX FIFO underflow and TX FIFO overflow (packer-inclusive depth 73) across both:
//   (1) Isolated one-hot enabled vs selectively masked ERROR_ENABLE discipline (Comment #11), and
//   (2) Randomized ERROR_ENABLE settings, followed by checked Bidir recovery.
class spi_host_overflow_underflow_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_overflow_underflow_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int txfifo_ptr = 0;
  int segms_size;
  int segms_words;
  spi_host_command_t command[$];

  virtual task pre_start();
    super.pre_start();
  endtask

  virtual task run_isolated_overflow_underflow_enable_mask_checks();
    bit [7:0]    read_q[$];
    uvm_status_e status;

    `uvm_info(`gfn, "Running isolated enabled vs masked UNDERFLOW and OVERFLOW checks", UVM_LOW)
    spi_host_init();
    csr_wr(.ptr(ral.control),     .value(32'h2000_007F)); // spien=0, output_en=1
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0003));
    csr_wr(.ptr(ral.intr_state),  .value(32'h0000_0003));

    // 1a. One-hot UNDERFLOW enabled (ERROR_ENABLE = 32'h04)
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_0004));
    access_data_fifo(read_q, RxFifo, 1'b0);
    begin
      bit [31:0] empty_rx_word = {<<8{read_q}};
      `DV_CHECK_EQ(empty_rx_word, 32'h0, "Empty RXDATA read must return 0x0")
    end
    check_error(ral.error_status.underflow, 1);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b1,
                 "intr_error_o must assert on one-hot enabled UNDERFLOW")
    csr_wr(.ptr(ral.error_status.underflow), .value(1'b1));
    csr_wr(.ptr(ral.intr_state),             .value(32'h3));
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0,
                 "intr_error_o must deassert after W1C clear of UNDERFLOW")

    // 1b. Selectively masked UNDERFLOW (ERROR_ENABLE = 32'h1B: all other errors enabled, underflow[2]=0)
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_001B));
    access_data_fifo(read_q, RxFifo, 1'b0);
    check_error(ral.error_status.underflow, 1);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0,
                 "intr_error_o must remain 0 when ERROR_ENABLE.UNDERFLOW==0")
    csr_rd_check(.ptr(ral.intr_state.error), .compare_value(1'b0));
    csr_wr(.ptr(ral.error_status.underflow), .value(1'b1));

    // 2a. One-hot OVERFLOW enabled (ERROR_ENABLE = 32'h02) at packer-inclusive depth 73 -> 74th write
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_0002));
    for (int w = 0; w < SPI_HOST_TX_DEPTH + 1; w++) begin
      ral.txdata.write(status, 0, 32'h2000_0000 + w);
    end
    csr_rd_check(.ptr(ral.status.txqd),   .compare_value(8'd73));
    csr_rd_check(.ptr(ral.status.txfull), .compare_value(1'b1));
    check_error(ral.error_status.overflow, 0);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0)

    ral.txdata.write(status, 0, 32'hDEAD_0FEF); // 74th word triggers overflow
    check_error(ral.error_status.overflow, 1);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b1,
                 "intr_error_o must assert on one-hot enabled OVERFLOW")
    csr_wr(.ptr(ral.error_status.overflow), .value(1'b1));
    csr_wr(.ptr(ral.intr_state),            .value(32'h3));
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0)

    // 2b. Selectively masked OVERFLOW (ERROR_ENABLE = 32'h1D: all other errors enabled, overflow[1]=0)
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_001D));
    ral.txdata.write(status, 0, 32'hBEEF_0FEF); // TX FIFO still at 73 words (TXFULL=1)
    check_error(ral.error_status.overflow, 1);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0,
                 "intr_error_o must remain 0 when ERROR_ENABLE.OVERFLOW==0")
    csr_rd_check(.ptr(ral.intr_state.error), .compare_value(1'b0));
    csr_wr(.ptr(ral.error_status.overflow), .value(1'b1));
    spi_host_init();
  endtask

  virtual task body();
    bit [7:0] read_q[$];
    bit [7:0] txqd;
    spi_host_intr_state_t intr_state;

    // 1. Isolated one-hot enabled & masked UNDERFLOW / OVERFLOW verification (Comment #11)
    run_isolated_overflow_underflow_enable_mask_checks();

    // 2. Randomized ERROR_ENABLE sequence + active traffic + post-error Bidir recovery
    command.delete();
    segms_size = 0;
    segms_words = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;

    fork
      begin : isolation_fork
        fork
          start_agent_reactive_seqs();
        join_none
        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .spinwait_delay_ns(100));
          csr_spinwait(.ptr(ral.status.rxqd), .exp_data(8'h0), .spinwait_delay_ns(100));
          cfg.clk_rst_vif.wait_clks(100);
        end
        disable fork;
      end
      begin
        read_rx_fifo();
      end
    join

    access_data_fifo(read_q, RxFifo, 1'b0); // attempting empty read error underflow
    check_error(ral.error_status.underflow, 1);
    csr_wr(.ptr(ral.error_status.underflow), .value(1'b1)); // W1C clear underflow
    csr_wr(.ptr(ral.intr_state), .value(32'h3));

    csr_wr(.ptr(ral.configopts.clkdiv), .value(16'h28)); // clk div set to 40

    while (segms_words <= (SPI_HOST_TX_DEPTH + 1)) begin
      check_error(ral.error_status.overflow, 0);
      gen_trans();
    end
    check_error(ral.error_status.overflow, 1);
    csr_wr(.ptr(ral.error_status.overflow), .value(1'b1)); // W1C clear overflow

    // Drain overflowed TX FIFO via SW reset, clear any latched error/interrupt status,
    // and verify end-to-end recovery via a scoreboard-checked Bidir transfer.
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3f));
    csr_wr(.ptr(ral.intr_state),   .value(32'h3));
    program_spi_host_regs();
    begin
      uvm_status_e status;
      uvm_reg_data_t rdata;
      spi_host_command_t cmd;
      int unsigned prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      int unsigned prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
      write_txdata(32'h5AA5_C33C, 4'hf, status);
      wait_ready_for_command();
      cmd.direction = Bidir;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(status, 0, rdata);
      cfg.clk_rst_vif.wait_clks(10);
      if (cfg.en_scb) begin
        `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                     "Expected scoreboard TX check on post-overflow recovery transfer")
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     "Expected scoreboard RX check on post-overflow recovery transfer")
      end
    end
  endtask : body

  virtual task gen_trans();
    generate_transaction();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        segms_size = segment.spi_data.size() + segms_size;
        segms_words = segms_size / 4;
        access_data_fifo(segment.spi_data, TxFifo, 0);
      end
      command.push_back(segment.command_reg);
    end
  endtask

  virtual task generate_transaction();
    transaction_init();
    transaction.tx_only_weight = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction, num_segments == 1; cmd == ReadStd;)
  endtask

endclass : spi_host_overflow_underflow_vseq
