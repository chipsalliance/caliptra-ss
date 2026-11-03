// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error_cmd test vseq
// test tries to capture error interrupt when cmd invalid condition appears
// cmd invalid is created when cmd sent and host isn't ready
class spi_host_error_cmd_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_error_cmd_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int cmdq_depth = 0;

  virtual task body();
    program_spi_host_regs();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));

    // Enable error interrupts in error_enable
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 1. Test CSID Invalid error (csidinval)
    csr_wr(.ptr(ral.csid), .value(SPI_HOST_NUM_CS));
    begin
      spi_host_command_t cmd;
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
    end
    check_error(ral.error_status.csidinval, 1);
    csr_wr(.ptr(ral.error_status.csidinval), .value(1'b1)); // W1C
    csr_wr(.ptr(ral.csid), .value(0)); // Restore valid CSID

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 2. Test Command Invalid error (cmdinval) - Dual/Quad with Bidir is invalid
    begin
      spi_host_command_t cmd;
      cmd.direction = Bidir;
      cmd.mode      = Dual;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
    end
    check_error(ral.error_status.cmdinval, 1);
    csr_wr(.ptr(ral.error_status.cmdinval), .value(1'b1)); // W1C

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 3. Test Command Queue Busy error (cmdbusy)
    cmdq_depth = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    while (cmdq_depth < SPI_HOST_CMD_DEPTH) begin
      check_error(ral.error_status.cmdbusy, 0);
      send_cmd();
    end
    send_cmd();
    check_error(ral.error_status.cmdbusy, 1);
    csr_wr(.ptr(ral.error_status.cmdbusy), .value(1'b1)); // W1C

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 4. Test Access Invalid error (accessinval) across all 8 invalid byte-enable masks on TXDATA
    begin
      uvm_status_e status;
      bit [3:0] invalid_masks[8] = '{
        4'b0000, 4'b0101, 4'b0111, 4'b1001, 4'b1010, 4'b1011, 4'b1101, 4'b1110
      };
      foreach (invalid_masks[i]) begin
        write_txdata(32'hDEADBEEF, invalid_masks[i], status);
        check_error(ral.error_status.accessinval, 1);
        // Verify rejected write was not enqueued in the TX FIFO
        csr_rd_check(.ptr(ral.status.txqd), .compare_value(8'h0));
        csr_wr(.ptr(ral.error_status.accessinval), .value(1'b1)); // W1C
        check_error(ral.error_status.accessinval, 0);
      end
    end

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));

    // 5. Test errors with error_enable = 0 to cover ere=0 bins in error_status_cg
    csr_wr(.ptr(ral.error_enable), .value(32'h0));

    // 5a. CSID invalid with error_enable = 0
    csr_wr(.ptr(ral.csid), .value(SPI_HOST_NUM_CS));
    begin
      spi_host_command_t cmd;
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
    end
    check_error(ral.error_status.csidinval, 1);
    csr_wr(.ptr(ral.error_status.csidinval), .value(1'b1)); // W1C
    csr_wr(.ptr(ral.csid), .value(0));

    // 5b. Command invalid with error_enable = 0 (Dual/Quad Bidir)
    begin
      spi_host_command_t cmd;
      cmd.direction = Bidir;
      cmd.mode      = Dual;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
    end
    check_error(ral.error_status.cmdinval, 1);
    csr_wr(.ptr(ral.error_status.cmdinval), .value(1'b1)); // W1C

    // Also send Quad + Bidir with csaat=1 and csaat=0 to complete speedXdirectionXcsaat_cp
    begin
      spi_host_command_t cmd;
      cmd.direction = Bidir;
      cmd.mode      = Quad;
      cmd.csaat     = 1'b1;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      cmd.csaat     = 1'b0;
      program_command_reg(cmd);
    end
    check_error(ral.error_status.cmdinval, 1);
    csr_wr(.ptr(ral.error_status.cmdinval), .value(1'b1)); // W1C

    // 5c. Cmdbusy with error_enable = 0
    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    csr_wr(.ptr(ral.error_enable), .value(32'h0));
    cmdq_depth = 0;
    while (cmdq_depth < SPI_HOST_CMD_DEPTH) begin
      send_cmd();
    end
    send_cmd();
    check_error(ral.error_status.cmdbusy, 1);
    csr_wr(.ptr(ral.error_status.cmdbusy), .value(1'b1)); // W1C

    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3f));
    csr_wr(.ptr(ral.intr_state),   .value(32'h3));
    program_spi_host_regs();

    // 6. Post-error recovery: execute a scoreboard-checked Bidir transfer
    begin
      uvm_status_e status;
      uvm_reg_data_t rdata;
      spi_host_command_t cmd;
      int unsigned prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      int unsigned prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
      write_txdata(32'hA55A_3CC3, 4'hf, status);
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
                     "Expected scoreboard TX check on post-error recovery transfer")
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     "Expected scoreboard RX check on post-error recovery transfer")
      end
    end
  endtask : body

  virtual task send_cmd();
    generate_transaction();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        access_data_fifo(segment.spi_data, TxFifo);
      end
    end
    program_command_reg(segment.command_reg);
    cmdq_depth++;
  endtask

  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,num_segments == 1;cmd == ReadStd;)
  endtask

endclass : spi_host_error_cmd_vseq
