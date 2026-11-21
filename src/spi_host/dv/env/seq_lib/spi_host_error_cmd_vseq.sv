// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// error_cmd test vseq
// Verifies CSIDINVAL, CMDINVAL (both Dual/Quad+Bidir and reserved SPEED=2'b11 RsvdSpd across all
// directions), CMDBUSY, and ACCESSINVAL across enabled and masked ERROR_ENABLE settings, plus
// pin quiescence and post-error recovery (Comments #3, #7, #8, #9).
class spi_host_error_cmd_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_error_cmd_vseq)
  `uvm_object_new

  spi_segment_item segment;
  int cmdq_depth = 0;

  virtual task body();
    spi_dir_e all_dirs[4] = '{None, RxOnly, TxOnly, Bidir};

    program_spi_host_regs();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));

    // Enable error interrupts in error_enable
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 1. Test CSID Invalid error (csidinval) with ERROR_ENABLE.CSIDINVAL = 1
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
    csr_wr(.ptr(ral.error_status), .value(32'h0000_0010)); // One-hot W1C csidinval
    csr_wr(.ptr(ral.csid), .value(0)); // Restore valid CSID

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // 2. Test Command Invalid error (cmdinval) - Dual and Quad with Bidir
    begin
      spi_host_command_t cmd;
      cmd.direction = Bidir;
      cmd.mode      = Dual;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      check_error(ral.error_status.cmdinval, 1);
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008)); // One-hot W1C cmdinval

      spi_host_init();
      csr_wr(.ptr(ral.control.spien), .value(1'b0));
      csr_wr(.ptr(ral.error_enable),  .value(32'h1F));

      cmd.direction = Bidir;
      cmd.mode      = Quad;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      check_error(ral.error_status.cmdinval, 1);
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008)); // One-hot W1C cmdinval
    end

    // 2b. Directed Reserved SPEED = 2'b11 (RsvdSpd) rejection, non-execution on pins while
    //     CONTROL.SPIEN == 1, interrupt assertion, and clean recovery across all 4 directions
    //     (Comments #7, #8, #9).
    foreach (all_dirs[d_i]) begin
      uvm_status_e       st;
      spi_host_command_t cmd;
      spi_host_init();
      program_control_reg(); // spien=1, output_en=1
      csr_wr(.ptr(ral.csid),         .value(32'h0));
      csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
      csr_wr(.ptr(ral.error_enable), .value(32'h0000_0008)); // One-hot CMDINVAL enabled
      csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0003));
      csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0003));

      if (all_dirs[d_i] inside {TxOnly, Bidir}) begin
        write_txdata(32'hCAFE_BEEF, 4'hf, st);
      end
      cmd.direction = all_dirs[d_i];
      cmd.mode      = RsvdSpd; // Reserved SPEED = 2'b11
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);

      // Wait several core clocks with SPIEN=1 and verify pins stayed completely quiescent
      cfg.clk_rst_vif.wait_clks(12);
      `DV_CHECK_EQ(cfg.m_spi_agent_cfg.vif.csb, {SPI_HOST_NUM_CS{1'b1}},
                   $sformatf("CSB must remain inactive high on RsvdSpd (%s)", all_dirs[d_i].name()))
      `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, 1'b0,
                   $sformatf("SCK must remain idle on RsvdSpd (%s)", all_dirs[d_i].name()))
      `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'h0,
                   $sformatf("SD_EN must remain disabled on RsvdSpd (%s)", all_dirs[d_i].name()))
      csr_rd_check(.ptr(ral.status.active), .compare_value(1'b0));
      check_error(ral.error_status.cmdinval, 1);

      // Flush halted u_cmd_queue via SW_RST before clearing ERROR_STATUS so RsvdSpd descriptor is drained
      program_spi_host_sw_reset();
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008));
      csr_wr(.ptr(ral.intr_state),   .value(32'h3));
      check_error(ral.error_status.cmdinval, 0);
    end

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
    csr_wr(.ptr(ral.error_status), .value(32'h0000_0001)); // One-hot W1C cmdbusy

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
        csr_wr(.ptr(ral.error_status), .value(32'h0000_0020)); // One-hot W1C accessinval
        check_error(ral.error_status.accessinval, 0);
      end
    end

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));

    // 5. Test masked error reporting and confirmed core-halt policy (Comment #3 — Confirmed Option A,
    //    Harry Callahan, Nov 12, 2026):
    //    ERROR_ENABLE gates `intr_error_o` interrupt generation ONLY; `enb_error = |sw_error_status`
    //    (spi_host.sv:409,487-495) unconditionally halts u_spi_core regardless of ERROR_ENABLE until
    //    ERROR_STATUS is cleared.
    //    5.0: Active SPIEN=1 comparison on maskable UNDERFLOW across ERROR_ENABLE.UNDERFLOW = 1 vs 0,
    //         observing queued-command halt while sticky and W1C-only recovery without SW_RST.
    for (int en_i = 1; en_i >= 0; en_i--) begin
      uvm_status_e       st;
      uvm_reg_data_t     rdata;
      spi_host_command_t halt_cmd;
      int unsigned       prev_tx_cnt, prev_rx_cnt;

      spi_host_init();
      csr_wr(.ptr(ral.csid),         .value(32'h0));
      csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
      csr_wr(.ptr(ral.control),      .value(32'hA000_007F)); // SPIEN=1, OUTPUT_EN=1
      // en_i=1: all errors enabled (32'h1F); en_i=0: UNDERFLOW[2] masked while others enabled (32'h1B)
      csr_wr(.ptr(ral.error_enable), .value(en_i ? 32'h0000_001F : 32'h0000_001B));
      csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0003));
      csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0003));

      prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;

      // Trigger maskable UNDERFLOW with SPIEN=1 by reading empty RXDATA
      ral.rxdata.read(st, 0, rdata);
      `DV_CHECK_EQ(rdata, 32'h0, "Empty RXDATA read must return 0x0")
      check_error(ral.error_status.underflow, 1);
      `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), bit'(en_i),
                   $sformatf("intr_error_o mismatch for ERROR_ENABLE.UNDERFLOW=%0d", en_i))

      // Submit a valid following Bidir command while sticky ERROR_STATUS.UNDERFLOW == 1 and SPIEN == 1:
      // both en_i=1 and en_i=0 MUST keep u_spi_core halted (CSB inactive high, CMDQD=1, ACTIVE=0).
      write_txdata(32'hC33C_5AA0 ^ en_i, 4'hf, st);
      `DV_CHECK_EQ(st, UVM_IS_OK)
      halt_cmd.direction = Bidir;
      halt_cmd.mode      = Standard;
      halt_cmd.csaat     = 1'b0;
      halt_cmd.len       = 9'd3;
      program_command_reg(halt_cmd);

      cfg.clk_rst_vif.wait_clks(20);
      `DV_CHECK_EQ(cfg.m_spi_agent_cfg.vif.csb, {SPI_HOST_NUM_CS{1'b1}},
                   $sformatf("Following command must stay halted on CSB while UNDERFLOW sticky (en=%0d)", en_i))
      csr_rd_check(.ptr(ral.status.cmdqd),  .compare_value(4'd1));
      csr_rd_check(.ptr(ral.status.active), .compare_value(1'b0));

      // Clear UNDERFLOW via W1C ONLY (no SW_RST) -> queued Bidir command must immediately unhalt & complete
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0004));
      csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0003));
      csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(st, 0, rdata);
      cfg.clk_rst_vif.wait_clks(10);
      if (cfg.en_scb) begin
        `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                     $sformatf("Expected W1C-only unhalt TX check (ERROR_ENABLE.UNDERFLOW=%0d)", en_i))
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     $sformatf("Expected W1C-only unhalt RX check (ERROR_ENABLE.UNDERFLOW=%0d)", en_i))
      end
    end

    spi_host_init();
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
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
    csr_wr(.ptr(ral.error_status), .value(32'h0000_0010)); // One-hot W1C csidinval
    csr_wr(.ptr(ral.csid), .value(0));

    // 5b. Command invalid with error_enable = 0 (Dual+Bidir, Quad+Bidir, and RsvdSpd)
    begin
      spi_host_command_t cmd;
      cmd.direction = Bidir;
      cmd.mode      = Dual;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      check_error(ral.error_status.cmdinval, 1);
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008)); // One-hot W1C cmdinval

      cmd.direction = Bidir;
      cmd.mode      = Quad;
      cmd.csaat     = 1'b1;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      cmd.csaat     = 1'b0;
      program_command_reg(cmd);
      check_error(ral.error_status.cmdinval, 1);
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008)); // One-hot W1C cmdinval

      // Masked RsvdSpd (ERROR_ENABLE.CMDINVAL == 0 while other error enables == 1: 32'h17)
      spi_host_init();
      program_control_reg();
      csr_wr(.ptr(ral.error_enable), .value(32'h17)); // All enabled EXCEPT cmdinval[3]=0
      csr_wr(.ptr(ral.intr_enable),  .value(32'h3));
      csr_wr(.ptr(ral.intr_state),   .value(32'h3));
      cmd.direction = TxOnly;
      cmd.mode      = RsvdSpd;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      cfg.clk_rst_vif.wait_clks(8);
      `DV_CHECK_EQ(cfg.m_spi_agent_cfg.vif.csb, {SPI_HOST_NUM_CS{1'b1}},
                   "CSB must remain inactive on masked RsvdSpd command")
      check_error(ral.error_status.cmdinval, 1);
      `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostError), 1'b0,
                   "intr_error_o must stay 0 when ERROR_ENABLE.CMDINVAL==0")
      program_spi_host_sw_reset();
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0008));
    end

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
    csr_wr(.ptr(ral.error_status), .value(32'h0000_0001)); // One-hot W1C cmdbusy

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
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction, num_segments == 1; cmd == ReadStd;)
  endtask

endclass : spi_host_error_cmd_vseq
