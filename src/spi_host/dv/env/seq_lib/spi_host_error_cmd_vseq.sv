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
    cfg.en_scb = 0;
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

    // 4. Test Access Invalid error (accessinval)
    begin
      uvm_status_e status;
      void'(uvm_hdl_force("tb.dut.access_valid", 1'b0));
      ral.txdata.write(status, 0, 32'hDEADBEEF);
      void'(uvm_hdl_release("tb.dut.access_valid"));
    end
    check_error(ral.error_status.accessinval, 1);
    csr_wr(.ptr(ral.error_status.accessinval), .value(1'b1)); // W1C

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
