// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// event test vseq
// Verifies all 6 EVENT_ENABLE sources both via:
//   (1) Directed one-hot isolation (provoke -> verify intr_spi_event_o & INTR_STATE.SPI_EVENT ->
//       disable bit while active to prove masking -> re-enable & clear condition to prove deassertion),
//       including explicit below/equal/above watermark boundaries (Comments #9, #11, #23, #25), and
//   (2) Randomized multi-source EVENT_ENABLE combinations.
class spi_host_event_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_event_vseq)
  `uvm_object_new

  bit rx_drain;
  bit [7:0] rxqd;
  bit [7:0] txqd;
  spi_segment_item segment;
  spi_host_intr_state_t intr_state;
  int segms_size;
  int segms_words;
  spi_host_command_t command[$];
  spi_host_command_t command_snd;

  constraint spi_host_ctrl_reg_c {
    spi_host_ctrl_reg.tx_watermark inside {[2 : 4]};
    spi_host_ctrl_reg.rx_watermark inside {[2 : 4]};
  }

  constraint spi_config_regs_clkdiv_c {
    spi_config_regs.clkdiv inside {[2 : 3]};
  }

  constraint spi_host_command_reg_c {
    spi_host_command_reg.direction == Bidir;
    spi_host_command_reg.mode == Standard;
  }

  virtual task pre_start();
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    super.pre_start();
  endtask

  virtual task check_isolated_spi_event_pin(bit exp_asserted, string ctx);
    uvm_reg_data_t intr_st;
    cfg.clk_rst_vif.wait_clks(2);
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(SpiHostEvent), exp_asserted,
                 $sformatf("[%s] intr_spi_event_o mismatch", ctx))
    csr_rd(.ptr(ral.intr_state), .value(intr_st));
    `DV_CHECK_EQ(intr_st[SpiHostEvent], exp_asserted,
                 $sformatf("[%s] INTR_STATE.SPI_EVENT mismatch", ctx))
  endtask

  // Directed one-hot isolation pass across all 6 EVENT_ENABLE bits:
  //   bit 0: RXFULL, bit 1: TXEMPTY, bit 2: RXWM, bit 3: TXWM, bit 4: READY, bit 5: IDLE
  virtual task run_isolated_one_hot_event_and_wm_boundary_checks();
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         rdata;

    `uvm_info(`gfn, "Running directed one-hot EVENT_ENABLE isolation & watermark boundary checks", UVM_LOW)
    spi_host_init();
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.error_enable), .value(32'h0));
    csr_wr(.ptr(ral.intr_test),    .value(32'h0));
    csr_wr(.ptr(ral.intr_state),   .value(32'h3));
    csr_wr(.ptr(ral.intr_enable),  .value(1 << SpiHostEvent));

    // 1. One-hot TXEMPTY (bit 1 = 6'h02)
    csr_wr(.ptr(ral.control),      .value(32'h2000_027F)); // spien=0, output_en=1, tx_wm=2, rx_wm=0x7F
    csr_wr(.ptr(ral.event_enable), .value(32'h02));        // ONLY txempty enabled
    csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "TXEMPTY asserted (one-hot)");
    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while active
    check_isolated_spi_event_pin(1'b0, "TXEMPTY masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h02));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "TXEMPTY re-enabled");
    ral.txdata.write(status, 0, 32'h1111_2222);            // TXQD=1 -> TXEMPTY=0
    csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "TXEMPTY deasserted on TXQD=1");

    // 2. One-hot TXWM (bit 3 = 6'h08): below (TXQD=1 < 2), equal (TXQD=2 == 2), above (TXQD=3 > 2)
    csr_wr(.ptr(ral.event_enable), .value(32'h08));        // ONLY txwm enabled (tx_wm=2, TXQD=1)
    csr_rd_check(.ptr(ral.status.txwm), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "TXWM asserted below watermark (TXQD=1 < 2)");
    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while active
    check_isolated_spi_event_pin(1'b0, "TXWM masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h08));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "TXWM re-enabled");
    ral.txdata.write(status, 0, 32'h3333_4444);            // TXQD=2 == tx_wm -> TXWM=0
    csr_rd_check(.ptr(ral.status.txwm), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "TXWM deasserted at TXQD==TX_WATERMARK (2==2)");
    ral.txdata.write(status, 0, 32'h5555_6666);            // TXQD=3 > tx_wm -> TXWM=0
    csr_rd_check(.ptr(ral.status.txwm), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "TXWM stays 0 above watermark (TXQD=3 > 2)");

    // 3. One-hot READY (bit 4 = 6'h10): CMDQD=0..7 (READY=1) vs CMDQD=8 (READY=0)
    spi_host_init();
    csr_wr(.ptr(ral.intr_enable),  .value(1 << SpiHostEvent));
    csr_wr(.ptr(ral.control),      .value(32'h2000_007F)); // spien=0
    csr_wr(.ptr(ral.event_enable), .value(32'h10));        // ONLY ready enabled
    csr_rd_check(.ptr(ral.status.ready), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "READY asserted at CMDQD=0");
    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while READY=1
    check_isolated_spi_event_pin(1'b0, "READY masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h10));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "READY re-enabled");
    for (int k = 0; k < SPI_HOST_CMD_DEPTH; k++) begin
      cmd.direction = None;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
    end
    csr_rd_check(.ptr(ral.status.ready), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "READY deasserted at CMDQD=8");

    // 4. One-hot IDLE (bit 5 = 6'h20): idle (ACTIVE=0) -> active mid-transfer (ACTIVE=1) -> idle
    spi_host_init();
    csr_wr(.ptr(ral.intr_enable),  .value(1 << SpiHostEvent));
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0014)); // clkdiv=20 (~1350 clks for 4B Standard)
    csr_wr(.ptr(ral.control),      .value(32'hA000_007F)); // spien=1, output_en=1
    csr_wr(.ptr(ral.event_enable), .value(32'h20));        // ONLY idle enabled
    csr_rd_check(.ptr(ral.status.active), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b1, "IDLE asserted when quiescent");
    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while idle
    check_isolated_spi_event_pin(1'b0, "IDLE masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h20));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "IDLE re-enabled");

    ral.txdata.write(status, 0, 32'hA55A_3CC3);
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    program_command_reg(cmd);
    @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
    csr_rd_check(.ptr(ral.status.active), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b0, "IDLE deasserted while transfer ACTIVE=1");
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    check_isolated_spi_event_pin(1'b1, "IDLE re-asserted after transfer completes");

    // 5. One-hot RXWM (bit 2 = 6'h04): below (RXQD=1), equal (RXQD=2), above (RXQD=3), drain
    // NOTE (Pending Designer Confirmation - Comment #25):
    // RTL (spi_host_data_fifos.sv:129) implements rx_wm_o = (rx_qd_o >= rx_watermark_i), matching
    // CONTROL.RX_WATERMARK ("reaches"), whereas STATUS.RXWM and EVENT_ENABLE.RXWM RDL descriptions
    // say "exceeds"/"greater than". Explicit below/equal/above checks are retained against current
    // RTL >= pending designer/spec-owner confirmation and RDL reconciliation.
    csr_wr(.ptr(ral.configopts),   .value(32'h0000_0001)); // Fast clkdiv=1
    csr_wr(.ptr(ral.control),      .value(32'hA000_0002)); // rx_watermark = 2
    csr_wr(.ptr(ral.event_enable), .value(32'h04));        // ONLY rxwm enabled
    check_isolated_spi_event_pin(1'b0, "RXWM=0 at RXQD=0 (<2)");

    cmd.direction = RxOnly;
    cmd.mode      = Quad;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3; // 1 word -> RXQD=1 (below watermark 2)
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd1));
    csr_rd_check(.ptr(ral.status.rxwm), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "RXWM=0 below watermark (RXQD=1 < 2)");

    program_command_reg(cmd); // 2nd word -> RXQD=2 (equal to watermark 2)
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd2));
    csr_rd_check(.ptr(ral.status.rxwm), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "RXWM=1 at equality boundary (RXQD=2 == 2)");
    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while RXWM=1
    check_isolated_spi_event_pin(1'b0, "RXWM masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h04));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "RXWM re-enabled");

    program_command_reg(cmd); // 3rd word -> RXQD=3 (above watermark 2)
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd3));
    csr_rd_check(.ptr(ral.status.rxwm), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "RXWM=1 above watermark (RXQD=3 > 2)");

    ral.rxdata.read(status, 0, rdata);
    ral.rxdata.read(status, 0, rdata); // RXQD=1 < 2 -> RXWM deasserts
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd1));
    csr_rd_check(.ptr(ral.status.rxwm), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "RXWM deasserted after draining to RXQD=1");
    ral.rxdata.read(status, 0, rdata); // Drain final word -> RXQD=0

    // 6. One-hot RXFULL (bit 0 = 6'h01) using efficient 63-word + 1-word Quad fill (Comment #23)
    csr_wr(.ptr(ral.event_enable), .value(32'h01));        // ONLY rxfull enabled
    cmd.direction = RxOnly;
    cmd.mode      = Quad;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd251; // 252 bytes = 63 words in one burst -> RXQD=63
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd_check(.ptr(ral.status.rxqd),   .compare_value(8'd63));
    csr_rd_check(.ptr(ral.status.rxfull), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "RXFULL=0 at RXQD=63");

    cmd.len = 9'd3; // 4 bytes = 64th word -> RXQD=64 -> RXFULL=1
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd_check(.ptr(ral.status.rxqd),   .compare_value(8'd64));
    csr_rd_check(.ptr(ral.status.rxfull), .compare_value(1'b1));
    check_isolated_spi_event_pin(1'b1, "RXFULL=1 at RXQD=64");

    csr_wr(.ptr(ral.event_enable), .value(32'h00));        // Mask while RXFULL=1
    check_isolated_spi_event_pin(1'b0, "RXFULL masked (EVENT_ENABLE=0)");
    csr_wr(.ptr(ral.event_enable), .value(32'h01));        // Re-enable
    check_isolated_spi_event_pin(1'b1, "RXFULL re-enabled");

    ral.rxdata.read(status, 0, rdata); // Pop 1 word -> RXQD=63 -> RXFULL=0
    csr_rd_check(.ptr(ral.status.rxqd),   .compare_value(8'd63));
    csr_rd_check(.ptr(ral.status.rxfull), .compare_value(1'b0));
    check_isolated_spi_event_pin(1'b0, "RXFULL deasserted at RXQD=63");
    for (int w = 0; w < 63; w++) begin
      ral.rxdata.read(status, 0, rdata);
    end
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd0));
  endtask

  virtual task body();
    // 1. Directed one-hot isolated EVENT_ENABLE & watermark boundary verification (Comments #9, #11, #25)
    run_isolated_one_hot_event_and_wm_boundary_checks();

    // 2. Randomized multi-source EVENT_ENABLE combinations
    command.delete();
    segms_size = 0;
    segms_words = 0;
    spi_host_txn_sent = 1;
    rx_poll_min_delay_ns = 0;
    rx_poll_max_delay_ns = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;

    spi_host_init();
    wait_ready_for_command();
    program_spi_host_regs();
    check_event(ral.status.ready, 1, 1);

    while (segms_words < spi_host_ctrl_reg.tx_watermark) begin
      gen_trans();
    end
    check_event(ral.status.txwm, 0, 0);
    for (int i = 0; i < command.size(); i++) begin
      command_snd = command[i];
      snd_cmd(command_snd);
      if (i == 0) check_event(ral.status.active, 1, 1);
      csr_rd(.ptr(ral.status.txqd), .value(txqd));
      `DV_CHECK_EQ(txqd, spi_host_ctrl_reg.tx_watermark - i)
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(0));
      csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      if (txqd == (spi_host_ctrl_reg.tx_watermark - 1)) begin
        check_event(ral.status.txwm, 1, 1);
      end else if (txqd < (spi_host_ctrl_reg.tx_watermark - 1)) begin
        check_event(ral.status.txwm, 0, 1);
      end
      read_rx_fifo();
    end
    check_event(ral.status.txempty, 1, 1);

    cfg.clk_rst_vif.wait_clks(20);

    begin
      spi_host_command_t bulk_cmd;
      for (int i = 0; i < spi_host_ctrl_reg.rx_watermark; i++) begin
        check_event(ral.status.rxwm, 0, 0);
        spi_send_trans(1);
        csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
        csr_spinwait(.ptr(ral.status.rxqd), .exp_data(i + 1));
        csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      end
      check_event(ral.status.rxwm, 1, 1);
      if (spi_host_ctrl_reg.rx_watermark < SPI_HOST_RX_DEPTH) begin
        spi_send_trans(1);
        csr_spinwait(.ptr(ral.status.txqd), .exp_data(0));
        csr_spinwait(.ptr(ral.status.rxqd), .exp_data(spi_host_ctrl_reg.rx_watermark + 1));
        csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      end
      check_event(ral.status.rxwm, 0, 1);
      if (spi_host_ctrl_reg.rx_watermark > 0) read_rx_fifo();

      // Efficient multi-word RX fill (63 words + 1 word) instead of 64 single-word polled loops (Comment #23)
      check_event(ral.status.rxfull, 0, 0);
      wait_ready_for_command();
      bulk_cmd.direction = RxOnly;
      bulk_cmd.mode      = Quad;
      bulk_cmd.csaat     = 1'b0;
      bulk_cmd.len       = 9'd251; // 63 words
      program_command_reg(bulk_cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      csr_spinwait(.ptr(ral.status.rxqd),   .exp_data(8'd63));
      check_event(ral.status.rxfull, 0, 0);

      bulk_cmd.len = 9'd3; // 64th word
      program_command_reg(bulk_cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(0));
      csr_spinwait(.ptr(ral.status.rxqd),   .exp_data(SPI_HOST_RX_DEPTH));
      check_event(ral.status.rxfull, 1, 1);
      read_rx_fifo();
    end
  endtask : body

  virtual task gen_trans();
    generate_transaction();
    while (transaction.segments.size() > 0) begin
      segment = transaction.segments.pop_back();
      if (segment.command_reg.direction != RxOnly) begin
        segms_size = segment.spi_data.size() + segms_size;
        segms_words = segms_size / 4;
        access_data_fifo(segment.spi_data, TxFifo);
      end
      command.push_back(segment.command_reg);
    end
  endtask

  virtual task snd_cmd(spi_host_command_t command_snd);
    wait_ready_for_command();
    program_command_reg(command_snd);
    wait_ready_for_command();
  endtask

  virtual task spi_send_trans(int num_transactions, bit wait_ready = 1'b1);
    for (int n = 0; n < num_transactions; n++) begin
      generate_transaction();
      send_trans(transaction, wait_ready);
      if (wait_ready) wait_ready_for_command();
    end
    spi_host_txn_sent = 1;
  endtask

  virtual task generate_transaction();
    transaction_init();
    transaction.read_weight = 0;
    transaction.write_weight = 100;
    transaction.tx_only_weight = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction, num_segments == 1; cmd == WriteStd;)
    foreach (transaction.segments[i]) begin
      transaction.segments[i].command_reg.direction = Bidir;
      transaction.segments[i].command_reg.len = 3;
      transaction.segments[i].spi_data = '{8'h55, 8'haa, 8'h55, 8'haa};
    end
  endtask
endclass : spi_host_event_vseq
