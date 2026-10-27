// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Dual Chip Select (CS0 & CS1) verification sequence (SPI_HOST_NUM_CS = 2)
class spi_host_dual_cs_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_dual_cs_vseq)
  `uvm_object_new

  rand bit [31:0] wr_data_cs0[FIFO_DEPTH];
  rand bit [31:0] wr_data_cs1[FIFO_DEPTH];

  virtual task body();
    uvm_status_e status;
    bit [31:0] err_val;

    `uvm_info(`gfn, "Starting 'spi_host_dual_cs_vseq' (SPI_HOST_NUM_CS = 2)", UVM_LOW)

    // Set baseline configuration parameters
    spi_config_regs.cpol = 1'b0;
    spi_config_regs.cpha = 1'b0;
    spi_config_regs.clkdiv = 16'd2;
    spi_config_regs.csnlead = 4'd1;
    spi_config_regs.csntrail = 4'd1;
    spi_config_regs.csnidle = 4'd1;
    spi_config_regs.fullcyc = 1'b0;

    spi_host_ctrl_reg.tx_watermark = 0;
    spi_host_ctrl_reg.rx_watermark = 0;
    spi_host_ctrl_reg.csid = 0;
    spi_host_ctrl_reg.sw_rst = 0;

    apply_reset("HARD");
    spi_host_init();
    program_spi_host_regs();

    // 1. Exercise all fields of CONFIGOPTS_0 (CS0), CONFIGOPTS_1 (CS1), and CSID for coverage
    csr_wr(.ptr(ral.configopts),   .value(32'hEFFF_FFFF));
    csr_wr(.ptr(ral.configopts_1), .value(32'hEFFF_FFFF));
    csr_wr(.ptr(ral.configopts),   .value(32'h0000_0000));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0000_0000));
    csr_wr(.ptr(ral.csid),         .value(32'hFFFF_FFFF));
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0000));

    // 2. Configure independent timing options for CS0 (CONFIGOPTS_0) and CS1 (CONFIGOPTS_1)
    // CS0: clkdiv=2, csnlead=1, csntrail=1, csnidle=1, fullcyc=0, cpha=0, cpol=0
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    // CS1: clkdiv=3, csnlead=2, csntrail=2, csnidle=2, fullcyc=0, cpha=0, cpol=0
    csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0003));

    // Randomize target page address (same address on both Flash 0 and Flash 1 to prove CS isolation)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
      flash_addr < 32'h080000;
      flash_addr[7:0] == 8'h00;
    )
    `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data_cs0)
    `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data_cs1)

    // Ensure CS0 and CS1 payloads are distinct
    wr_data_cs0[0] = 32'hCAFE_0000;
    wr_data_cs1[0] = 32'hBEEF_1111;

    // 3. Program and verify Flash 0 via CSID = 0 (CONFIGOPTS_0)
    foreach (wr_data[i]) wr_data[i] = wr_data_cs0[i];
    run_flash_page_program_and_read(2'd0);

    // 4. Program and verify Flash 1 via CSID = 1 (CONFIGOPTS_1) at the SAME flash_addr
    foreach (wr_data[i]) wr_data[i] = wr_data_cs1[i];
    run_flash_page_program_and_read(2'd1);

    // 4b. Re-read Flash 0 (CSID = 0) at the SAME flash_addr to verify CS1 write did not corrupt CS0
    foreach (wr_data[i]) wr_data[i] = wr_data_cs0[i];
    run_flash_read_and_check(2'd0);

    // 5. Test CSAAT=1 active CSID switch (CS0 <-> CS1) from IdleCSBActive and pipelined CPHA=0/1
    // Covers spi_host_fsm.sv lines 214, 221, 223 (command_i.csid != csid_q -> WaitTrail)
    run_csaat_cs_switch_stimulus();

    // 6. Test out-of-range CSID >= SPI_HOST_NUM_CS (CSID = 2) -> csidinval error assertion
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_001F));
    csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0003));
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0002));
    begin
      spi_host_command_t inval_cmd;
      inval_cmd.direction = TxOnly;
      inval_cmd.mode      = Standard;
      inval_cmd.csaat     = 1'b0;
      inval_cmd.len       = 9'd0;
      program_command_reg(inval_cmd); // Properly encodes Direction=TxOnly (bits [13:12]=2'b10 => 32'h0000_2000)
    end

    // Verify error_status.csidinval (bit 4) is set
    csr_rd(.ptr(ral.error_status), .value(err_val));
    `DV_CHECK_EQ(err_val[4], 1'b1, "Expected csidinval error_status[4] == 1 when CSID = 2")

    // Flush queued command via SW reset, clear csidinval error, and verify post-error recovery on CS1
    program_spi_host_sw_reset();
    csr_wr(.ptr(ral.error_status), .value(32'h0000_003F));
    csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0003));
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0001));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0003));
    begin
      spi_host_command_t rec_cmd;
      uvm_reg_data_t rdata;
      int unsigned prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      int unsigned prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
      write_txdata(32'hA55A_C33C, 4'hf, status);
      wait_ready_for_command();
      rec_cmd.direction = Bidir;
      rec_cmd.mode      = Standard;
      rec_cmd.csaat     = 1'b0;
      rec_cmd.len       = 9'd3;
      program_command_reg(rec_cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(status, 0, rdata);
      cfg.clk_rst_vif.wait_clks(10);
      if (cfg.en_scb) begin
        `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                     "Expected scoreboard TX check on post-csidinval CS1 recovery transfer")
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     "Expected scoreboard RX check on post-csidinval CS1 recovery transfer")
      end
    end
    csr_wr(.ptr(ral.csid), .value(32'h0000_0000));

    `uvm_info(`gfn, "Finished 'spi_host_dual_cs_vseq' successfully", UVM_LOW)
  endtask : body

  // Exercises CSID switching while CSAAT=1 (both from parked IdleCSBActive and pipelined in-flight)
  virtual task run_csaat_cs_switch_stimulus();
    uvm_status_e status;
    spi_host_command_t cmd;

    `uvm_info(`gfn, "Running CSAAT=1 CSID switch stimulus (IdleCSBActive -> WaitTrail -> CSBSwitch)", UVM_LOW)

    // 5a. Parked IdleCSBActive switch: CS0 (csaat=1) -> wait IdleCSBActive -> CS1 (csaat=0)
    csr_wr(.ptr(ral.csid), .value(32'h0000_0000));
    ral.txdata.write(status, 0, 32'hA5A5_0001);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b1;
    cmd.len       = 9'd3; // 4 bytes
    program_command_reg(cmd);

    if (cfg.force_spi_fsm_vif != null) begin
      wait (cfg.force_spi_fsm_vif.fsm_state == 3'd7); // Wait until parked in IdleCSBActive
    end else begin
      cfg.clk_rst_vif.wait_clks(250);
    end

    // Issue next segment on CS1 while CS0 is held active in IdleCSBActive
    csr_wr(.ptr(ral.csid), .value(32'h0000_0001));
    ral.txdata.write(status, 0, 32'h5A5A_1110);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // 5b. Reverse parked IdleCSBActive switch: CS1 (csaat=1) -> wait IdleCSBActive -> CS0 (csaat=0)
    csr_wr(.ptr(ral.csid), .value(32'h0000_0001));
    ral.txdata.write(status, 0, 32'hDEAD_1111);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b1;
    cmd.len       = 9'd3;
    program_command_reg(cmd);

    if (cfg.force_spi_fsm_vif != null) begin
      wait (cfg.force_spi_fsm_vif.fsm_state == 3'd7); // Wait until parked in IdleCSBActive
    end else begin
      cfg.clk_rst_vif.wait_clks(250);
    end

    csr_wr(.ptr(ral.csid), .value(32'h0000_0000));
    ral.txdata.write(status, 0, 32'hBEEF_0000);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // 5b2. Parked IdleCSBActive same-CS continuation with CPHA=1 (covers IdleCSBActive -> InternalClkHigh)
    csr_wr(.ptr(ral.csid),       .value(32'h0000_0000));
    csr_wr(.ptr(ral.configopts), .value(32'h4111_0002)); // CPHA=1, CPOL=0
    ral.txdata.write(status, 0, 32'hCAFE_1111);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b1;
    cmd.len       = 9'd3;
    program_command_reg(cmd);

    if (cfg.force_spi_fsm_vif != null) begin
      wait (cfg.force_spi_fsm_vif.fsm_state == 3'd7); // Wait until parked in IdleCSBActive
    end else begin
      cfg.clk_rst_vif.wait_clks(250);
    end

    // Issue second segment on same CS0 while parked in IdleCSBActive with cpha_q == 1
    ral.txdata.write(status, 0, 32'hBEEF_2222);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // 5c. Pipelined back-to-back CSAAT=1 CSID switch across individual config_changed fields:
    // Covers spi_host_fsm.sv:124 single-term conditions (cpol, cpha, csntrail, csnlead)
    // as well as InternalClkHigh/InternalClkLow -> WaitTrail when command_i.csid != csid_q
    begin
      bit [31:0] cfg_variants[4] = '{
        32'h8111_0002, // 1. Only cpol differs from 32'h0111_0002 (bit 31)
        32'h4111_0002, // 2. Only cpha differs from 32'h0111_0002 (bit 30)
        32'h0121_0002, // 3. Only csntrail differs from 32'h0111_0002 (bits [23:20])
        32'h0211_0002  // 4. Only csnlead differs from 32'h0111_0002 (bits [27:24])
      };

      foreach (cfg_variants[idx]) begin
        csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
        csr_wr(.ptr(ral.configopts_1), .value(cfg_variants[idx]));

        ral.txdata.write(status, 0, 32'h1234_5678);
        ral.txdata.write(status, 0, 32'h8765_4321);

        csr_wr(.ptr(ral.csid), .value(32'h0000_0000));
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b1;
        cmd.len       = 9'd3;
        program_command_reg(cmd);

        // Immediately queue CS1 command before CS0 finishes shifting
        csr_wr(.ptr(ral.csid), .value(32'h0000_0001));
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd3;
        program_command_reg(cmd);

        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
      end

      // Also exercise pipelined CSAAT=1 when the active segment has CPHA=1 (InternalClkLow -> else branch):
      // (a) CPHA=1 in-flight CS1 -> CS0 switch (next_state_after_idle_csb_active == WaitTrail)
      csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
      csr_wr(.ptr(ral.configopts_1), .value(32'h4111_0002)); // CPHA=1 on CS1
      ral.txdata.write(status, 0, 32'h1122_3344);
      ral.txdata.write(status, 0, 32'h5566_7788);
      csr_wr(.ptr(ral.csid), .value(32'h0000_0001));
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b1;
      cmd.len       = 9'd3;
      program_command_reg(cmd);

      csr_wr(.ptr(ral.csid), .value(32'h0000_0000));
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

      // (b) CPHA=1 in-flight same-CS continuation CS1 -> CS1 (next_state_after_idle_csb_active == InternalClkHigh)
      ral.txdata.write(status, 0, 32'h99AA_BBCC);
      ral.txdata.write(status, 0, 32'hDDEE_FF00);
      csr_wr(.ptr(ral.csid), .value(32'h0000_0001));
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b1;
      cmd.len       = 9'd3;
      program_command_reg(cmd);

      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
    end

    // 5d. Brief TX stall while CSID = 1 is active with fullcyc = 1
    // (covers spi_host_fsm.sv:103 sample_en_internal & ~stall = (1,0) and line 562 csid != 0 & !stall)
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h2222_0003)); // fullcyc=1 on CS1
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0001));
    ral.txdata.write(status, 0, 32'hCAFE_BABE); // Push 1 word (4 bytes) for an 8-byte command
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd7; // 8 bytes -> stalls after first 4 bytes while CS1 is active
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b1), .backdoor(1'b0), .spinwait_delay_ns(50));
    ral.txdata.write(status, 0, 32'hDEAD_C0DE); // Supply 2nd word to clear stall
    csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // 5e. Queued CS1 commands with CONFIGOPTS_1 modified while the first CS1 command is in flight:
    // Verifies that per-CS mode and timing prediction snapshots CONFIGOPTS_1 per queued command.
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0001));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0003)); // Mode 0 (cpol=0, cpha=0), lead/trail/idle=2, clkdiv=3
    ral.txdata.write(status, 0, 32'hA55A_3CC3);
    ral.txdata.write(status, 0, 32'h6996_F00F);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3; // 4 bytes
    program_command_reg(cmd);

    // Immediately update CONFIGOPTS_1 to Mode 3 (cpol=1, cpha=1), lead/trail/idle=3, clkdiv=4
    // and queue a second CS1 command while the first CS1 command is still executing
    csr_wr(.ptr(ral.configopts_1), .value(32'hC333_0004));
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3; // 4 bytes
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // 5f. Deliberate CS1 mode and timing (lead/trail/idle) fault controls
    if (cfg.en_scb) begin
      // 1) Deliberate CS1 mode (cpol/cpha) mismatch fault control:
      // Expected CS1 Mode 2 (cpol=1, cpha=0: 0 LeadingEdges, SamplingEdge = negedge SCK) vs.
      // actual DUT CS1 Mode 0 (cpol=0, cpha=0: SamplingEdge = posedge SCK). Driving MISO 1 core
      // clock after each posedge SCK with clkdiv=4 gives 4 full core clocks of setup/hold margin
      // around both posedge and negedge SCK (zero delta-cycle race, zero SVA violation, exact 8 nibbles).
      begin
        spi_host_scb_neg_catcher mode_catcher = spi_host_scb_neg_catcher::type_id::create("cs1_mode_catcher");
        uvm_reg_data_t rdata;
        bit [7:0] rx_drv_byte = 8'hA4;
        mode_catcher.match_pattern = "*READ: actual data did not match exp data*";
        csr_wr(.ptr(ral.csid),         .value(32'h0000_0001));
        csr_wr(.ptr(ral.configopts_1), .value(32'h8111_0004)); // Expected CS1 Mode 2 (cpol=1, cpha=0), clkdiv=4
        csr_poke(.ptr(ral.configopts_1), .value(32'h0111_0004), .predict(1'b0)); // Actual DUT CS1 Mode 0 (cpol=0, cpha=0), clkdiv=4
        uvm_report_cb::add(null, mode_catcher);

        wait_ready_for_command();
        cmd.direction = RxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;

        fork
          begin
            @(negedge cfg.m_spi_agent_cfg.vif.csb[1]);
            for (int b = 7; b >= 0; b--) begin
              cfg.m_spi_agent_cfg.vif.sio_out[1] = rx_drv_byte[b];
              @(posedge cfg.m_spi_agent_cfg.vif.sck);
              cfg.clk_rst_vif.wait_clks(1);
            end
            cfg.m_spi_agent_cfg.vif.sio_out[1] = ~rx_drv_byte[0];
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
            cfg.m_spi_agent_cfg.vif.sio_out = 4'bzzzz;
          end
          begin
            program_command_reg(cmd);
            csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
          end
        join

        csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        ral.rxdata.read(status, 0, rdata);
        `DV_CHECK_EQ(rdata[7:0], rx_drv_byte, "DUT Mode 0 RXDATA capture sanity check on CS1")
        cfg.clk_rst_vif.wait_clks(10);

        csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0002));
        uvm_report_cb::delete(null, mode_catcher);
        `DV_CHECK_EQ(mode_catcher.caught_err_cnt, 1,
                     "Expected CS1 mode mismatch negative control to trigger scoreboard READ error")
      end

      // 2) Deliberate CS1 csnlead, csntrail, and csnidle timing fault controls
      begin
        spi_host_scb_neg_catcher lead_catcher  = spi_host_scb_neg_catcher::type_id::create("cs1_lead_catcher");
        spi_host_scb_neg_catcher trail_catcher = spi_host_scb_neg_catcher::type_id::create("cs1_trail_catcher");
        spi_host_scb_neg_catcher idle_catcher  = spi_host_scb_neg_catcher::type_id::create("cs1_idle_catcher");
        lead_catcher.match_pattern  = "*Lead-time check failed (CS1)*";
        trail_catcher.match_pattern = "*Trail-time check failed (CS1)*";
        idle_catcher.match_pattern  = "*CS1 (CONFIGOPTS.csnidle*";
        uvm_report_cb::add(null, lead_catcher);
        uvm_report_cb::add(null, trail_catcher);
        uvm_report_cb::add(null, idle_catcher);

        // Program expected CS1 timing (lead=5, trail=5, idle=5, clkdiv=3) via frontdoor, then
        // poke faster timing (lead=0, trail=0, idle=0, clkdiv=3) into the DUT via backdoor and
        // queue two back-to-back 1-byte CS1 transfers so lead, trail, and inter-command idle
        // violations are all observed by the scoreboard.
        csr_wr(.ptr(ral.csid),         .value(32'h0000_0001));
        csr_wr(.ptr(ral.configopts_1), .value(32'h0555_0003));
        csr_poke(.ptr(ral.configopts_1), .value(32'h0000_0003), .predict(1'b0));
        write_txdata(32'h0000_00A5, 4'b0001, status);
        write_txdata(32'h0000_005A, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        wait_ready_for_command();
        program_command_reg(cmd);

        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        cfg.clk_rst_vif.wait_clks(40);

        uvm_report_cb::delete(null, lead_catcher);
        uvm_report_cb::delete(null, trail_catcher);
        uvm_report_cb::delete(null, idle_catcher);
        `DV_CHECK_GE(lead_catcher.caught_err_cnt, 1,
                     "Expected CS1 csnlead fault control to trigger Lead-time check error")
        `DV_CHECK_GE(trail_catcher.caught_err_cnt, 1,
                     "Expected CS1 csntrail fault control to trigger Trail-time check error")
        `DV_CHECK_GE(idle_catcher.caught_err_cnt, 1,
                     "Expected CS1 csnidle fault control to trigger Idle-time check error")
      end
    end
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0003));
  endtask : run_csaat_cs_switch_stimulus

endclass : spi_host_dual_cs_vseq
