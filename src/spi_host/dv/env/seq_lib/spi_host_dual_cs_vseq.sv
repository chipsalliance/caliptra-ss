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

    // 5. Test CSAAT=1 active CSID switch (CS0 <-> CS1) from IdleCSBActive and pipelined CPHA=0/1
    // Covers spi_host_fsm.sv lines 214, 221, 223 (command_i.csid != csid_q -> WaitTrail)
    run_csaat_cs_switch_stimulus();

    // 6. Test out-of-range CSID >= SPI_HOST_NUM_CS (CSID = 2) -> csidinval error assertion
    csr_wr(.ptr(ral.error_enable), .value(32'h0000_001F));
    csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0003));
    csr_wr(.ptr(ral.csid),         .value(32'h0000_0002));
    csr_wr(.ptr(ral.command),      .value(32'h0200_0000)); // Direction=TxOnly, Len=0

    // Verify error_status.csidinval (bit 4) is set
    csr_rd(.ptr(ral.error_status), .value(err_val));
    `DV_CHECK_EQ(err_val[4], 1'b1, "Expected csidinval error_status[4] == 1 when CSID = 2")

    // Clear csidinval error and recover via software reset
    csr_wr(.ptr(ral.control.sw_rst), .value(1'b1));
    csr_wr(.ptr(ral.control.sw_rst), .value(1'b0));
    csr_wr(.ptr(ral.error_status),   .value(32'h0000_0010));
    csr_wr(.ptr(ral.intr_state),     .value(32'h0000_0003));
    csr_wr(.ptr(ral.csid),           .value(32'h0000_0000));

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
    end

    // 5d. Brief TX stall while CSID = 1 is active (covers spi_host_fsm.sv:562 csid != 0 and !stall)
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0003));
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
  endtask : run_csaat_cs_switch_stimulus

endclass : spi_host_dual_cs_vseq
