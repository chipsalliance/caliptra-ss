// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// speed test vseq
class spi_host_speed_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_speed_vseq)
  `uvm_object_new

  constraint spi_config_regs_c {
    spi_config_regs.cpol dist {
      1'b0 :/ 1,
      1'b1 :/ 1
    };
    spi_config_regs.cpha dist {
      1'b0 :/ 1,
      1'b1 :/ 1
    };
    spi_config_regs.csnlead inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                     cfg.seq_cfg.host_spi_max_csn_latency]};
    spi_config_regs.csntrail inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                      cfg.seq_cfg.host_spi_max_csn_latency]};
    spi_config_regs.csnidle inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                     cfg.seq_cfg.host_spi_max_csn_latency]};
  }

  constraint spi_config_regs_clkdiv_c {
    // CLKDIV randomised in lower/mid range here; upper range [0x0100:0xFFFF] is verified
    // unforced in spi_host_upper_range_clkdiv_vseq.sv.
    spi_config_regs.clkdiv inside {[cfg.seq_cfg.host_spi_min_clkdiv :
                                    cfg.seq_cfg.host_spi_lower_middle_clkdiv]};
  }

  virtual task pre_start();
    super.pre_start();
    run_cov_stimulus = 1'b0;
  endtask

  virtual task start_spi_host_trans(int num_transactions, bit wait_ready = 1'b1);
    cfg.seq_cfg.std_en  = 1;
    cfg.seq_cfg.dual_en = 1;
    cfg.seq_cfg.quad_en = 1;
    super.start_spi_host_trans(num_transactions);
  endtask

  virtual task sweep_config_opts();
    uvm_status_e status;
    uvm_reg_data_t rdata;
    spi_host_command_t cmd;
    // Includes exact max 4-bit boundary 4'd15 across CSNLEAD, CSNTRAIL, and CSNIDLE (Comment #9)
    bit [3:0] latency_vals[4] = '{4'd0, 4'd3, 4'd8, 4'd15};
    // Lower and bottom-eight clkdiv bins: {0}, {[1:15]} (4 bins), {[16'h10:16'hfe]} (5 bins)
    bit [15:0] xfer_clkdiv_vals[10] = '{
      16'd0,
      16'd1, 16'd5, 16'd10, 16'd15,
      16'h0020, 16'h0050, 16'h0080, 16'h00b0, 16'h00e0
    };
    int iter_idx = 0;

    `uvm_info(`gfn, "Executing scoreboard-checked TX/RX transfers across CS0/CS1 timing (incl. 15) & clkdiv bins", UVM_LOW)
    csr_wr(.ptr(ral.control), .value(32'hA000_007F)); // spien=1, output_en=1

    for (int lead_i = 0; lead_i < 4; lead_i++) begin
      for (int idle_i = 0; idle_i < 4; idle_i++) begin
        for (int trail_i = 0; trail_i < 4; trail_i++) begin
          bit cpol_val    = bit'(lead_i % 2);
          bit cpha_val    = bit'(idle_i % 2);
          bit fullcyc_val = bit'(trail_i % 2);
          int cs_idx      = ((lead_i / 2) ^ (idle_i / 2) ^ (trail_i % 2)) % SPI_HOST_NUM_CS;
          bit [15:0] cur_clkdiv = xfer_clkdiv_vals[iter_idx % $size(xfer_clkdiv_vals)];
          bit [31:0] cfg_word   = {
            cpol_val, cpha_val, fullcyc_val, 1'b0,
            latency_vals[lead_i], latency_vals[trail_i], latency_vals[idle_i],
            cur_clkdiv
          };

          csr_wr(.ptr(ral.csid), .value(cs_idx));
          if (cs_idx == 1) begin
            csr_wr(.ptr(ral.configopts_1), .value(cfg_word));
          end else begin
            csr_wr(.ptr(ral.configopts), .value(cfg_word));
          end

          // Confirmed Design Contract (Harry Callahan, Option A, Nov 12, 2026 - Comment #4):
          // Full-cycle RX sampling (FULLCYC=1) is architecturally supported only when CPHA=0
          // (spi_host_fsm.sv:275); TxOnly is used for (cpha=1, fullcyc=1).
          write_txdata(32'hA55A_00FF ^ {16'(iter_idx), 8'(lead_i), 8'(trail_i)}, 4'b0001, status);
          wait_ready_for_command();
          cmd.direction = (cpha_val && fullcyc_val) ? TxOnly : Bidir;
          cmd.mode      = Standard;
          cmd.csaat     = 1'b0;
          cmd.len       = 9'd0; // 1-byte checked transfer
          program_command_reg(cmd);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

          if (cmd.direction == Bidir) begin
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
            ral.rxdata.read(status, 0, rdata);
          end

          iter_idx++;
        end
      end
    end

    // Controlled delayed-MISO sensitivity check & negative controls for CONFIGOPTS.FULLCYC (Comment #4)
    run_fullcyc_delayed_miso_and_fault_check();

    // Two-sided ConfigSwitch (WaitIdle + CSBSwitch) positive & negative controls (Comment #20)
    run_two_sided_config_switch_checks();

    // Also verify end-to-end Flash page program + Quad readback across both CS0 and CS1
    begin
      int saved_num_words = num_words;
      num_words = 4;
      for (int i = 0; i < 4; i++) begin
        int cs_idx = i % SPI_HOST_NUM_CS;
        bit [31:0] flash_cfg = {
          1'b0, 1'b0, bit'(i % 2 == 1), 1'b0,
          latency_vals[i], latency_vals[3 - i], latency_vals[i],
          xfer_clkdiv_vals[i]
        };
        if (cs_idx == 1) begin
          csr_wr(.ptr(ral.configopts_1), .value(flash_cfg));
        end else begin
          csr_wr(.ptr(ral.configopts), .value(flash_cfg));
        end
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
          flash_addr < 32'h080000;
          flash_addr[7:0] == 8'h00;
        )
        `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
        run_flash_page_program_and_read(cs_idx[1:0]);
      end
      num_words = saved_num_words;
    end

    // Restore clean default operating configopts on both chip selects
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0002));
  endtask

  // Drives an identical delayed-MISO waveform where MISO holds early_byte (0x5A) through the
  // nominal half-cycle posedge SCK, then transitions 2 core clocks later (mid-high-phase at
  // clkdiv=4) to late_byte (0xA5) before the full-cycle negedge SCK:
  //   - FULLCYC = 0 must capture 0x5A (nominal half-cycle sample_en_q)
  //   - FULLCYC = 1 must capture 0xA5 (full-cycle sample_en_q2)
  //   - Negative controls prove both DUT ignoring FULLCYC and scoreboard ignoring FULLCYC fail.
  virtual task drive_delayed_miso_byte(int cs_idx, bit [7:0] early_b, bit [7:0] late_b);
    @(negedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
    cfg.m_spi_agent_cfg.vif.sio_out[1] <= early_b[7];
    for (int b = 7; b >= 0; b--) begin
      @(posedge cfg.m_spi_agent_cfg.vif.sck);
      cfg.clk_rst_vif.wait_clks(2);
      cfg.m_spi_agent_cfg.vif.sio_out[1] <= late_b[b];
      @(negedge cfg.m_spi_agent_cfg.vif.sck);
      cfg.m_spi_agent_cfg.vif.sio_out[1] <= (b > 0) ? early_b[b - 1] : 1'bz;
    end
    cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
  endtask

  virtual task run_fullcyc_delayed_miso_and_fault_check();
    localparam bit [7:0] EARLY_MISO = 8'h5A;
    localparam bit [7:0] LATE_MISO  = 8'hA5;
    spi_host_command_t cmd;
    uvm_status_e       status;
    uvm_reg_data_t     rdata;
    int unsigned       prev_rx_cnt;

    `uvm_info(`gfn, "Running controlled FULLCYC=0 vs FULLCYC=1 delayed-MISO sensitivity & fault checks", UVM_LOW)
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);

    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      for (int fc = 0; fc <= 1; fc++) begin
        bit [31:0] cfg_w = {1'b0, 1'b0, bit'(fc), 1'b0, 4'd0, 4'd1, 4'd1, 16'd4};
        bit [7:0]  exp_b = fc ? LATE_MISO : EARLY_MISO;
        prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;

        csr_wr(.ptr(ral.csid), .value(cs));
        if (cs == 1) csr_wr(.ptr(ral.configopts_1), .value(cfg_w));
        else         csr_wr(.ptr(ral.configopts),   .value(cfg_w));

        write_txdata(32'h0000_003C, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = Bidir;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        fork
          drive_delayed_miso_byte(cs, EARLY_MISO, LATE_MISO);
          begin
            program_command_reg(cmd);
            csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
          end
        join
        csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        ral.rxdata.read(status, 0, rdata);
        `DV_CHECK_EQ(rdata[7:0], exp_b,
                     $sformatf("Delayed-MISO capture mismatch on CS%0d for FULLCYC=%0d", cs, fc))
        cfg.clk_rst_vif.wait_clks(10);
        if (cfg.en_scb) begin
          `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                       "Expected scoreboard RX check on delayed-MISO FULLCYC transfer")
        end
      end
    end

    // Negative controls (1: DUT ignores FULLCYC via backdoor poke; 2: s_ignore_fullcyc_fault=1)
    if (cfg.en_scb) begin
      spi_host_scb_neg_catcher fc_catcher = spi_host_scb_neg_catcher::type_id::create("fc_catcher");
      fc_catcher.match_pattern = "*READ: actual data did not match exp data*";
      uvm_report_cb::add(null, fc_catcher);

      // (a) Simulate a broken DUT that ignores FULLCYC=1 (captures 0x5A while scoreboard expects 0xA5)
      csr_wr(.ptr(ral.csid),       .value(32'h0));
      csr_wr(.ptr(ral.configopts), .value(32'h2011_0004)); // Expected FULLCYC=1
      csr_poke(.ptr(ral.configopts), .value(32'h0011_0004), .predict(1'b0)); // Actual DUT FULLCYC=0
      wait_ready_for_command();
      cmd.direction = RxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      fork
        drive_delayed_miso_byte(0, EARLY_MISO, LATE_MISO);
        begin
          program_command_reg(cmd);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        end
      join
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(status, 0, rdata);
      `DV_CHECK_EQ(rdata[7:0], EARLY_MISO)
      cfg.clk_rst_vif.wait_clks(10);
      `DV_CHECK_EQ(fc_catcher.caught_err_cnt, 1,
                   "Expected scoreboard to detect a DUT mutant that ignores FULLCYC=1")

      // (b) Exercise s_ignore_fullcyc_fault=1 against real FULLCYC=1 DUT capture (0xA5 vs 0x5A)
      csr_wr(.ptr(ral.configopts), .value(32'h2011_0004));
      spi_host_scoreboard::s_ignore_fullcyc_fault = 1'b1;
      wait_ready_for_command();
      fork
        drive_delayed_miso_byte(0, EARLY_MISO, LATE_MISO);
        begin
          program_command_reg(cmd);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        end
      join
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(status, 0, rdata);
      `DV_CHECK_EQ(rdata[7:0], LATE_MISO)
      cfg.clk_rst_vif.wait_clks(10);
      spi_host_scoreboard::s_ignore_fullcyc_fault = 1'b0;
      uvm_report_cb::delete(null, fc_catcher);
      `DV_CHECK_EQ(fc_catcher.caught_err_cnt, 2,
                   "Expected s_ignore_fullcyc_fault negative control to trigger scoreboard READ error")
      program_spi_host_sw_reset();
    end

    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
  endtask

  // Verifies both pre-switch (WaitIdle) and post-switch (CSBSwitch) idle bounds and all-CSB-high
  // CPOL transition placement, plus early-transition and missing-CPOL-switch negative controls (Comment #20).
  virtual task run_two_sided_config_switch_checks();
    spi_host_command_t cmd;
    uvm_status_e       status;
    uvm_reg_data_t     rdata;

    // 1. Positive single-field CSNIDLE-only transition and CPOL+CSNIDLE two-sided transition
    begin
      bit [31:0] switch_cfgs[3] = '{
        {1'b0, 1'b0, 1'b0, 1'b0, 4'd2, 4'd2, 4'd2, 16'd2}, // Frame 0: CPOL=0, CSNIDLE=2, CLKDIV=2
        {1'b0, 1'b0, 1'b0, 1'b0, 4'd2, 4'd2, 4'd5, 16'd2}, // Frame 1: CSNIDLE-only change (2 -> 5)
        {1'b1, 1'b0, 1'b0, 1'b0, 4'd2, 4'd2, 4'd4, 16'd3}  // Frame 2: CPOL (0 -> 1) + CSNIDLE + CLKDIV switch
      };
      csr_wr(.ptr(ral.csid), .value(32'h0));
      foreach (switch_cfgs[k]) begin
        csr_wr(.ptr(ral.configopts), .value(switch_cfgs[k]));
        write_txdata(32'h0000_005A ^ k, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = Bidir;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        ral.rxdata.read(status, 0, rdata);
      end
    end

    // 2. Negative controls: (a) early pre/post ConfigSwitch transition, (b) missing idle CPOL switch
    if (cfg.en_scb) begin
      spi_host_scb_neg_catcher total_catcher = spi_host_scb_neg_catcher::type_id::create("cfgsw_total_catcher");
      spi_host_scb_neg_catcher pre_catcher   = spi_host_scb_neg_catcher::type_id::create("cfgsw_pre_catcher");
      spi_host_scb_neg_catcher post_catcher  = spi_host_scb_neg_catcher::type_id::create("cfgsw_post_catcher");
      spi_host_scb_neg_catcher cpol_catcher  = spi_host_scb_neg_catcher::type_id::create("cfgsw_cpol_catcher");
      total_catcher.match_pattern = "*Two-sided ConfigSwitch CSNIDLE check failed*";
      pre_catcher.match_pattern   = "*ConfigSwitch pre-polarity-switch idle failed*";
      post_catcher.match_pattern  = "*ConfigSwitch post-polarity-switch idle failed*";
      cpol_catcher.match_pattern  = "*ConfigSwitch CPOL transition missing while all CSB high*";
      uvm_report_cb::add(null, total_catcher);
      uvm_report_cb::add(null, pre_catcher);
      uvm_report_cb::add(null, post_catcher);
      uvm_report_cb::add(null, cpol_catcher);

      // (a) Early pre/post ConfigSwitch negative control
      csr_wr(.ptr(ral.csid),       .value(32'h0));
      csr_wr(.ptr(ral.configopts), .value(32'h0115_0003)); // Frame A: CPOL=0, CSNIDLE=5, CLKDIV=3
      write_txdata(32'h0000_00A5, 4'b0001, status);
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

      csr_wr(.ptr(ral.configopts), .value(32'h8115_0003)); // Frame B: CPOL=1, CSNIDLE=5
      spi_host_scoreboard::s_force_early_csnidle_fault = 1'b1;
      write_txdata(32'h0000_005A, 4'b0001, status);
      wait_ready_for_command();
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      spi_host_scoreboard::s_force_early_csnidle_fault = 1'b0;

      // (b) Missing idle CPOL transition negative control (frontdoor CPOL=0, backdoor poked CPOL=1)
      csr_wr(.ptr(ral.configopts), .value(32'h0112_0003)); // Scoreboard expects CPOL 1 -> 0
      csr_poke(.ptr(ral.configopts), .value(32'h8112_0003), .predict(1'b0)); // DUT stays CPOL=1 (no idle SCK switch)
      write_txdata(32'h0000_00FF, 4'b0001, status); // All-ones TX byte is mode-invariant so only CPOL switch check fires
      wait_ready_for_command();
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      cfg.clk_rst_vif.wait_clks(20);

      uvm_report_cb::delete(null, total_catcher);
      uvm_report_cb::delete(null, pre_catcher);
      uvm_report_cb::delete(null, post_catcher);
      uvm_report_cb::delete(null, cpol_catcher);
      `DV_CHECK_EQ(total_catcher.caught_err_cnt, 1,
                   "Expected two-sided ConfigSwitch total-idle negative control to fire")
      `DV_CHECK_EQ(pre_catcher.caught_err_cnt, 1,
                   "Expected ConfigSwitch pre-polarity-switch idle negative control to fire")
      `DV_CHECK_EQ(post_catcher.caught_err_cnt, 1,
                   "Expected ConfigSwitch post-polarity-switch idle negative control to fire")
      `DV_CHECK_EQ(cpol_catcher.caught_err_cnt, 1,
                   "Expected ConfigSwitch missing-CPOL-transition negative control to fire")
      program_spi_host_sw_reset();
      csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));
      program_control_reg();
    end
  endtask

  virtual task body();
    super.body();
    sweep_config_opts();
  endtask

endclass : spi_host_speed_vseq
