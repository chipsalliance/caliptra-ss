// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the upper range of clkdiv values [16'h0100 : 16'hFFFF] completely unforced (fast_mode = 0)
class spi_host_upper_range_clkdiv_vseq extends spi_host_speed_vseq;
  `uvm_object_utils(spi_host_upper_range_clkdiv_vseq)
  `uvm_object_new

  constraint spi_config_regs_c {
    // SPI flash model in tb.sv requires SPI Mode 0 (cpol=0, cpha=0) and standard half-cycle sampling
    spi_config_regs.cpol == 1'b0;
    spi_config_regs.cpha == 1'b0;
    spi_config_regs.fullcyc == 1'b0;
    spi_config_regs.csnlead inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                     cfg.seq_cfg.host_spi_max_csn_latency]};
    spi_config_regs.csntrail inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                      cfg.seq_cfg.host_spi_max_csn_latency]};
    spi_config_regs.csnidle inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                     cfg.seq_cfg.host_spi_max_csn_latency]};
  }

  constraint spi_config_regs_clkdiv_c {
    // Step 1 runs unforced multi-segment flash page program & quad-read across CS0 and CS1
    // in [16'h0100 : 16'h0200], while Steps 2-4 explicitly verify unforced transfers across
    // 16'h0100, 16'h4000, 16'h8000, 16'hB000, 16'hE000, and max 16'hFFFF on every seed.
    spi_config_regs.clkdiv inside {[16'h0100 : 16'h0200]};
    spi_config_regs.clkdiv[3:0] == 0;

    // Minimise extra idle/lead/trail half-cycles during upper-divider sweeps.
    spi_config_regs.csnlead  == 4'd0;
    spi_config_regs.csntrail == 4'd0;
    spi_config_regs.csnidle  == 4'd0;
  }

  constraint num_trans_c {
    num_trans inside {[1 : 2]};
  }

  virtual task pre_start();
    super.pre_start();
    num_words             = 1;
    use_preset_configopts = 1;
    run_cov_stimulus      = 0;
    cfg.force_spi_fsm_vif.fast_mode = 0;
  endtask

  virtual task post_start();
    super.post_start();
    cfg.force_spi_fsm_vif.fast_mode = 0;
  endtask

  function void pre_randomize();
    super.pre_randomize();
    cfg.seq_cfg.host_spi_min_len = 1;
    cfg.seq_cfg.host_spi_max_len = 2;
  endfunction

  virtual task body();
    spi_host_command_t cmd;
    uvm_status_e       status;
    uvm_reg_data_t     rdata;
    realtime           t_edge1, t_edge2;
    int unsigned       obs_half_period_clks;
    int unsigned       prev_tx_cnt, prev_rx_cnt;

    // 1. Run unforced flash program & quad-read transfers across CS0 and CS1 using the
    // randomized upper-range spi_config_regs.clkdiv ([16'h0100 : 16'h0200]).
    cfg.force_spi_fsm_vif.fast_mode = 0;
    spi_host_smoke_vseq::body();

    // 2. Verify actual unforced (fast_mode = 0) upper-range Bidir (TX + RX) transfer
    // at clkdiv = 16'h0100 (256 -> half-SCK period = 257 core clocks).
    cfg.clk_rst_vif.wait_clks(10);
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    csr_wr(.ptr(ral.csid), .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_0100));
    write_txdata(32'h0000_00A5, 4'b0001, status);
    wait_ready_for_command();
    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    fork
      begin
        bit [7:0] rx_byte = 8'h3C;
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int b = 7; b >= 0; b--) begin
          cfg.m_spi_agent_cfg.vif.sio_out[1] = rx_byte[b];
          if (b == 7) begin
            @(posedge cfg.m_spi_agent_cfg.vif.sck);
            t_edge1 = $realtime();
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
            t_edge2 = $realtime();
          end else begin
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
          end
        end
        cfg.m_spi_agent_cfg.vif.sio_out = 4'bzzzz;
      end
      begin
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      end
    join
    obs_half_period_clks = $rtoi(((t_edge2 - t_edge1) / 1ps) / real'(cfg.clk_rst_vif.clk_period_ps) + 0.5);
    `DV_CHECK_EQ(obs_half_period_clks, 16'h0100 + 1,
                 "Upper-range clkdiv=0x0100 SCK half-period did not match expected 257 core clocks")
    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
    ral.rxdata.read(status, 0, rdata);
    `DV_CHECK_EQ(rdata[7:0], 8'h3C, "Expected RXDATA byte 0x3C at unforced clkdiv=0x0100")
    cfg.clk_rst_vif.wait_clks(10);
    if (cfg.en_scb) begin
      `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                   "Expected scoreboard TX check for unforced clkdiv=0x0100")
      `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                   "Expected scoreboard RX check for unforced clkdiv=0x0100")
    end

    // 3. Cover all upper-eight clkdiv bins ([16'h00ff : 16'hfffe]) across CS0 and CS1 via unforced
    // 1-byte Quad scoreboard-checked transfers (2 SCK cycles per byte).
    begin
      bit [15:0] upper_bins[4] = '{16'h4000, 16'h8000, 16'hB000, 16'hE000};
      foreach (upper_bins[idx]) begin
        int cs_idx = idx % SPI_HOST_NUM_CS;
        csr_wr(.ptr(ral.csid), .value(cs_idx));
        if (cs_idx == 1) begin
          csr_wr(.ptr(ral.configopts_1), .value({16'h0000, upper_bins[idx]}));
        end else begin
          csr_wr(.ptr(ral.configopts), .value({16'h0000, upper_bins[idx]}));
        end
        write_txdata(32'h0000_0050 | idx[7:0], 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Quad;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      end
    end

    // 4. Verify actual unforced (fast_mode = 0) max-range Bidir (TX + RX) transfer
    // at clkdiv = 16'hFFFF (65535 -> half-SCK period = 65536 core clocks) on CS0, plus
    // a 1-byte Quad checked transfer at 16'hFFFF on CS1.
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_FFFF));
    write_txdata(32'h0000_00A3, 4'b0001, status);
    wait_ready_for_command();
    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    fork
      begin
        bit [7:0] rx_byte = 8'hC3;
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int b = 7; b >= 0; b--) begin
          cfg.m_spi_agent_cfg.vif.sio_out[1] = rx_byte[b];
          if (b == 7) begin
            @(posedge cfg.m_spi_agent_cfg.vif.sck);
            t_edge1 = $realtime();
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
            t_edge2 = $realtime();
          end else begin
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
          end
        end
        cfg.m_spi_agent_cfg.vif.sio_out = 4'bzzzz;
      end
      begin
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      end
    join
    obs_half_period_clks = $rtoi(((t_edge2 - t_edge1) / 1ps) / real'(cfg.clk_rst_vif.clk_period_ps) + 0.5);
    `DV_CHECK_EQ(obs_half_period_clks, 32'd65536,
                 "Upper-range clkdiv=0xFFFF SCK half-period did not match expected 65536 core clocks")
    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
    ral.rxdata.read(status, 0, rdata);
    `DV_CHECK_EQ(rdata[7:0], 8'hC3, "Expected RXDATA byte 0xC3 at unforced clkdiv=0xFFFF")

    if (SPI_HOST_NUM_CS > 1) begin
      csr_wr(.ptr(ral.csid),         .value(32'h1));
      csr_wr(.ptr(ral.configopts_1), .value(32'h0000_FFFF));
      write_txdata(32'h0000_00E7, 4'b0001, status);
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Quad;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      @(posedge cfg.m_spi_agent_cfg.vif.csb[1]);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                   .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      csr_wr(.ptr(ral.csid), .value(32'h0));
    end

    cfg.clk_rst_vif.wait_clks(10);
    if (cfg.en_scb) begin
      `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + ((SPI_HOST_NUM_CS > 1) ? 2 : 1),
                   "Expected scoreboard TX check for unforced clkdiv=0xFFFF across CS0/CS1")
      `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                   "Expected scoreboard RX check for unforced clkdiv=0xFFFF")
    end

    // 5. Negative controls at unforced upper-range clkdiv (0x0100):
    // Verify that divider/timing mismatch, TX mismatch, and RX mismatch are caught.
    if (cfg.en_scb) begin
      // 5a. Divider / lead-time fault control (transfer runs at clkdiv=0x0100 while expected is clkdiv=0x0200)
      begin
        spi_host_scb_neg_catcher lead_catcher  = spi_host_scb_neg_catcher::type_id::create("upper_lead_catcher");
        spi_host_scb_neg_catcher trail_catcher = spi_host_scb_neg_catcher::type_id::create("upper_trail_catcher");
        lead_catcher.match_pattern  = "*Lead-time check failed*";
        trail_catcher.match_pattern = "*Trail-time check failed*";
        uvm_report_cb::add(null, lead_catcher);
        uvm_report_cb::add(null, trail_catcher);

        csr_wr(.ptr(ral.csid),       .value(32'h0));
        csr_wr(.ptr(ral.configopts), .value(32'h0000_0200)); // Expected half-period 513 > actual 257
        csr_poke(.ptr(ral.configopts), .value(32'h0000_0100), .predict(1'b0));
        write_txdata(32'h0000_0055, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(500));
        cfg.clk_rst_vif.wait_clks(300);

        uvm_report_cb::delete(null, lead_catcher);
        uvm_report_cb::delete(null, trail_catcher);
        `DV_CHECK_GE(lead_catcher.caught_err_cnt + trail_catcher.caught_err_cnt, 1,
                     "Expected upper-range clkdiv timing fault control to trigger Lead/Trail check error")
      end

      // 5b. TX and RX mismatch fault controls at unforced clkdiv = 16'h0100
      begin
        spi_host_scb_neg_catcher tx_catcher = spi_host_scb_neg_catcher::type_id::create("upper_tx_catcher");
        spi_host_scb_neg_catcher rx_catcher = spi_host_scb_neg_catcher::type_id::create("upper_rx_catcher");
        bit orig_host_dir = cfg.m_spi_agent_cfg.host_bit_dir;
        bit orig_dev_dir  = cfg.m_spi_agent_cfg.device_bit_dir;
        rx_catcher.match_pattern = "*READ: actual data did not match exp data*";
        uvm_report_cb::add(null, tx_catcher);
        uvm_report_cb::add(null, rx_catcher);

        csr_wr(.ptr(ral.configopts), .value(32'h0000_0100));
        cfg.m_spi_agent_cfg.host_bit_dir   = ~orig_host_dir;
        cfg.m_spi_agent_cfg.device_bit_dir = ~orig_dev_dir;

        // TX mismatch at clkdiv=0x0100
        write_txdata(32'h0000_00A4, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(500));

        // RX mismatch at clkdiv=0x0100
        fork
          begin
            bit [7:0] rx_drv = 8'hA4;
            @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
            for (int b = 7; b >= 0; b--) begin
              cfg.m_spi_agent_cfg.vif.sio_out[1] = rx_drv[b];
              @(negedge cfg.m_spi_agent_cfg.vif.sck);
            end
            cfg.m_spi_agent_cfg.vif.sio_out = 4'bzzzz;
          end
        join_none
        wait_ready_for_command();
        cmd.direction = RxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(500));
        csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
        ral.rxdata.read(status, 0, rdata);
        cfg.clk_rst_vif.wait_clks(10);

        cfg.m_spi_agent_cfg.host_bit_dir   = orig_host_dir;
        cfg.m_spi_agent_cfg.device_bit_dir = orig_dev_dir;
        uvm_report_cb::delete(null, tx_catcher);
        uvm_report_cb::delete(null, rx_catcher);
        `DV_CHECK_EQ(tx_catcher.caught_err_cnt, 1,
                     "Expected upper-range clkdiv TX fault control to catch 1 TX mismatch")
        `DV_CHECK_EQ(rx_catcher.caught_err_cnt, 1,
                     "Expected upper-range clkdiv RX fault control to catch 1 RX mismatch")
      end
    end

    // 6. Follow with a clean unforced transfer at clkdiv = 16'h0002 to verify recovery
    // and complete 1->0 toggle across upper clkdiv bits after testing 0xFFFF and 0x0100.
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0002));
    write_txdata(32'h0000_00C3, 4'b0001, status);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
  endtask : body

endclass : spi_host_upper_range_clkdiv_vseq
