// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the upper range of clkdiv values [FF+1: FFFF]
class spi_host_upper_range_clkdiv_vseq extends spi_host_speed_vseq;
  `uvm_object_utils(spi_host_upper_range_clkdiv_vseq)
  `uvm_object_new

  // when set causes the constraint to pick the maximum value in the clock divider range
  rand bit max_range_value;

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
    solve max_range_value before spi_config_regs.clkdiv;
    // Step 3 explicitly runs scoreboard-checked transfers at 16'hFF00 and 16'hFFFF on every seed,
    // so randomize Step 1's multi-segment flash page program/read in [16'h100 : 16'h400].
    max_range_value == 0;
    if (max_range_value) {
      spi_config_regs.clkdiv == 16'hffff;
    } else {
      spi_config_regs.clkdiv inside {[16'h100 : 16'h400]};
      spi_config_regs.clkdiv[3:0] == 0;
    }

    // In order to minimise sim-time the idle/lead/trail delays are all set to 0.
    foreach (spi_config_regs.csnlead[i]) {
      spi_config_regs.csnlead[i] == 0;
    }
    foreach (spi_config_regs.csntrail[i]) {
      spi_config_regs.csntrail[i] == 0;
    }
    foreach (spi_config_regs.csnidle[i]) {
      spi_config_regs.csnidle[i] == 0 ;
    }
  }

  constraint num_trans_c {
    // Really low number of TXN generated to avoid lenghty simulation time
    // since we already have a very slow SPI clock
    num_trans inside {[1 : 2]};
  }

  // This VSEQ is the only one which allows large clock divider values and due to that the
  // VSEQ allow the internal FSM counter to be decremented by 16-units.
  // The VIF flag is enabled only whilst this VSEQ is run
  virtual task pre_start();
    super.pre_start();
    num_words = 1;
    use_preset_configopts = 1;
    run_cov_stimulus      = 0;
    cfg.force_spi_fsm_vif.fast_mode = 1;
  endtask

  virtual task post_start();
    super.post_start();
    cfg.force_spi_fsm_vif.fast_mode = 0;
  endtask

  function void pre_randomize();
    super.pre_randomize();
    // Redefining the ranges to ensure 'num_cmd_bytes' gets randomised to a
    // lower value to ensure simulations finish sooner
    cfg.seq_cfg.host_spi_min_len = 1;
    cfg.seq_cfg.host_spi_max_len = 2;
  endfunction

  virtual task body();
    spi_host_command_t cmd;
    uvm_status_e       status;
    realtime           t_edge1, t_edge2;
    int unsigned       obs_half_period_clks;

    // 1. Run flash program & quad-read transfers across CS0 and CS1 using the
    // randomized upper-range spi_config_regs.clkdiv ([16'h100:16'h400] or 16'hffff).
    spi_host_smoke_vseq::body();

    // 2. Verify actual upper-range divider timing with fast_mode = 0 (no counter shortcut)
    // at clkdiv = 16'h0100 (256 -> half-SCK period = 257 core clocks) and check TX data in scoreboard.
    cfg.force_spi_fsm_vif.fast_mode = 0;
    csr_wr(.ptr(ral.csid), .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_0100));
    write_txdata(32'h0000_00A5, 4'b0001, status);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    fork
      begin
        @(posedge cfg.m_spi_agent_cfg.vif.sck);
        t_edge1 = $realtime();
        @(negedge cfg.m_spi_agent_cfg.vif.sck);
        t_edge2 = $realtime();
      end
      begin
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      end
    join
    obs_half_period_clks = $rtoi(((t_edge2 - t_edge1) / 1ps) / real'(cfg.clk_rst_vif.clk_period_ps) + 0.5);
    `DV_CHECK_EQ(obs_half_period_clks, 16'h0100 + 1,
                 "Upper-range clkdiv=0x0100 SCK half-period did not match expected divider timing")

    // 3. Re-enable fast_mode and complete scoreboard-checked transfers at clkdiv = 16'hFF00 and 16'hFFFF
    // to exercise all upper clkdiv[15:8] bits through u_cmd_queue -> u_spi_core -> u_fsm.
    cfg.force_spi_fsm_vif.fast_mode = 1;
    csr_wr(.ptr(ral.configopts), .value(32'h0111_FF00));
    write_txdata(32'h0000_005A, 4'b0001, status);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                 .spinwait_delay_ns(500), .timeout_ns(50_000_000));

    csr_wr(.ptr(ral.configopts), .value(32'h0111_FFFF));
    write_txdata(32'h0000_003C, 4'b0001, status);
    wait_ready_for_command();
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                 .spinwait_delay_ns(500), .timeout_ns(50_000_000));

    // 4. Follow with clkdiv[15:8] = 8'h00 transfer to complete 1->0 toggle on upper clkdiv bits
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));
    write_txdata(32'h0000_00C3, 4'b0001, status);
    wait_ready_for_command();
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
  endtask : body

endclass : spi_host_upper_range_clkdiv_vseq
