// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the upper range of clkdiv values [FF+1: FFFF]
class spi_host_upper_range_clkdiv_vseq extends spi_host_speed_vseq;
  `uvm_object_utils(spi_host_upper_range_clkdiv_vseq)
  `uvm_object_new

  // when set causes the constraint to pick the maximum value in the clock divider range
  rand bit max_range_value;

  constraint spi_config_regs_clkdiv_c {
    solve max_range_value before spi_config_regs.clkdiv;
    max_range_value dist { 0 :/ 7, 1 :/ 3};
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
    super.body();

    // Explicitly exercise upper clkdiv[15:8] bits through u_cmd_queue -> u_spi_core -> u_fsm
    csr_wr(.ptr(ral.csid), .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0111_FF00));
    wait_ready_for_command();
    cmd.direction = None;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    program_command_reg(cmd);
    cfg.clk_rst_vif.wait_clks(20);

    // Clear slow transfer via sw_rst and follow with clkdiv[15:8] = 8'h00 to complete 1->0 toggle
    csr_wr(.ptr(ral.control.sw_rst), .value(1'b1));
    cfg.clk_rst_vif.wait_clks(5);
    csr_wr(.ptr(ral.control.sw_rst), .value(1'b0));
    csr_wr(.ptr(ral.control.spien),  .value(1'b1));

    csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));
    wait_ready_for_command();
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
  endtask : body

endclass : spi_host_upper_range_clkdiv_vseq
