// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import uvm_pkg::*;
import tlul_pkg::*;
import caliptra_prim_mubi_pkg::*;
import caliptra_ss_uart_reg_pkg::*;

interface uart_sec_cm_if (
  input logic clk_i,
  input logic rst_ni
);

  logic intg_error;

  logic [6:0]  cmd_mask;
  logic [6:0]  data_mask;
  logic [6:0]  drv_cmd_val;
  logic [6:0]  drv_data_val;

  task inject_cmd_intg_flip(int bit_idx);
    cmd_mask = (bit_idx < 7) ? (7'd1 << bit_idx) : 7'(bit_idx);
    wait (tb.dut.tl_h2d.a_valid === 1'b1);
    #1ps;
    drv_cmd_val = tb.dut.tl_h2d.a_user.cmd_intg ^ cmd_mask;
    force tb.dut.tl_h2d.a_user.cmd_intg = drv_cmd_val;
    @(posedge clk_i);
    release tb.dut.tl_h2d.a_user.cmd_intg;
  endtask

  task inject_data_intg_flip(int bit_idx);
    data_mask = (bit_idx < 7) ? (7'd1 << bit_idx) : 7'(bit_idx);
    wait (tb.dut.tl_h2d.a_valid === 1'b1);
    #1ps;
    drv_data_val = tb.dut.tl_h2d.a_user.data_intg ^ data_mask;
    force tb.dut.tl_h2d.a_user.data_intg = drv_data_val;
    @(posedge clk_i);
    release tb.dut.tl_h2d.a_user.data_intg;
  endtask

  function automatic logic get_ctrl_we();
    return tb.dut.u_caliptra_ss_uart.u_reg.ctrl_we;
  endfunction

  function automatic logic get_ctrl_tx();
    return tb.dut.u_caliptra_ss_uart.u_reg.ctrl_tx_qs;
  endfunction

  function automatic logic get_ovrd_we();
    return tb.dut.u_caliptra_ss_uart.u_reg.ovrd_we;
  endfunction

  function automatic logic get_ovrd_txen();
    return tb.dut.u_caliptra_ss_uart.u_reg.ovrd_txen_qs;
  endfunction

  task exercise_pre_intg_corners();
    @(negedge clk_i);
  endtask

  // Exercise un-driven testbench interface variables and CDC random delay instrumentation without any forces
  task exercise_uart_core_break_default();
    @(negedge clk_i);
    #1ps;

    // Toggle un-driven AXI response user signals in tb.axi_if (normal procedural assignment, no force)
    tb.axi_if.buser = 32'hFFFF_FFFF;
    tb.axi_if.ruser = 32'hFFFF_FFFF;
    #1ps;
    tb.axi_if.buser = 32'h0000_0000;
    tb.axi_if.ruser = 32'h0000_0000;
    #1ps;

    // Exercise caliptra_prim_cdc_rand_delay with cdc_instrumentation_enabled == 0 (normal bit assignment, no force)
    tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled = 1'b0;
    tb.uart_if.uart_rx = 1'b0;
    #1ps;
    tb.uart_if.uart_rx = 1'b1;
    #1ps;
    tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled = 1'b1;
  endtask

  task exercise_tlul_assert_cover_sequences();
    @(negedge clk_i);
  endtask
endinterface
