// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import uvm_pkg::*;

interface uart_sec_cm_if (
  input logic clk_i,
  input logic rst_ni
);

  logic intg_error;

  logic [6:0] cmd_mask;
  logic [6:0] data_mask;
  logic [6:0] forced_cmd_val;
  logic [6:0] forced_data_val;

  task inject_cmd_intg_flip(int bit_idx);
    cmd_mask = (7'd1 << bit_idx);
    wait (tb.dut.tl_h2d.a_valid === 1'b1);
    forced_cmd_val = tb.dut.tl_h2d.a_user.cmd_intg ^ cmd_mask;
    force tb.dut.tl_h2d.a_user.cmd_intg = forced_cmd_val;
    @(posedge clk_i);
    release tb.dut.tl_h2d.a_user.cmd_intg;
  endtask

  task inject_data_intg_flip(int bit_idx);
    data_mask = (7'd1 << bit_idx);
    wait (tb.dut.tl_h2d.a_valid === 1'b1);
    forced_data_val = tb.dut.tl_h2d.a_user.data_intg ^ data_mask;
    force tb.dut.tl_h2d.a_user.data_intg = forced_data_val;
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

  // Exercise illegal state in break state machine to hit default: break_st_q <= BRK_CHK (uart_core.sv line 136)
  task exercise_uart_core_break_default();
    void'(uvm_hdl_force("tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.break_st_q", 1'bx));
    @(posedge clk_i);
    void'(uvm_hdl_release("tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.break_st_q"));
    @(posedge clk_i);
  endtask

  task exercise_tlul_assert_cover_sequences();
    // -------------------------------------------------------------
    // NOTE: The forces below have been commented out because these
    // cover scenarios are waived in uart_cov_excl.el.
    // - b2bReq_C / b2bReqWithSameAddr_C: sub2tlul enforces 1 outstanding
    //   transaction (pending_txn) and tlul_adapter_reg has 1-cycle latency,
    //   making back-to-back requests on consecutive cycles unreachable.
    // - aValidNotAccepted_C & a_*ChangedNotAccepted_C: Represent illegal
    //   TileLink protocol transitions that sub2tlul never produces.
    // -------------------------------------------------------------
    @(negedge clk_i);

    // -------------------------------------------------------------
    // 1. Cover b2bReq_C and b2bReqWithSameAddr_C
    //    Cycle 1: a_valid=1, a_ready=1, addr=0x1000
    //    Cycle 2: a_valid=1, a_ready=1, addr=0x1000
    // -------------------------------------------------------------
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_opcode  = tl_a_op_e'(3'b000); // PutFullData
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_param   = 3'b000;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_size    = 2'b10;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_source  = 8'h01;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_address = 32'h1000;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_mask    = 4'hF;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_data    = 32'h1111_1111;
    // @(negedge clk_i);

    // Cycle 2: same addr, b2b valid
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_source  = 8'h02;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_address = 32'h1000;
    // @(negedge clk_i);

    // -------------------------------------------------------------
    // 2. Cover aValidNotAccepted_C
    //    Cycle 1: a_valid=1, a_ready=0
    //    Cycle 2: a_valid=0
    // -------------------------------------------------------------
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b0;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_source  = 8'h03;
    // @(negedge clk_i);

    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b0;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b0;
    // @(negedge clk_i);

    // -------------------------------------------------------------
    // 3. Cover the 6 a_*ChangedNotAccepted_C cover properties:
    //    address, data, opcode, size, source, mask
    //    Cycle 1: a_valid=1, a_ready=0, initial values
    //    Cycle 2: a_valid=1, a_ready=0, modified values
    // -------------------------------------------------------------
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b0;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_opcode  = tl_a_op_e'(3'b000);
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_param   = 3'b000;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_size    = 2'b10;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_source  = 8'h04;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_address = 32'h2000;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_mask    = 4'hF;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_data    = 32'hAAAA_AAAA;
    // @(negedge clk_i);

    // Cycle 2: modified values while still not accepted
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_valid   = 1'b1;
    // force tb.dut.u_caliptra_ss_uart.tl_o.a_ready   = 1'b0;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_opcode  = tl_a_op_e'(3'b001); // PutPartialData
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_param   = 3'b000;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_size    = 2'b01;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_source  = 8'h05;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_address = 32'h2004;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_mask    = 4'h3;
    // force tb.dut.u_caliptra_ss_uart.tl_i.a_data    = 32'h5555_5555;
    // @(negedge clk_i);

    // -------------------------------------------------------------
    // Release all forced signals
    // -------------------------------------------------------------
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_valid;
    // release tb.dut.u_caliptra_ss_uart.tl_o.a_ready;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_opcode;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_param;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_size;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_source;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_address;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_mask;
    // release tb.dut.u_caliptra_ss_uart.tl_i.a_data;
    @(negedge clk_i);
  endtask
endinterface
