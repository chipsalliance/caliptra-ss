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
  logic [1:0]      last_bresp;
  logic [1:0]      last_rresp;
  logic            last_d_error;
  logic            last_intg_err;
  logic            last_reg_we_err;
  logic            last_d2h_rsp_intg_err;
  logic            last_reg_side_effect;
  logic            last_addrmiss_or_wr_err;
  int unsigned     intg_err_cnt;

  // Monotonic fault-detection counters preserved across hardware resets for EOT sign-off
  int unsigned     total_h2d_intg_err_cnt      = 0;
  int unsigned     total_cmd_single_err_cnt    = 0;
  int unsigned     total_cmd_multibit_err_cnt  = 0;
  int unsigned     total_data_single_err_cnt   = 0;
  int unsigned     total_data_multibit_err_cnt = 0;
  int unsigned     total_reg_we_err_cnt        = 0;
  int unsigned     total_d2h_intg_err_cnt      = 0;

  // Serialize concurrent fault-injection tasks so IEEE 1800 static force-RHS storage cannot race.
  semaphore        inject_lock = new(1);

  function automatic void clear_monotonic_counters();
    total_h2d_intg_err_cnt      = 0;
    total_cmd_single_err_cnt    = 0;
    total_cmd_multibit_err_cnt  = 0;
    total_data_single_err_cnt   = 0;
    total_data_multibit_err_cnt = 0;
    total_reg_we_err_cnt        = 0;
    total_d2h_intg_err_cnt      = 0;
  endfunction

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_bresp              <= 2'b00;
      last_rresp              <= 2'b00;
      last_d_error            <= 1'b0;
      last_intg_err           <= 1'b0;
      last_reg_we_err         <= 1'b0;
      last_d2h_rsp_intg_err   <= 1'b0;
      last_reg_side_effect    <= 1'b0;
      last_addrmiss_or_wr_err <= 1'b0;
      intg_err_cnt            <= 0;
    end else begin
      if (tb.dut.u_caliptra_ss_uart.u_reg.reg_we_err) begin
        last_reg_we_err      <= 1'b1;
        total_reg_we_err_cnt <= total_reg_we_err_cnt + 1;
      end
      if (tb.dut.tl_h2d.a_valid && tb.dut.tl_d2h.a_ready) begin
        last_intg_err           <= tb.dut.u_caliptra_ss_uart.u_reg.u_chk.err_o;
        last_reg_side_effect    <= (|tb.dut.u_caliptra_ss_uart.u_reg.reg_we_check) |
                                   tb.dut.u_caliptra_ss_uart.u_reg.status_re       |
                                   tb.dut.u_caliptra_ss_uart.u_reg.rdata_re        |
                                   tb.dut.u_caliptra_ss_uart.u_reg.fifo_status_re  |
                                   tb.dut.u_caliptra_ss_uart.u_reg.val_re;
        last_addrmiss_or_wr_err <= tb.dut.u_caliptra_ss_uart.u_reg.addrmiss |
                                   tb.dut.u_caliptra_ss_uart.u_reg.wr_err;
        if (tb.dut.u_caliptra_ss_uart.u_reg.u_chk.err_o) begin
          intg_err_cnt           <= intg_err_cnt + 1;
          total_h2d_intg_err_cnt <= total_h2d_intg_err_cnt + 1;
        end
        if (tb.dut.u_caliptra_ss_uart.u_reg.u_chk.err[0]) begin
          total_cmd_single_err_cnt <= total_cmd_single_err_cnt + 1;
        end
        if (tb.dut.u_caliptra_ss_uart.u_reg.u_chk.err[1]) begin
          total_cmd_multibit_err_cnt <= total_cmd_multibit_err_cnt + 1;
        end
        if (tb.dut.u_caliptra_ss_uart.u_reg.u_chk.u_tlul_data_integ_dec.data_err[0]) begin
          total_data_single_err_cnt <= total_data_single_err_cnt + 1;
        end
        if (tb.dut.u_caliptra_ss_uart.u_reg.u_chk.u_tlul_data_integ_dec.data_err[1]) begin
          total_data_multibit_err_cnt <= total_data_multibit_err_cnt + 1;
        end
      end
      if (tb.dut.tl_d2h.d_valid && tb.dut.tl_h2d.d_ready) begin
        last_d_error          <= tb.dut.tl_d2h.d_error;
        last_d2h_rsp_intg_err <= tb.tlul_rsp_intg_err;
        if (tb.tlul_rsp_intg_err) begin
          total_d2h_intg_err_cnt <= total_d2h_intg_err_cnt + 1;
        end
      end
      if (tb.axi_if.bvalid && tb.axi_if.bready) begin
        last_bresp <= tb.axi_if.bresp;
      end
      if (tb.axi_if.rvalid && tb.axi_if.rready) begin
        last_rresp <= tb.axi_if.rresp;
      end
    end
  end

  task automatic inject_cmd_intg_flip(logic [6:0] xor_mask);
    static logic [6:0] drv_cmd_val;
    inject_lock.get(1);
    wait ((tb.dut.tl_h2d.a_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    drv_cmd_val = tb.dut.tl_h2d.a_user.cmd_intg ^ xor_mask;
    force tb.dut.tl_h2d.a_user.cmd_intg = drv_cmd_val;
    fork : wait_cmd_intg_hs begin
      fork
        @(posedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b1 && tb.dut.tl_d2h.a_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.tl_h2d.a_user.cmd_intg;
    inject_lock.put(1);
  endtask

  task automatic inject_data_intg_flip(logic [6:0] xor_mask);
    static logic [6:0] drv_data_val;
    inject_lock.get(1);
    wait ((tb.dut.tl_h2d.a_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    drv_data_val = tb.dut.tl_h2d.a_user.data_intg ^ xor_mask;
    force tb.dut.tl_h2d.a_user.data_intg = drv_data_val;
    fork : wait_data_intg_hs begin
      fork
        @(posedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b1 && tb.dut.tl_d2h.a_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.tl_h2d.a_user.data_intg;
    inject_lock.put(1);
  endtask

  // Corrupt protected H2D command payload fields after u_axi2tlul_cmd_intg_gen encodes cmd_intg
  // (field_sel: 0 = 1-bit a_address, 1 = 2-bit a_address, 2 = a_opcode, 3 = a_mask, 4 = instr_type)
  task automatic inject_cmd_payload_flip(int field_sel);
    static logic [31:0] corrupted_addr;
    static tl_a_op_e    corrupted_opcode;
    static logic [3:0]  corrupted_mask;
    static mubi4_t      corrupted_instr;
    static logic [6:0]  orig_cmd_intg;

    inject_lock.get(1);
    wait ((tb.dut.tl_h2d.a_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    orig_cmd_intg = tb.dut.tl_h2d.a_user.cmd_intg;
    force tb.dut.tl_h2d.a_user.cmd_intg = orig_cmd_intg;
    case (field_sel)
      0: begin
        corrupted_addr = tb.dut.tl_h2d.a_address ^ 32'h0000_0004;
        force tb.dut.tl_h2d.a_address = corrupted_addr;
      end
      1: begin
        corrupted_addr = tb.dut.tl_h2d.a_address ^ 32'h0000_0018;
        force tb.dut.tl_h2d.a_address = corrupted_addr;
      end
      2: begin
        corrupted_opcode = tl_a_op_e'(tb.dut.tl_h2d.a_opcode ^ 3'b001);
        force tb.dut.tl_h2d.a_opcode = corrupted_opcode;
      end
      3: begin
        corrupted_mask = tb.dut.tl_h2d.a_mask ^ 4'b0001;
        force tb.dut.tl_h2d.a_mask = corrupted_mask;
      end
      default: begin
        corrupted_instr = mubi4_t'(tb.dut.tl_h2d.a_user.instr_type ^ 4'b0001);
        force tb.dut.tl_h2d.a_user.instr_type = corrupted_instr;
      end
    endcase
    fork : wait_cmd_payload_hs begin
      fork
        @(posedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b1 && tb.dut.tl_d2h.a_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.tl_h2d.a_address;
    release tb.dut.tl_h2d.a_opcode;
    release tb.dut.tl_h2d.a_mask;
    release tb.dut.tl_h2d.a_user.instr_type;
    release tb.dut.tl_h2d.a_user.cmd_intg;
    inject_lock.put(1);
  endtask

  // Corrupt protected H2D write data payload after u_axi2tlul_cmd_intg_gen encodes data_intg
  task automatic inject_data_payload_flip(logic [31:0] xor_mask);
    static logic [31:0] corrupted_data;
    static logic [6:0]  orig_data_intg;

    inject_lock.get(1);
    wait ((tb.dut.tl_h2d.a_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    orig_data_intg = tb.dut.tl_h2d.a_user.data_intg;
    corrupted_data = tb.dut.tl_h2d.a_data ^ xor_mask;
    force tb.dut.tl_h2d.a_user.data_intg = orig_data_intg;
    force tb.dut.tl_h2d.a_data           = corrupted_data;
    fork : wait_data_payload_hs begin
      fork
        @(posedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b1 && tb.dut.tl_d2h.a_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.tl_h2d.a_data;
    release tb.dut.tl_h2d.a_user.data_intg;
    inject_lock.put(1);
  endtask

  // Corrupt outgoing D2H response SECDED integrity bits on caliptra_ss_uart.tl_o.
  // When suppress_sva is set (expected negative fault checks in normal regressions), pause
  // FpvSecCmTlulRspIntgCheck_A across the single faulted handshake so VCS does not emit an
  // 'Offending' log line while u_tlul_rsp_intg_chk.err_o is still sampled and asserted.
  task automatic inject_d2h_rsp_intg_flip(logic [6:0] xor_mask, bit suppress_sva = 1'b1);
    static logic [6:0] corrupted_rsp_intg;
    inject_lock.get(1);
    wait ((tb.dut.u_caliptra_ss_uart.tl_o.d_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    if (suppress_sva) $assertoff(0, tb.FpvSecCmTlulRspIntgCheck_A);
    corrupted_rsp_intg = tb.dut.u_caliptra_ss_uart.tl_o.d_user.rsp_intg ^ xor_mask;
    force tb.dut.u_caliptra_ss_uart.tl_o.d_user.rsp_intg = corrupted_rsp_intg;
    fork : wait_d2h_rsp_hs begin
      fork
        @(posedge clk_i iff (tb.dut.u_caliptra_ss_uart.tl_o.d_valid === 1'b1 &&
                             tb.dut.tl_h2d.d_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.u_caliptra_ss_uart.tl_o.d_user.rsp_intg;
    if (suppress_sva) $asserton(0, tb.FpvSecCmTlulRspIntgCheck_A);
    inject_lock.put(1);
  endtask

  // Corrupt outgoing D2H read data payload after u_rsp_intg_gen encodes data_intg
  task automatic inject_d2h_data_payload_flip(logic [31:0] xor_mask, bit suppress_sva = 1'b1);
    static logic [31:0] corrupted_d_data;
    static logic [6:0]  orig_d_data_intg;
    inject_lock.get(1);
    wait ((tb.dut.u_caliptra_ss_uart.tl_o.d_valid === 1'b1) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    if (suppress_sva) $assertoff(0, tb.FpvSecCmTlulRspIntgCheck_A);
    orig_d_data_intg = tb.dut.u_caliptra_ss_uart.tl_o.d_user.data_intg;
    corrupted_d_data = tb.dut.u_caliptra_ss_uart.tl_o.d_data ^ xor_mask;
    force tb.dut.u_caliptra_ss_uart.tl_o.d_user.data_intg = orig_d_data_intg;
    force tb.dut.u_caliptra_ss_uart.tl_o.d_data           = corrupted_d_data;
    fork : wait_d2h_data_hs begin
      fork
        @(posedge clk_i iff (tb.dut.u_caliptra_ss_uart.tl_o.d_valid === 1'b1 &&
                             tb.dut.tl_h2d.d_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.u_caliptra_ss_uart.tl_o.d_data;
    release tb.dut.u_caliptra_ss_uart.tl_o.d_user.data_intg;
    if (suppress_sva) $asserton(0, tb.FpvSecCmTlulRspIntgCheck_A);
    inject_lock.put(1);
  endtask

  // Inject a 1-cycle spurious single-bit write-enable fault on an actual u_reg.*_we net while the
  // bus is idle (en_i == 0), exercising reg_we_check[2] combinational fan-in and en_chk detection.
  task automatic inject_spurious_idle_we();
    inject_lock.get(1);
    fork : wait_idle_we_start begin
      fork
        @(negedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b0 &&
                             tb.dut.u_caliptra_ss_uart.u_reg.reg_we === 1'b0));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    force tb.dut.u_caliptra_ss_uart.u_reg.intr_test_we = 1'b1;
    fork : wait_idle_we_end begin
      fork
        @(posedge clk_i);
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    release tb.dut.u_caliptra_ss_uart.u_reg.intr_test_we;
    inject_lock.put(1);
  endtask

  // Inject a simultaneous second write-enable net (selected by second_reg_idx among the 8 writable
  // CSRs in reg_we_check[11:0]) during an active CSR write (en_i == 1), exercising
  // caliptra_prim_onehot_check err_tree collision detection across every reachable tree level.
  task automatic inject_active_multibit_we(int second_reg_idx = 9);
    inject_lock.get(1);
    wait ((tb.dut.tl_h2d.a_valid === 1'b1 &&
           tb.dut.u_caliptra_ss_uart.u_reg.reg_we === 1'b1 &&
           tb.dut.u_caliptra_ss_uart.u_reg.addrmiss === 1'b0) || !rst_ni);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    #1ps;
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    case (second_reg_idx)
      0:       force tb.dut.u_caliptra_ss_uart.u_reg.intr_state_we   = 1'b1;
      1:       force tb.dut.u_caliptra_ss_uart.u_reg.intr_enable_we  = 1'b1;
      2:       force tb.dut.u_caliptra_ss_uart.u_reg.intr_test_we    = 1'b1;
      3:       force tb.dut.u_caliptra_ss_uart.u_reg.ctrl_we         = 1'b1;
      6:       force tb.dut.u_caliptra_ss_uart.u_reg.wdata_we        = 1'b1;
      7:       force tb.dut.u_caliptra_ss_uart.u_reg.fifo_ctrl_we    = 1'b1;
      11:      force tb.dut.u_caliptra_ss_uart.u_reg.timeout_ctrl_we = 1'b1;
      default: force tb.dut.u_caliptra_ss_uart.u_reg.ovrd_we         = 1'b1;
    endcase
    fork : wait_active_we_hs begin
      fork
        @(posedge clk_i iff (tb.dut.tl_h2d.a_valid === 1'b1 && tb.dut.tl_d2h.a_ready === 1'b1));
        wait (!rst_ni);
      join_any
      disable fork;
    end join
    #1ps;
    case (second_reg_idx)
      0:       release tb.dut.u_caliptra_ss_uart.u_reg.intr_state_we;
      1:       release tb.dut.u_caliptra_ss_uart.u_reg.intr_enable_we;
      2:       release tb.dut.u_caliptra_ss_uart.u_reg.intr_test_we;
      3:       release tb.dut.u_caliptra_ss_uart.u_reg.ctrl_we;
      6:       release tb.dut.u_caliptra_ss_uart.u_reg.wdata_we;
      7:       release tb.dut.u_caliptra_ss_uart.u_reg.fifo_ctrl_we;
      11:      release tb.dut.u_caliptra_ss_uart.u_reg.timeout_ctrl_we;
      default: release tb.dut.u_caliptra_ss_uart.u_reg.ovrd_we;
    endcase
    inject_lock.put(1);
  endtask

  task automatic exercise_pre_intg_corners();
    inject_spurious_idle_we();
  endtask

  function automatic logic get_ctrl_tx();
    return tb.dut.u_caliptra_ss_uart.u_reg.ctrl_tx_qs;
  endfunction

  function automatic logic get_ovrd_txen();
    return tb.dut.u_caliptra_ss_uart.u_reg.ovrd_txen_qs;
  endfunction

  function automatic void set_cdc_rand_delay_en(bit en);
    tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled = en;
  endfunction

  function automatic void set_force_status_rxidle(bit en);
    if (en) begin
      force tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_uart_idle = 1'b1;
    end else begin
      release tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_uart_idle;
    end
  endfunction

  // Inject a valid serial UART frame directly onto DUT cio_tx_o while CTRL.TX == 0 to verify
  // that uart_monitor and uart_scoreboard catch unexpected TX traffic even when TX is disabled.
  task automatic inject_spurious_tx_frame(byte data, realtime bit_period,
                                          bit en_parity, bit odd_parity);
    static logic drv_tx_bit;
    bit          parity_bit;
    inject_lock.get(1);
    if (!rst_ni) begin
      inject_lock.put(1);
      return;
    end
    parity_bit = (^data) ^ odd_parity;

    // Start bit (0)
    drv_tx_bit = 1'b0;
    force tb.dut.u_caliptra_ss_uart.cio_tx_o = drv_tx_bit;
    fork : wait_spurious_start begin
      fork
        #(bit_period);
        wait (!rst_ni);
      join_any
      disable fork;
    end join

    // 8 LSB-first data bits
    for (int i = 0; i < 8 && rst_ni; i++) begin
      drv_tx_bit = data[i];
      force tb.dut.u_caliptra_ss_uart.cio_tx_o = drv_tx_bit;
      fork : wait_spurious_data begin
        fork
          #(bit_period);
          wait (!rst_ni);
        join_any
        disable fork;
      end join
    end

    // Optional parity bit
    if (en_parity && rst_ni) begin
      drv_tx_bit = parity_bit;
      force tb.dut.u_caliptra_ss_uart.cio_tx_o = drv_tx_bit;
      fork : wait_spurious_parity begin
        fork
          #(bit_period);
          wait (!rst_ni);
        join_any
        disable fork;
      end join
    end

    // Stop bit (1)
    if (rst_ni) begin
      drv_tx_bit = 1'b1;
      force tb.dut.u_caliptra_ss_uart.cio_tx_o = drv_tx_bit;
      fork : wait_spurious_stop begin
        fork
          #(bit_period);
          wait (!rst_ni);
        join_any
        disable fork;
      end join
    end

    release tb.dut.u_caliptra_ss_uart.cio_tx_o;
    inject_lock.put(1);
  endtask

  // UART-local self-test helper to pause/resume AxiAwPayloadKnown_A on tb.axi_write_req_if
  // without adding test-only $assertoff hooks to the shared axi_agent interface.
  function void set_aw_payload_known_assert(bit enable);
    if (enable) begin
      $asserton(0, tb.axi_write_req_if.AxiAwPayloadKnown_A);
    end else begin
      $assertoff(0, tb.axi_write_req_if.AxiAwPayloadKnown_A);
    end
  endfunction

  initial begin
    if ($test$plusargs("force_rxidle_stuck_1")) begin
      force tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.rx_uart_idle = 1'b1;
    end
  end

  initial begin
    if ($test$plusargs("force_rtl_sva_x_fault")) begin
      @(posedge rst_ni);
      wait (tb.axi_if.awvalid === 1'b1 && rst_ni === 1'b1);
      #1ps;
      force tb.dut.u_caliptra_ss_uart.cio_tx_o            = 1'bx;
      force tb.dut.u_caliptra_ss_uart.intr_tx_watermark_o = 1'bx;
      force tb.axi_if.awcache                             = 4'hx;
      @(posedge clk_i);
      #1ps;
      release tb.dut.u_caliptra_ss_uart.cio_tx_o;
      release tb.dut.u_caliptra_ss_uart.intr_tx_watermark_o;
      release tb.axi_if.awcache;
    end
    if ($test$plusargs("force_csr_status_reset_fault")) begin
      force tb.dut.u_caliptra_ss_uart.u_reg.ctrl_tx_qs = 1'b1;
    end
  end
endinterface
