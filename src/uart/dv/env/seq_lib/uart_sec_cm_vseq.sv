// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: sec_cm_bus_integrity (uart_sec_cm / uart_sec_cm_vseq)
// Verify TileLink bus integrity & one-hot write-enable countermeasures end-to-end:
// - Spurious idle WE (`en_i == 0`) and active multi-bit WE (`en_i == 1`) via real `u_reg.*_we` nets.
// - H2D command & data SECDED 1-bit and 2-bit ECC / payload fault injection.
// - Architectural RX FIFO byte preservation on faulted `RDATA` reads (`rw.status != UVM_IS_OK`).
// - Outgoing D2H `rsp_intg` and `data_intg` SECDED negative fault checks (`u_tlul_rsp_intg_chk` /
//   `FpvSecCmTlulRspIntgCheck_A`).
// - Sticky `intg_err_o` persistence across clock cycles and valid reads, post-reset recovery, and
//   monotonic fault-detection counter verification across resets.

class uart_sec_cm_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_sec_cm_vseq)

  `uvm_object_new

  virtual task init_uart_cfg();
    en_tx                  = 1'b1;
    en_rx                  = 1'b1;
    en_tx_monitor_checks   = 1'b1;
    en_rx_monitor_checks   = 1'b1;
    baud_rate              = BaudRate115200;
    en_parity              = 1'b0;
    odd_parity             = 1'b0;
    en_noise_filter        = 1'b0;
    uart_period_glitch_pct = 0;
    uart_init();
  endtask

  task body();
    uvm_reg_data_t prev_val, new_val, read_val, fst_val, dut_rdata;
    bit            uncaught_d2h_fault = $test$plusargs("inject_uncaught_d2h_intg_fault");

    `uvm_info(`gfn, "Starting uart_sec_cm_vseq: Bus Integrity Verification", UVM_LOW)
    cfg.sec_cm_vif.clear_monotonic_counters();

    // Step 1: Initialize UART and establish known register values
    init_uart_cfg();
    void'(ral.ctrl.predict(ral.ctrl.get()));
    prev_val = ral.ctrl.get();
    `uvm_info(`gfn, $sformatf("Baseline: ral.ctrl = 0x%08x, intg_err_o = %0b", prev_val, cfg.sec_cm_vif.intg_error), UVM_LOW)
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "Initial intg_error should be 0")

    // Exercise UART Core Override & System Loopback (uart_core.sv lines 220 & 222)
    `uvm_info(`gfn, "--- Testing UART Core Override & System Loopback ---", UVM_LOW)
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0001)); // txen=1
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0000)); // txen=0
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0010)); // slpbk=1 (bit 4)
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000));

    // Exercise all 8 writeable registers via normal AXI writes so u_prim_reg_we_check
    // valid one-hot decode (en_i=1, oh_i=(1<<b), addr_i=b) is covered by real stimulus
    csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test),    .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl),         .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.wdata),        .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl),    .value(32'h0000_0003), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd),         .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // -------------------------------------------------------------------------
    // Test 0A: Spurious single-bit WE while bus is idle (en_i == 0, en_chk via u_reg.intr_test_we)
    // -------------------------------------------------------------------------
    `uvm_info(`gfn, "--- Test 0A: Spurious Idle Write-Enable Fault (en_i == 0) ---", UVM_LOW)
    cfg.sec_cm_vif.inject_spurious_idle_we();
    cfg.clk_rst_vif.wait_clks(2);
    `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_we_err, 1'b1,
                 "u_prim_reg_we_check.err_o must assert on spurious idle u_reg.intr_test_we fault")
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                 "DUT must assert intg_err_o on spurious idle u_reg.intr_test_we fault")
    // Verify sticky persistence across subsequent clock cycles and valid bus read before reset
    cfg.clk_rst_vif.wait_clks(10);
    csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                 "intg_err_o must remain sticky across valid reads after spurious idle WE fault")
    apply_reset("HARD");
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error must clear after reset following spurious idle WE fault")

    // -------------------------------------------------------------------------
    // Test 0B: Simultaneous multi-bit WE during active writes across all 7 writable
    //          binary-tree collision pairs in caliptra_prim_onehot_check (levels 3, 2, 1, 0)
    // -------------------------------------------------------------------------
    `uvm_info(`gfn, "--- Test 0B: Active Multi-Bit Write-Enable Binary-Tree Fault Sweep (en_i == 1) ---", UVM_LOW)
    begin
      // Pairs of (active_csr, forced_second_reg_we_check_idx):
      // [0,1], [2,3], [6,7] -> level-3 leaf pairs
      // [9,11], [0,2]       -> level-2 subtree pairs
      // [0,6]               -> level-1 subtree pair
      // [2,9]               -> level-0 root pair
      uvm_reg target_regs[7] = '{ral.intr_state, ral.intr_test, ral.wdata,
                                 ral.ovrd,       ral.intr_state, ral.intr_state,
                                 ral.intr_test};
      int second_idxs[7]     = '{1, 3, 7, 11, 2, 6, 9};
      foreach (target_regs[p_i]) begin
        fork
          cfg.sec_cm_vif.inject_active_multibit_we(second_idxs[p_i]);
          csr_wr(.ptr(target_regs[p_i]), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_we_err, 1'b1,
                     $sformatf("u_prim_reg_we_check.err_o must assert on active multi-bit WE pair %0d (%0s + idx %0d)",
                               p_i, target_regs[p_i].get_name(), second_idxs[p_i]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                     $sformatf("DUT must assert intg_err_o on active multi-bit WE pair %0d", p_i))
        cfg.clk_rst_vif.wait_clks(10);
        csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                     $sformatf("intg_err_o must remain sticky across valid reads after multi-bit WE pair %0d", p_i))
        apply_reset("HARD");
        ral.reset("HARD");
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0,
                     $sformatf("intg_error must clear after reset following multi-bit WE pair %0d", p_i))
      end
    end

    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    init_uart_cfg();
    void'(ral.ctrl.predict(ral.ctrl.get()));
    prev_val = ral.ctrl.get();

    // =========================================================================
    // Test 1: Inject 1-bit & 2-bit flips into TileLink Command Integrity (cmd_intg)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 1: Testing Command Integrity Fault Injection ---", UVM_LOW)
    begin
      logic [6:0] cmd_masks[8] = '{7'b000_0001, 7'b000_0010, 7'b000_0100, 7'b000_1000,
                                   7'b001_0000, 7'b010_0000, 7'b100_0000, 7'b100_0001};
      foreach (cmd_masks[m_idx]) begin
        logic [6:0] xor_mask = cmd_masks[m_idx];
        `uvm_info(`gfn, $sformatf("Injecting cmd_intg fault mask=0x%02x", xor_mask), UVM_LOW)
        new_val = 32'h0000_0000;
        fork
          cfg.sec_cm_vif.inject_cmd_intg_flip(xor_mask);
          csr_wr(.ptr(ral.ctrl), .value(new_val), .predict(1'b0), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);

        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on cmd_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert during handshake on cmd_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, $sformatf("All register write/read side effects must be suppressed on cmd_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d_error, 1'b1, $sformatf("DUT must assert TL-UL d_error on cmd_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_bresp, 2'b10, $sformatf("AXI bresp must be SLVERR (2'b10) on cmd_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.get_ctrl_tx(), 1'b1, $sformatf("ral.ctrl.tx must retain original value on cmd_intg fault (0x%02x)", xor_mask))

        cfg.clk_rst_vif.wait_clks(10);
        csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(read_val, prev_val, $sformatf("ral.ctrl must remain intact (0x%08x) after cmd_intg fault (0x%02x)", prev_val, xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("intg_err_o must persist after subsequent valid read on cmd_intg fault (0x%02x)", xor_mask))

        apply_reset("HARD");
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")

        init_uart_cfg();
        void'(ral.ctrl.predict(ral.ctrl.get()));
        prev_val = ral.ctrl.get();
      end
    end

    // =========================================================================
    // Test 2: Inject 1-bit & 2-bit flips into TileLink Data Integrity (data_intg)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 2: Testing Data Integrity Fault Injection ---", UVM_LOW)
    begin
      logic [6:0] data_masks[8] = '{7'b000_0001, 7'b000_0010, 7'b000_0100, 7'b000_1000,
                                    7'b001_0000, 7'b010_0000, 7'b100_0000, 7'b100_0001};
      foreach (data_masks[m_idx]) begin
        logic [6:0] xor_mask = data_masks[m_idx];
        `uvm_info(`gfn, $sformatf("Injecting data_intg fault mask=0x%02x", xor_mask), UVM_LOW)
        new_val = 32'h0000_0003;
        fork
          cfg.sec_cm_vif.inject_data_intg_flip(xor_mask);
          csr_wr(.ptr(ral.ovrd), .value(new_val), .predict(1'b0), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);

        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert during handshake on data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, $sformatf("All register write/read side effects must be suppressed on data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d_error, 1'b1, $sformatf("DUT must assert TL-UL d_error on data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_bresp, 2'b10, $sformatf("AXI bresp must be SLVERR (2'b10) on data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.get_ovrd_txen(), 1'b0, $sformatf("ral.ovrd.txen must retain original value on data_intg fault (0x%02x)", xor_mask))

        cfg.clk_rst_vif.wait_clks(10);
        csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(read_val[1:0], 2'b00, $sformatf("ral.ovrd must remain intact (0x0) after data_intg fault (0x%02x)", xor_mask))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("intg_err_o must persist after subsequent valid read on data_intg fault (0x%02x)", xor_mask))

        apply_reset("HARD");
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")

        init_uart_cfg();
      end
    end

    // =========================================================================
    // Test 2B: Inject 1-bit & 2-bit Payload Faults on Protected H2D Command & Data Fields
    // =========================================================================
    `uvm_info(`gfn, "--- Test 2B: Testing Protected H2D Command & Data Payload Fault Injection ---", UVM_LOW)
    for (int fld = 0; fld < 5; fld++) begin
      void'(ral.ctrl.predict(ral.ctrl.get()));
      prev_val = ral.ctrl.get();
      fork
        cfg.sec_cm_vif.inject_cmd_payload_flip(fld);
        csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
      join
      cfg.clk_rst_vif.wait_clks(2);
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                   $sformatf("DUT must assert intg_err_o on H2D cmd payload fault (fld=%0d)", fld))
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1,
                   $sformatf("u_chk.err_o must assert during handshake on H2D cmd payload fault (fld=%0d)", fld))
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0,
                   $sformatf("All register write/read side effects must be suppressed on H2D cmd payload fault (fld=%0d)", fld))
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_d_error, 1'b1,
                   $sformatf("DUT must assert TL-UL d_error on H2D cmd payload fault (fld=%0d)", fld))
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_bresp, 2'b10,
                   $sformatf("AXI bresp must be SLVERR on H2D cmd payload fault (fld=%0d)", fld))
      `DV_CHECK_EQ(cfg.sec_cm_vif.get_ctrl_tx(), 1'b1,
                   $sformatf("ral.ctrl.tx must retain original value on H2D cmd payload fault (fld=%0d)", fld))
      csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
      `DV_CHECK_EQ(read_val, prev_val,
                   $sformatf("ral.ctrl must remain intact (0x%08x) after H2D cmd payload fault (fld=%0d)", prev_val, fld))
      apply_reset("HARD");
      cfg.clk_rst_vif.wait_clks(10);
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")
      init_uart_cfg();
    end

    begin
      logic [31:0] data_xor_masks[2] = '{32'h0000_0001, 32'h0000_0003};
      foreach (data_xor_masks[m]) begin
        fork
          cfg.sec_cm_vif.inject_data_payload_flip(data_xor_masks[m]);
          csr_wr(.ptr(ral.ovrd), .value(32'h0000_0003), .predict(1'b0), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                     $sformatf("DUT must assert intg_err_o on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1,
                     $sformatf("u_chk.err_o must assert during handshake on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0,
                     $sformatf("All register write/read side effects must be suppressed on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d_error, 1'b1,
                     $sformatf("DUT must assert TL-UL d_error on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_bresp, 2'b10,
                     $sformatf("AXI bresp must be SLVERR on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        `DV_CHECK_EQ(cfg.sec_cm_vif.get_ovrd_txen(), 1'b0,
                     $sformatf("ral.ovrd.txen must remain 0 on H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(read_val[1:0], 2'b00,
                     $sformatf("ral.ovrd must remain intact (0x0) after H2D a_data payload fault (mask=0x%0h)", data_xor_masks[m]))
        apply_reset("HARD");
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")
        init_uart_cfg();
      end
    end

    // =========================================================================
    // Test 3: Inject bit flip on Read Transactions (status, non-empty rdata, fifo_status, val)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 3: Testing Read Transaction Integrity Fault Injection ---", UVM_LOW)
    begin
      uvm_reg ro_regs[4] = '{ral.status, ral.rdata, ral.fifo_status, ral.val};
      foreach (ro_regs[idx]) begin
        // For RDATA (read-pop side-effect register), pre-load a known RX byte (0xC3) so we
        // verify architecturally that a faulted RDATA read does NOT pop the RX FIFO and that
        // uart_scoreboard rolls back its speculative pre_read pop cleanly.
        if (ro_regs[idx] == ral.rdata) begin
          send_rx_byte(8'hC3);
          reset_aware_simple_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0),
                                      .spinwait_delay_ns(500), .timeout_ns(50_000_000));
          csr_rd(.ptr(ral.fifo_status), .value(fst_val));
          `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fst_val), 1,
                       "RX FIFO must hold 1 pending byte (0xC3) before faulted RDATA read")
        end

        fork
          cfg.sec_cm_vif.inject_cmd_intg_flip(7'h01);
          csr_rd(.ptr(ro_regs[idx]), .value(read_val), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);
        // Check 1 (Detection): intg_err_o asserted and bus returns TL-UL d_error / AXI SLVERR
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, "DUT must assert intg_err_o on read transaction cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, "u_chk.err_o must assert during handshake on read cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Read side-effect enables must be suppressed on read cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d_error, 1'b1, "DUT must assert TL-UL d_error on read transaction cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_rresp, 2'b10, "AXI rresp must be SLVERR (2'b10) on read transaction cmd_intg fault")

        if (ro_regs[idx] == ral.rdata) begin
          csr_rd(.ptr(ral.fifo_status), .value(fst_val));
          `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fst_val), 1,
                       "Faulted RDATA read must preserve rxlvl == 1 in RX FIFO")
          csr_rd(.ptr(ral.rdata), .value(dut_rdata), .check(UVM_CHECK));
          `DV_CHECK_EQ(dut_rdata[7:0], 8'hC3,
                       "Subsequent valid RDATA read must return preserved RX byte (0xC3)")
          csr_rd(.ptr(ral.fifo_status), .value(fst_val));
          `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fst_val), 0,
                       "RX FIFO must drain to rxlvl == 0 after subsequent valid RDATA read")
        end

        // Check 2 (Persistence): intg_err_o remains asserted across subsequent clock cycles and valid reads
        cfg.clk_rst_vif.wait_clks(10);
        csr_rd(.ptr(ral.status), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, "intg_err_o must persist across subsequent valid reads until reset")

        // Check 3 (Recovery): Recover DUT via reset
        apply_reset("HARD");
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")
        init_uart_cfg();
      end
    end

    // =========================================================================
    // Test 3B: Outgoing D2H Response & Data SECDED Negative Fault Verification
    //          (u_rsp_intg_gen -> u_tlul_rsp_intg_chk / FpvSecCmTlulRspIntgCheck_A)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 3B: Testing Outgoing D2H rsp_intg & data_intg SECDED Fault Detection ---", UVM_LOW)
    begin
      logic [6:0]  rsp_masks[2] = '{7'h01, 7'h03};
      logic [31:0] d2h_masks[2] = '{32'h0000_0001, 32'h0000_0003};

      foreach (rsp_masks[m]) begin
        fork
          cfg.sec_cm_vif.inject_d2h_rsp_intg_flip(rsp_masks[m], .suppress_sva(!uncaught_d2h_fault));
          csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d2h_rsp_intg_err, 1'b1,
                     $sformatf("u_tlul_rsp_intg_chk.err_o must assert on D2H rsp_intg fault (0x%0h)", rsp_masks[m]))
      end

      foreach (d2h_masks[m]) begin
        fork
          cfg.sec_cm_vif.inject_d2h_data_payload_flip(d2h_masks[m], .suppress_sva(!uncaught_d2h_fault));
          csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
        join
        cfg.clk_rst_vif.wait_clks(2);
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_d2h_rsp_intg_err, 1'b1,
                     $sformatf("u_tlul_rsp_intg_chk.err_o must assert on D2H d_data fault (0x%0h)", d2h_masks[m]))
      end

      // Confirm FpvSecCmTlulRspIntgCheck_A is re-armed and clean D2H responses pass without error
      csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
      cfg.clk_rst_vif.wait_clks(2);
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_d2h_rsp_intg_err, 1'b0,
                   "Clean D2H response after Test 3B must pass u_tlul_rsp_intg_chk with err_o == 0")
    end

    // =========================================================================
    // Test 4: AXI Sub-word Accesses, Corner Cases, Toggles & FSM Transitions
    // (Executed naturally via uart_axi_toggle_vseq without forces)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 4: Running uart_axi_toggle_vseq for AXI Toggles, Subwords, 64-bit Size & FSM ---", UVM_LOW)
    begin
      uart_axi_toggle_vseq axi_seq = uart_axi_toggle_vseq::type_id::create("axi_seq");
      axi_seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(axi_seq)
      axi_seq.start(p_sequencer, this);
    end

    // =========================================================================
    // Test 5: UART RX Start Bit Glitch Abort (via VIP glitch driver, no forces)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 5: Testing UART RX Start Bit Glitch Abort via VIP ---", UVM_LOW)
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    begin
      uint uart_clk_period_ps = cfg.m_uart_agent_cfg.vif.uart_clk_period / 1ps;
      repeat (20) begin
        cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
            .max_glitch_ps(uart_clk_period_ps * 0.4),
            .stable_ps_after_glitch(uart_clk_period_ps * 0.8));
      end
      cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    end

    // =========================================================================
    // Test 6: Comprehensive CSR Bit-Toggle Coverage
    // =========================================================================
    `uvm_info(`gfn, "--- Test 6: Testing Comprehensive CSR Bit-Toggle Coverage ---", UVM_LOW)
    exercise_csr_bit_toggles();

    // =========================================================================
    // Test 7: Verify post-reset graceful recovery & TileLink bus responsiveness
    // =========================================================================
    `uvm_info(`gfn, "--- Test 7: Verifying Post-Reset Graceful Recovery ---", UVM_LOW)
    apply_reset("HARD");
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error must clear after hardware reset")

    // Reset RAL mirror and check all register defaults
    ral.reset("HARD");
    begin
      uvm_reg all_regs[$];
      ral.get_registers(all_regs);
      foreach (all_regs[i]) begin
        if (all_regs[i].get_rights() != "WO") begin
          csr_rd(.ptr(all_regs[i]), .value(read_val), .check(UVM_CHECK));
        end
      end
    end

    // Verify basic bidirectional transmission works cleanly after recovery
    init_uart_cfg();
    send_tx_byte(8'hA5);
    cfg.clk_rst_vif.wait_clks(1);
    spinwait_txidle();
    cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
    send_rx_byte(8'h5A);
    reset_aware_simple_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0),
                                .spinwait_delay_ns(500), .timeout_ns(50_000_000));
    csr_rd(.ptr(ral.rdata), .value(dut_rdata));
    `DV_CHECK_EQ(dut_rdata[7:0], 8'h5A, "Recovered UART RX received byte check")

    // Verify monotonic fault-detection counters preserved across all resets in this sequence:
    // - 27 H2D SECDED faults: 8 cmd_intg + 8 data_intg + 5 cmd_payload + 2 data_payload + 4 RO reads
    // - 8 reg_we_check faults: 1 spurious idle WE (en_i==0) + 7 simultaneous multi-bit WE tree pairs (en_i==1)
    // - 4 D2H SECDED faults: 2 rsp_intg + 2 d_data payload
    `uvm_info(`gfn, $sformatf(
        "SEC_CM_FAULT_SUMMARY: total_h2d_intg_err=%0d (cmd_1b=%0d, cmd_2b=%0d, data_1b=%0d, data_2b=%0d), total_reg_we_err=%0d, total_d2h_intg_err=%0d",
        cfg.sec_cm_vif.total_h2d_intg_err_cnt,
        cfg.sec_cm_vif.total_cmd_single_err_cnt,
        cfg.sec_cm_vif.total_cmd_multibit_err_cnt,
        cfg.sec_cm_vif.total_data_single_err_cnt,
        cfg.sec_cm_vif.total_data_multibit_err_cnt,
        cfg.sec_cm_vif.total_reg_we_err_cnt,
        cfg.sec_cm_vif.total_d2h_intg_err_cnt), UVM_LOW)
    `DV_CHECK_EQ(cfg.sec_cm_vif.total_h2d_intg_err_cnt, 27,
                 "Monotonic H2D SECDED fault counter must equal all 27 injected H2D faults")
    `DV_CHECK_GE(cfg.sec_cm_vif.total_cmd_single_err_cnt, 15,
                 "u_chk.u_chk.err_o[0] single-bit command ECC errors must be observed")
    `DV_CHECK_GE(cfg.sec_cm_vif.total_cmd_multibit_err_cnt, 2,
                 "u_chk.u_chk.err_o[1] multi-bit command ECC errors must be observed")
    `DV_CHECK_GE(cfg.sec_cm_vif.total_data_single_err_cnt, 8,
                 "u_data_chk.err_o[0] single-bit data ECC errors must be observed")
    `DV_CHECK_GE(cfg.sec_cm_vif.total_data_multibit_err_cnt, 2,
                 "u_data_chk.err_o[1] multi-bit data ECC errors must be observed")
    `DV_CHECK_EQ(cfg.sec_cm_vif.total_reg_we_err_cnt, 8,
                 "Monotonic reg_we_check fault counter must equal 1 idle + 7 active multi-bit WE tree faults")
    `DV_CHECK_EQ(cfg.sec_cm_vif.total_d2h_intg_err_cnt, 4,
                 "Monotonic D2H SECDED fault counter must equal all 4 injected D2H faults")

    `uvm_info(`gfn, "uart_sec_cm_vseq passed all TileLink bus integrity protection checks!", UVM_LOW)
  endtask : body

  // Comprehensive CSR bit toggling task across writable register fields
  task exercise_csr_bit_toggles();
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    // 1. timeout_ctrl: Toggle all 24 bits (val[23:0]) and enable bit
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h00FF_FFFF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h80AA_AAAA), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0055_5555), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // 2. fifo_ctrl: Toggle rxilvl[4:2] and txilvl[7:5] through all combinations
    for (int t = 0; t < 8; t++) begin
      for (int r = 0; r < 8; r++) begin
        csr_wr(.ptr(ral.fifo_ctrl), .value((t << 5) | (r << 2)), .predict(1'b0), .check(UVM_NO_CHECK));
      end
    end
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_00FC), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_00A8), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0054), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // 3. intr_enable & intr_test: Toggle all 9 interrupt bits with enable=1 so intr_o triggers
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(5);
    csr_wr(.ptr(ral.intr_state), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(5);
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0155), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_00AA), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // 4. ovrd: Toggle txen and txval
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0003), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0002), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0001), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // 5. ctrl: Toggle tx, rx, nf, slpbk, llpbk, parity_en, parity_odd (bits [7:0])
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_00FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_00AA), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0055), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
  endtask

endclass : uart_sec_cm_vseq

// Alias class for factory instantiation
class uart_sec_cm extends uart_sec_cm_vseq;
  `uvm_object_utils(uart_sec_cm)
  `uvm_object_new
endclass : uart_sec_cm
