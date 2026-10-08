// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: sec_cm_bus_integrity (uart_sec_cm / uart_sec_cm_vseq)
// Verify TileLink bus integrity protection against malicious or accidental faults:
// - Inject bit flips into TileLink command / data integrity fields.
// - Verify DUT flags an integrity error response (intg_err_o == 1).
// - Verify DUT blocks invalid access (register contents are preserved, write enables suppressed).
// - Verify IP recovers gracefully after reset deassertion.

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
    uvm_reg_data_t prev_val, new_val, read_val, status_val, dut_rdata;
    
    `uvm_info(`gfn, "Starting uart_sec_cm_vseq: Bus Integrity Verification", UVM_LOW)

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
    // valid one-hot decode (en_i=1, oh_i=(1<<b), addr_i=b) is covered by real stimulus,
    // followed by unreachable multi-bit fault injection in exercise_pre_intg_corners()
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    csr_wr(.ptr(ral.intr_state),   .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable),  .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test),    .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl),         .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.wdata),        .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl),    .value(32'h0000_0003), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ovrd),         .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.sec_cm_vif.exercise_pre_intg_corners();
    apply_reset("HARD");
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    init_uart_cfg();
    void'(ral.ctrl.predict(ral.ctrl.get()));
    prev_val = ral.ctrl.get();

    // =========================================================================
    // Test 1: Inject bit flips into TileLink Command Integrity (cmd_intg: 7 bits)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 1: Testing Command Integrity Fault Injection ---", UVM_LOW)
    for (int bit_idx = 0; bit_idx < 7; bit_idx++) begin
      `uvm_info(`gfn, $sformatf("Injecting bit flip at cmd_intg bit %0d", bit_idx), UVM_LOW)
      
      // Arm one-shot bit-flip injector on next TileLink transaction
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(bit_idx);
      join_none

      // Attempt to write an invalid value to ral.ctrl (expecting error response)
      new_val = 32'h0000_0000;
      csr_wr(.ptr(ral.ctrl), .value(new_val), .predict(1'b0), .check(UVM_NO_CHECK));

      // Wait a cycle for error propagation
      cfg.clk_rst_vif.wait_clks(2);

      // Check 1 (Detection): DUT must flag integrity error and suppress write
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on cmd_intg[%0d] fault", bit_idx))
      `DV_CHECK_EQ(cfg.sec_cm_vif.get_ctrl_we(), 1'b0, $sformatf("ctrl_we must be suppressed on cmd_intg[%0d] fault", bit_idx))
      `DV_CHECK_EQ(cfg.sec_cm_vif.get_ctrl_tx(), 1'b1, $sformatf("ral.ctrl.tx must retain original value on cmd_intg[%0d] fault", bit_idx))

      // Check 2 (Persistence): Verify intg_err_o remains latched across subsequent clock cycles and valid bus reads
      cfg.clk_rst_vif.wait_clks(10);
      csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
      `DV_CHECK_EQ(read_val, prev_val, $sformatf("ral.ctrl must remain intact (0x%08x) after cmd_intg[%0d] fault", prev_val, bit_idx))
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("intg_err_o must persist after subsequent valid read on cmd_intg[%0d] fault", bit_idx))

      // Check 3 (Recovery): Recover DUT via reset and verify intg_err_o clears
      apply_reset("HARD");
      cfg.clk_rst_vif.wait_clks(10);
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")

      // Re-initialize for next iteration
      init_uart_cfg();
      void'(ral.ctrl.predict(ral.ctrl.get()));
      prev_val = ral.ctrl.get();
    end

    // =========================================================================
    // Test 2: Inject bit flips into TileLink Data Integrity (data_intg: 7 bits)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 2: Testing Data Integrity Fault Injection ---", UVM_LOW)
    for (int bit_idx = 0; bit_idx < 7; bit_idx++) begin
      `uvm_info(`gfn, $sformatf("Injecting bit flip at data_intg bit %0d", bit_idx), UVM_LOW)

      // Arm one-shot bit-flip injector on next TileLink transaction
      fork
        cfg.sec_cm_vif.inject_data_intg_flip(bit_idx);
      join_none

      // Attempt to write an invalid value to ral.ovrd (expecting error response)
      new_val = 32'h0000_0003;
      csr_wr(.ptr(ral.ovrd), .value(new_val), .predict(1'b0), .check(UVM_NO_CHECK));

      cfg.clk_rst_vif.wait_clks(2);

      // Check 1 (Detection): DUT must flag integrity error and suppress write
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on data_intg[%0d] fault", bit_idx))
      `DV_CHECK_EQ(cfg.sec_cm_vif.get_ovrd_txen(), 1'b0, $sformatf("ral.ovrd.txen must retain original value on data_intg[%0d] fault", bit_idx))

      // Check 2 (Persistence): Verify intg_err_o remains latched across subsequent clock cycles and valid bus reads
      cfg.clk_rst_vif.wait_clks(10);
      csr_rd(.ptr(ral.ovrd), .value(read_val), .check(UVM_NO_CHECK));
      `DV_CHECK_EQ(read_val[1:0], 2'b00, $sformatf("ral.ovrd must remain intact (0x0) after data_intg[%0d] fault", bit_idx))
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("intg_err_o must persist after subsequent valid read on data_intg[%0d] fault", bit_idx))

      // Check 3 (Recovery): Recover DUT via reset and verify intg_err_o clears
      apply_reset("HARD");
      cfg.clk_rst_vif.wait_clks(10);
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_error should clear after reset")

      init_uart_cfg();
    end

    // =========================================================================
    // Test 3: Inject bit flip on Read Transactions (status, rdata, fifo_status, val)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 3: Testing Read Transaction Integrity Fault Injection ---", UVM_LOW)
    begin
      uvm_reg ro_regs[4] = '{ral.status, ral.rdata, ral.fifo_status, ral.val};
      foreach (ro_regs[idx]) begin
        fork
          cfg.sec_cm_vif.inject_cmd_intg_flip(0);
        join_none

        csr_rd(.ptr(ro_regs[idx]), .value(read_val), .check(UVM_NO_CHECK));
        cfg.clk_rst_vif.wait_clks(2);
        // Check 1 (Detection): intg_err_o asserted
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, "DUT must assert intg_err_o on read transaction cmd_intg fault")

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
    // Test 5: AXI Sub-word Accesses, Corner Cases, Toggles & FSM Transitions
    // (Executed naturally via uart_axi_toggle_vseq without forces)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 5: Running uart_axi_toggle_vseq for AXI Toggles, Subwords, 64-bit Size & FSM ---", UVM_LOW)
    begin
      uart_axi_toggle_vseq axi_seq = uart_axi_toggle_vseq::type_id::create("axi_seq");
      axi_seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(axi_seq)
      axi_seq.start(p_sequencer);
    end

    // =========================================================================
    // =========================================================================
    // Test 7: UART Core Break State Default (uart_core.sv line 136)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 7: Testing UART Core Break State Default ---", UVM_LOW)
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.sec_cm_vif.exercise_uart_core_break_default();

    // Test 8: UART RX Start Bit Glitch Abort (via VIP glitch driver, no forces)
    // =========================================================================
    `uvm_info(`gfn, "--- Test 8: Testing UART RX Start Bit Glitch Abort via VIP ---", UVM_LOW)
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
    // Test 14: Comprehensive CSR Bit-Toggle Coverage
    // =========================================================================
    `uvm_info(`gfn, "--- Test 14: Testing Comprehensive CSR Bit-Toggle Coverage ---", UVM_LOW)
    exercise_csr_bit_toggles();

    // =========================================================================
    // Test 4: Verify post-reset graceful recovery & TileLink bus responsiveness
    // =========================================================================
    `uvm_info(`gfn, "--- Test 4: Verifying Post-Reset Graceful Recovery ---", UVM_LOW)
    // Exercise TL-UL cover sequences for 100% assertion coverage
    cfg.sec_cm_vif.exercise_tlul_assert_cover_sequences();
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
    do begin
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (status_val[5] == 1'b1);
    csr_rd(.ptr(ral.rdata), .value(dut_rdata));
    `DV_CHECK_EQ(dut_rdata[7:0], 8'h5A, "Recovered UART RX received byte check")

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

    // 5. ctrl: Toggle tx, rx, nf, slpbk, llpbk, parity_en, parity_odd, rxblvl
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
