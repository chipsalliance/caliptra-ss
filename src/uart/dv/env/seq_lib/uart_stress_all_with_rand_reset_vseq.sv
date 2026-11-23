// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: stress_all_with_reset (uart_stress_all_with_rand_reset)
// Verify resilience against asynchronous hardware reset.
// - Assert rst_ni at random intervals during active bidirectional traffic.
// - IP recovers gracefully after reset deassertion.
// - All registers return to reset defaults without hanging the bus.
class uart_stress_all_with_rand_reset_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_stress_all_with_rand_reset_vseq)

  rand uint delay;

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[5:10]};
  }

  constraint delay_c {
    delay dist {
      1                   :/ 1,
      [2      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :100_000]   :/ 1
    };
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit          reset_ongoing          = 1'b0;
      bit          reset_asserted_in_fork = 1'b0;
      int unsigned rst_clks               = $urandom_range(20, 100);
      int unsigned pre_kill_rst_clks      = rst_clks / 2;
      uart_stress_all_vseq uart_vseq;
      `uvm_info(`gfn, $sformatf("Starting iteration %0d/%0d of stress_all_with_rand_reset", i, num_trans), UVM_LOW)
      fork
        begin : isolation_fork
          fork
            begin : seq_wo_reset
              uart_vseq = uart_stress_all_vseq::type_id::create("uart_stress_all_vseq");
              uart_vseq.do_apply_reset = 0;
              uart_vseq.set_sequencer(p_sequencer);
              `DV_CHECK_RANDOMIZE_FATAL(uart_vseq)
              uart_vseq.start(p_sequencer);
              // once reset starts, need to wait until reset is done
              wait (reset_ongoing == 0);
              `uvm_info(`gfn, $sformatf("Finished sequence run %0d/%0d", i, num_trans), UVM_LOW)
            end

            begin : reset
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay,
                                                 delay dist {
                                                     1                   :/ 1,
                                                     [2      :100]       :/ 1,
                                                     [101    :10_000]    :/ 8,
                                                     [10_001 :100_000]   :/ 1
                                                 };)
              cfg.clk_rst_vif.wait_clks(delay);
              reset_ongoing          = 1'b1;
              cfg.under_reset        = 1'b1;
              reset_asserted_in_fork = 1'b1;
              `uvm_info(`gfn, $sformatf("Asserting async rst_ni for iteration %0d/%0d (delay=%0d clks, width=%0d clks)",
                                        i, num_trans, delay, rst_clks), UVM_LOW)
              // Assert rst_ni low and hold part of reset_width_clks inside fork so mid-transfer resets
              // are exercised, then exit join_any and kill seq_wo_reset WHILE rst_ni is still held low
              // so stale sequence threads cannot enqueue post-reset CSR writes before disable fork.
              cfg.clk_rst_vif.drive_rst_pin(1'b0);
              cfg.clk_rst_vif.wait_clks(pre_kill_rst_clks);
            end
          join_any
          // Drain in-flight CSR accesses that abort under reset before killing child threads so
          // no killed thread leaks a uvm_reg m_atomic semaphore.
          fork
            begin : drain_csr_fork
              fork
                csr_utils_pkg::wait_no_outstanding_access();
                cfg.clk_rst_vif.wait_clks(100);
              join_any
              disable fork;
            end : drain_csr_fork
          join
          if (p_sequencer.uart_sequencer_h != null) begin
            p_sequencer.uart_sequencer_h.stop_sequences();
          end
          if (ral.default_map.get_sequencer() != null) begin
            ral.default_map.get_sequencer().stop_sequences();
          end
          disable fork;
        end : isolation_fork
      join
      #1ps;

      if (reset_asserted_in_fork) begin
        cfg.clk_rst_vif.drive_rst_pin(1'b0);
        cfg.clk_rst_vif.wait_clks(rst_clks - pre_kill_rst_clks);
        cfg.clk_rst_vif.drive_rst_pin(1'b1);
        cfg.clk_rst_vif.wait_clks(5);
        cfg.under_reset = 1'b0;
        reset_ongoing   = 1'b0;
        `uvm_info(`gfn, $sformatf("Deasserted async rst_ni for iteration %0d/%0d", i, num_trans), UVM_LOW)
      end else begin
        cfg.under_reset = 1'b1;
        `uvm_info(`gfn, $sformatf("Asserting async rst_ni at end of iteration %0d/%0d", i, num_trans), UVM_LOW)
        cfg.clk_rst_vif.apply_reset(.reset_width_clks(rst_clks));
        cfg.under_reset = 1'b0;
        `uvm_info(`gfn, $sformatf("Deasserted async rst_ni at end of iteration %0d/%0d", i, num_trans), UVM_LOW)
      end

      check_after_reset();
    end
  endtask : body

  // Task to check registers return to defaults and bus is alive
  virtual task check_after_reset();
    uvm_reg all_regs[$];
    uvm_reg_data_t rdata;

    `uvm_info(`gfn, "Post-reset check: verifying register reset defaults and bus responsiveness", UVM_LOW)
    // Ensure reset is deasserted if it was interrupted
    cfg.clk_rst_vif.drive_rst_pin(1'b1);
    // Wait after reset deassertion for clocks to stabilize
    cfg.clk_rst_vif.wait_clks(20);

    // Clear any stale parent_sequence left on the shared adapter if a sub-sequence was killed mid-reset
    if (ral.default_map.get_adapter() != null) begin
      ral.default_map.get_adapter().parent_sequence = null;
    end

    // Reset RAL mirror to default values
    ral.reset("HARD");

    // Read back registers and verify reset defaults
    ral.get_registers(all_regs);
    foreach (all_regs[i]) begin
      if (all_regs[i].get_rights() != "WO") begin
        csr_rd(.ptr(all_regs[i]), .value(rdata), .check(UVM_CHECK));
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(rdata, all_regs[i].get_reset(),
                       $sformatf("Reset default mismatch on %0s", all_regs[i].get_name()))
        end
      end
    end

    // Verify interrupt state and all interrupt output pins are cleared after reset
    check_interrupts(rdata);
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(cfg.intr_vif.pins[NumUartIntr-1:0], '0,
                   "All interrupt output pins must be 0 after reset")
    end

    // Verify basic configuration and transaction work after reset
    cfg.en_scb_checks = 1'b1;
    cfg.m_uart_agent_cfg.re_enable_chk_mon_on_reset = 1'b1;
    cfg.m_uart_agent_cfg.en_tx_monitor = 1'b1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1'b1;
    cfg.disable_scb_rx_parity_check = 1'b0;
    cfg.disable_scb_rx_frame_check  = 1'b0;
    if (cfg.sec_cm_vif != null) cfg.sec_cm_vif.set_cdc_rand_delay_en(1'b1);
    uart_init();
    `uvm_info(`gfn, "Post-reset check passed: IP recovered gracefully and all registers at default values", UVM_LOW)
  endtask : check_after_reset

endclass : uart_stress_all_with_rand_reset_vseq

class uart_stress_all_with_rand_reset extends uart_stress_all_with_rand_reset_vseq;
  `uvm_object_utils(uart_stress_all_with_rand_reset)
  `uvm_object_new
endclass : uart_stress_all_with_rand_reset
