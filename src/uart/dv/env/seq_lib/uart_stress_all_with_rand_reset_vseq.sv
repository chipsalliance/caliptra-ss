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
      bit reset_ongoing;
      uart_stress_all_vseq uart_vseq;
      `uvm_info(`gfn, $sformatf("Starting iteration %0d/%0d of stress_all_with_rand_reset", i, num_trans), UVM_LOW)
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
          reset_ongoing = 1;
          cfg.under_reset = 1;
          `uvm_info(`gfn, $sformatf("Asserting async rst_ni for iteration %0d/%0d (delay=%0d clks)", i, num_trans, delay), UVM_LOW)
          cfg.clk_rst_vif.apply_reset(.reset_width_clks($urandom_range(20, 100)));
          cfg.under_reset = 0;
          reset_ongoing = 0;
          `uvm_info(`gfn, $sformatf("Deasserted async rst_ni for iteration %0d/%0d", i, num_trans), UVM_LOW)
        end
      join_any
      if (p_sequencer.uart_sequencer_h != null) begin
        p_sequencer.uart_sequencer_h.stop_sequences();
      end
      disable fork;
      #1ps;

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

    // Reset RAL mirror to default values
    ral.reset("HARD");

    // Read back registers and verify reset defaults
    ral.get_registers(all_regs);
    foreach (all_regs[i]) begin
      if (all_regs[i].get_rights() != "WO") begin
        csr_rd(.ptr(all_regs[i]), .value(rdata), .check(UVM_CHECK));
      end
    end

    // Verify basic configuration and transaction work after reset
    uart_init();
    `uvm_info(`gfn, "Post-reset check passed: IP recovered gracefully and all registers at default values", UVM_LOW)
  endtask : check_after_reset

endclass : uart_stress_all_with_rand_reset_vseq

class uart_stress_all_with_rand_reset extends uart_stress_all_with_rand_reset_vseq;
  `uvm_object_utils(uart_stress_all_with_rand_reset)
  `uvm_object_new
endclass : uart_stress_all_with_rand_reset
