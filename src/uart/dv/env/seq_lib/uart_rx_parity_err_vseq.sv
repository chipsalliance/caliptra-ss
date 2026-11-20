// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test rx parity error
// cross rx/tx watermark/overflow with parity error in this seq
class uart_rx_parity_err_vseq extends uart_fifo_overflow_vseq;
  `uvm_object_utils(uart_rx_parity_err_vseq)

  `uvm_object_new

  int total_parity_err_count;
  int total_parity_injected;
  int rx_bytes_sent_in_run;

  constraint en_parity_c {
    en_parity == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      1        :/ 2,
      [2:32]   :/ 2,
      [33:100] :/ 2
    };
  }

  virtual task pre_start();
    super.pre_start();
    skip_rx_parity_err_clear = 1'b1;
    total_parity_err_count   = 0;
    total_parity_injected    = 0;
    rx_bytes_sent_in_run     = 0;
  endtask

  virtual task uart_init();
    super.uart_init();
    rx_bytes_sent_in_run = 0;
  endtask

  virtual task send_rx_byte(byte data);
    bit inject_pe;
    bit [TL_DW-1:0] intr_val;
    rx_bytes_sent_in_run++;
    inject_pe = ($urandom_range(0, 4) == 0); // 20%
    // Guarantee at least one parity error is injected before the run finishes.
    if (total_parity_injected == 0 && rx_bytes_sent_in_run >= num_rx_bytes) begin
      inject_pe = 1'b1;
    end
    if (inject_pe) begin
      total_parity_injected++;
      cfg.m_uart_agent_cfg.en_rx_checks = 0; // scope exclusion only to parity-error byte
    end
    drive_rx_error_byte(.parity_err(inject_pe),
                        .frame_err (0),
                        .data      (data));
    if (inject_pe) begin
      cfg.m_uart_agent_cfg.en_rx_checks = en_rx;
    end

    if (inject_pe && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
        ral.ctrl.rx.get_mirrored_value() == 1'b1 &&
        ral.ctrl.parity_en.get_mirrored_value() == 1'b1) begin
      cfg.clk_rst_vif.wait_clks(20);
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        csr_rd(.ptr(ral.intr_state), .value(intr_val));
        if (!cfg.under_reset && cfg.clk_rst_vif.rst_n && intr_val[RxParityErr]) begin
          total_parity_err_count++;
          // Clear it via W1C
          csr_wr(.ptr(ral.intr_state), .value(1 << RxParityErr));
        end
      end
    end
  endtask

  virtual task post_start();
    if (this.get_type_name() == "uart_rx_parity_err_vseq" && do_apply_reset && !cfg.under_reset) begin
      `DV_CHECK_GT(total_parity_injected, 0, "Verify parity errors were injected")
      `DV_CHECK_GT(total_parity_err_count, 0, "Verify RX parity error interrupt was triggered during parity error test")
      `uvm_info(`gfn, $sformatf("Verified RX parity error interrupt occurred %0d times (injected %0d)!",
                 total_parity_err_count, total_parity_injected), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_rx_parity_err_vseq
