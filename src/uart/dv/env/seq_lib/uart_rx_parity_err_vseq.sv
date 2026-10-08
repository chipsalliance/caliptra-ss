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

  constraint en_parity_c {
    en_parity == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  virtual task pre_start();
    super.pre_start();
    total_parity_err_count = 0;
    total_parity_injected = 0;
  endtask

  virtual task send_rx_byte(byte data);
    bit inject_pe;
    bit [TL_DW-1:0] intr_val;
    cfg.m_uart_agent_cfg.en_rx_checks = 0; // disable rx checks in monitor
    inject_pe = ($urandom_range(0, 4) == 0); // 20%
    if (inject_pe) total_parity_injected++;
    drive_rx_error_byte(.parity_err(inject_pe),
                        .frame_err (0),
                        .data      (data));
    cfg.m_uart_agent_cfg.en_rx_checks = 1;

    if (inject_pe && ral.ctrl.rx.get_mirrored_value() == 1'b1 && ral.ctrl.parity_en.get_mirrored_value() == 1'b1) begin
      cfg.clk_rst_vif.wait_clks(20);
      csr_rd(.ptr(ral.intr_state), .value(intr_val));
      if (intr_val[RxParityErr]) begin
        total_parity_err_count++;
        // Clear it via W1C
        csr_wr(.ptr(ral.intr_state), .value(1 << RxParityErr));
      end
    end
  endtask

  virtual task post_start();
    if (this.get_type_name() == "uart_rx_parity_err_vseq") begin
      `DV_CHECK_GT(total_parity_injected, 0, "Verify parity errors were injected")
      `DV_CHECK_GT(total_parity_err_count, 0, "Verify RX parity error interrupt was triggered during parity error test")
      `uvm_info(`gfn, $sformatf("Verified RX parity error interrupt occurred %0d times (injected %0d)!",
                 total_parity_err_count, total_parity_injected), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_rx_parity_err_vseq
