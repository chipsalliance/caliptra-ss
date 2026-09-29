// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test TX override feature through uart.OVRD and check the pin
class uart_tx_ovrd_vseq extends uart_smoke_vseq;
  `uvm_object_utils(uart_tx_ovrd_vseq)

  int total_ovrd_txval_0_seen;
  int total_ovrd_txval_1_seen;

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    total_ovrd_txval_0_seen = 0;
    total_ovrd_txval_1_seen = 0;
  endtask

  // add orvd test on tx and make sure no side-effect on rx
  virtual task send_tx_byte(byte data);
    bit en_ovrd;
    bit txval;
    bit exp;
    bit test_vals[2] = '{1'b0, 1'b1};

    // Wait until previous TX is completely idle on both DUT and VIP
    csr_spinwait(.ptr(ral.status.txidle), .exp_data(1'b1));
    cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
    cfg.clk_rst_vif.wait_clks(2);

    // disable monitor as monitor can't handle override
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;

    // Explicitly verify both 0 and 1 override values
    foreach (test_vals[k]) begin
      ral.ovrd.txen.set(1'b1);
      ral.ovrd.txval.set(test_vals[k]);
      csr_wr(.ptr(ral.ovrd), .value(ral.ovrd.get()), .check(UVM_NO_CHECK), .predict(1));
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, test_vals[k],
                     $sformatf("UART TX pin must follow ovrd.txval=%0d when ovrd.txen=1", test_vals[k]))
      end
      if (test_vals[k] == 1'b0) total_ovrd_txval_0_seen++;
      else                     total_ovrd_txval_1_seen++;
    end

    repeat ($urandom_range(1, 5)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(en_ovrd)
      `DV_CHECK_STD_RANDOMIZE_FATAL(txval)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_tx_trans)

      if (en_ovrd) exp = txval;
      else         exp = 1;
      ral.ovrd.txen.set(en_ovrd);
      ral.ovrd.txval.set(txval);
      csr_wr(.ptr(ral.ovrd), .value(ral.ovrd.get()), .check(UVM_NO_CHECK), .predict(1));
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) `DV_CHECK_EQ(cfg.m_uart_agent_cfg.vif.uart_tx, exp)
      if (en_ovrd) begin
        if (txval == 1'b0) total_ovrd_txval_0_seen++;
        else               total_ovrd_txval_1_seen++;
      end
      cfg.clk_rst_vif.wait_clks(dly_to_next_tx_trans);
    end

    // disable ovrd
    ral.ovrd.txen.set(0);
    ral.ovrd.txval.set(0);
    csr_wr(.ptr(ral.ovrd), .value(0), .check(UVM_NO_CHECK), .predict(1));
    cfg.clk_rst_vif.wait_clks(2);
    #(cfg.m_uart_agent_cfg.vif.uart_clk_period * 2);
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;

    super.send_tx_byte(data);
  endtask

  virtual task post_start();
    if (this.get_type_name() == "uart_tx_ovrd_vseq") begin
      `DV_CHECK_GT(total_ovrd_txval_0_seen, 0, "Verify TX override 0 was tested")
      `DV_CHECK_GT(total_ovrd_txval_1_seen, 0, "Verify TX override 1 was tested")
      `uvm_info(`gfn, $sformatf("Verified TX override: txval=0 (%0d times), txval=1 (%0d times)",
                                total_ovrd_txval_0_seen, total_ovrd_txval_1_seen), UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_tx_ovrd_vseq
