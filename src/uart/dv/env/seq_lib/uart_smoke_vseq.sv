// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_reg_parent_seq extends uvm_sequence_base;
  `uvm_object_utils(uart_reg_parent_seq)
  function new(string name = "uart_reg_parent_seq");
    super.new(name);
  endfunction
endclass

class uart_scb_corrupt_catcher extends uvm_report_catcher;
  `uvm_object_utils(uart_scb_corrupt_catcher)

  bit expect_tx_err;
  bit expect_rx_err;
  bit expect_status_err;
  bit expect_fifo_lvl_err;
  bit expect_intr_err;
  bit expect_unexp_tx_err;
  int caught_tx_err_cnt;
  int caught_rx_err_cnt;
  int caught_status_err_cnt;
  int caught_fifo_lvl_err_cnt;
  int caught_intr_err_cnt;
  int caught_unexp_tx_err_cnt;

  function new(string name = "uart_scb_corrupt_catcher");
    super.new(name);
  endfunction

  static function bit str_contains(string s, string sub);
    if (sub.len() == 0 || s.len() < sub.len()) return 0;
    for (int i = 0; i <= s.len() - sub.len(); i++) begin
      if (s.substr(i, i + sub.len() - 1) == sub) return 1;
    end
    return 0;
  endfunction

  virtual function action_e catch();
    if (get_severity() == UVM_ERROR) begin
      string msg = get_message();
      if (expect_tx_err && str_contains(msg, "TX item mismatch!")) begin
        caught_tx_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_TX_CORRUPT_CHK");
        set_message($sformatf("Caught expected scoreboard TX mismatch error: %s", msg));
        return THROW;
      end
      if (expect_rx_err && str_contains(msg, "rdata read comparison")) begin
        caught_rx_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_RX_CORRUPT_CHK");
        set_message($sformatf("Caught expected scoreboard RX mismatch error: %s", msg));
        return THROW;
      end
      if (expect_status_err &&
          (str_contains(msg, "check rx_idle fail") ||
           str_contains(msg, "check rx_full fail") ||
           str_contains(msg, "check rx_empty fail") ||
           str_contains(msg, "check tx_full fail") ||
           str_contains(msg, "check tx_empty fail") ||
           str_contains(msg, "check tx_idle fail"))) begin
        caught_status_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_STATUS_CORRUPT_CHK");
        set_message($sformatf("Caught expected scoreboard STATUS mismatch error: %s", msg));
        return THROW;
      end
      if (expect_fifo_lvl_err &&
          (str_contains(msg, "txlvl mismatch") || str_contains(msg, "rxlvl mismatch"))) begin
        caught_fifo_lvl_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_FIFO_LVL_CORRUPT_CHK");
        set_message($sformatf("Caught expected scoreboard FIFO_STATUS mismatch error: %s", msg));
        return THROW;
      end
      if (expect_intr_err && str_contains(msg, "Interrupt:")) begin
        caught_intr_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_INTR_CORRUPT_CHK");
        set_message($sformatf("Caught expected scoreboard INTR_STATE mismatch error: %s", msg));
        return THROW;
      end
      if (expect_unexp_tx_err &&
          str_contains(msg, "Received unexpected TX item from DUT (tx_enabled=0)")) begin
        caught_unexp_tx_err_cnt++;
        set_severity(UVM_INFO);
        set_id("SCB_UNEXP_TX_DISABLED_CHK");
        set_message($sformatf("Caught expected scoreboard unexpected-TX-while-disabled error: %s", msg));
        return THROW;
      end
    end
    return THROW;
  endfunction
endclass

// simple smoke test with both en_tx and en_rx on
// process one item at a time for TX and RX
class uart_smoke_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_smoke_vseq)

  constraint baud_rate_extra_c {
    baud_rate inside {BaudRate115200, BaudRate230400, BaudRate256Kbps, BaudRate1Mbps};
  }

  constraint num_trans_c {
    num_trans == 2;
  }

  constraint num_tx_bytes_c {
    num_tx_bytes == 5;
  }

  constraint num_rx_bytes_c {
    num_rx_bytes == 5;
  }

  constraint en_tx_c {
    en_tx == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  constraint glitch_pct_c {
    uart_period_glitch_pct == 0;
  }

  `uvm_object_new

  virtual task body();
    bit [TL_DW-1:0] intr_test_val;
    do_interrupt = 0;
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();
      `uvm_info(`gfn, $sformatf("starting smoke run %0d/%0d", i, num_trans), UVM_MEDIUM)
      // Read INTR_TEST (WO register) to verify read returns zero and exercise addr_hit[2] logic
      csr_rd(.ptr(ral.intr_test), .value(intr_test_val));
      `DV_CHECK_EQ(intr_test_val, 0, "INTR_TEST must read back zero")

      // Exercise sub-word accesses for AXI coverage (8-bit byte and 16-bit halfword)
      begin
        uvm_reg_bus_op rw;
        uvm_sequencer_base sqr = ral.default_map.get_sequencer();
        uvm_reg_adapter adapter = ral.default_map.get_adapter();
        uvm_sequence_item item;
        uvm_sequence_item rsp_item;

        for (int k = 0; k < 4; k++) begin
          if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) break;
          // 8-bit byte read (axsize = 0)
          rw.kind = UVM_READ;
          rw.addr = ral.status.get_address();
          rw.n_bits = 8;
          rw.byte_en = 4'b0001;
          item = adapter.reg2bus(rw);
          start_item(item, .sequencer(sqr));
          finish_item(item);
          get_response(rsp_item);
          adapter.bus2reg(rsp_item, rw);
          if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
            `DV_CHECK_EQ(rw.status, UVM_IS_OK, "8-bit byte read failed")
          end else begin
            break;
          end

          if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) break;
          // 16-bit halfword read (axsize = 1)
          rw.kind = UVM_READ;
          rw.addr = ral.ctrl.get_address();
          rw.n_bits = 16;
          rw.byte_en = 4'b0011;
          item = adapter.reg2bus(rw);
          start_item(item, .sequencer(sqr));
          finish_item(item);
          get_response(rsp_item);
          adapter.bus2reg(rsp_item, rw);
          if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
            `DV_CHECK_EQ(rw.status, UVM_IS_OK, "16-bit halfword read failed")
          end else begin
            break;
          end
        end

        // Verify 32-bit partial writes propagate item.m_rw.byte_en into strobes,
        // leave unselected bytes unchanged, and establish CSR storage isolation.
        if (this.get_type_name() == "uart_smoke_vseq" && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
          verify_partial_writes_and_csr_isolation();
        end
      end

      // Exercise UVM RAL adapter parent_sequence assertions (uvm_reg_map::do_write & do_read)
      // Gated on do_apply_reset so random-reset disable-fork cannot kill mid-mutation and leak
      // parent_seq onto the shared adapter.
      if (do_apply_reset && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        uvm_reg_adapter adapter = ral.default_map.get_adapter();
        if (adapter != null) begin
          uart_reg_parent_seq parent_seq = uart_reg_parent_seq::type_id::create("parent_seq");
          uvm_reg_data_t val;
          adapter.parent_sequence = parent_seq;
          csr_wr(.ptr(ral.ovrd), .value('0));
          csr_rd(.ptr(ral.ovrd), .value(val));
          adapter.parent_sequence = null;
        end
      end

      // Exercise back-to-back interleaved read/write transactions for sub2tlul FSM coverage
      for (int m = 0; m < 4; m++) begin
        fork
          begin
            uvm_reg_data_t rd_val;
            csr_rd(.ptr(ral.ctrl), .value(rd_val));
          end
          begin
            csr_wr(.ptr(ral.ovrd), .value('0));
          end
        join
        fork
          begin
            csr_wr(.ptr(ral.ovrd), .value('0));
          end
          begin
            uvm_reg_data_t rd_val;
            csr_rd(.ptr(ral.status), .value(rd_val));
          end
        join
      end
      process_tx();
      process_rx();
      if (this.get_type_name() == "uart_smoke_vseq" && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        verify_rx_tx_fifo_isolation();
        if (i == num_trans && do_apply_reset) begin
          verify_scb_tx_rx_corruption_detection();
        end
      end
      process_remaining_data();
      if (this.get_type_name() == "uart_smoke_vseq" && i == num_trans && do_apply_reset &&
          !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        verify_unexpected_tx_while_disabled_detection();
      end
      `uvm_info(`gfn, $sformatf("finished smoke run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

  // Verify 32-bit partial writes propagate item.m_rw.byte_en into strobes,
  // leave unselected bytes unchanged, and establish CSR storage isolation.
  virtual task verify_partial_writes_and_csr_isolation();
    uvm_reg_bus_op     rw;
    uvm_sequencer_base sqr             = ral.default_map.get_sequencer();
    uvm_reg_adapter    adapter         = ral.default_map.get_adapter();
    uvm_reg_data_t     orig_fifo_ctrl  = ral.fifo_ctrl.get_mirrored_value();
    uvm_reg_data_t     orig_intr_en    = ral.intr_enable.get_mirrored_value();
    uvm_reg_data_t     orig_timeout_val= ral.timeout_ctrl.get_mirrored_value();
    uvm_reg_data_t     rd_val;
    uvm_sequence_item  item, rsp_item;
    bit [3:0]          partial_masks[7]= '{4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0011, 4'b1100, 4'b0000};

    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // 1. FIFO_CTRL (UART_PERMIT = 4'b0001):
    // Write byte 0 with byte_en = 4'b0001, then write with byte 0 unselected (byte_en = 4'b1110)
    // and verify byte 0 remains unchanged.
    rw.kind    = UVM_WRITE;
    rw.addr    = ral.fifo_ctrl.get_address();
    rw.n_bits  = 32;
    rw.byte_en = 4'b0001;
    rw.data    = 32'hDEAD_BE54;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rw.status, UVM_IS_OK, "32-bit partial write (byte_en=4'b0001) to fifo_ctrl must succeed")
    csr_rd(.ptr(ral.fifo_ctrl), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[7:0], 8'h54, "Selected byte 0 of fifo_ctrl must update to 0x54")
    `DV_CHECK_EQ(rd_val[31:8], 24'h0, "Unselected upper bytes [31:8] of fifo_ctrl must remain 0")

    rw.kind    = UVM_WRITE;
    rw.addr    = ral.fifo_ctrl.get_address();
    rw.n_bits  = 32;
    rw.byte_en = 4'b1110;
    rw.data    = 32'h1234_56A8;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rw.status, UVM_NOT_OK, "TL-UL d_error on partial write (byte_en=4'b1110) to fifo_ctrl must return UVM_NOT_OK (BRespSlverr)")
    csr_rd(.ptr(ral.fifo_ctrl), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[7:0], 8'h54, "Unselected byte 0 of fifo_ctrl must remain unchanged (0x54)")

    // 2. INTR_ENABLE (UART_PERMIT = 4'b0011):
    // Write bytes [1:0] with byte_en = 4'b0011, then issue partial write where bytes [1:0] are unselected (4'b1100)
    // and verify unselected bytes remain unchanged.
    rw.kind    = UVM_WRITE;
    rw.addr    = ral.intr_enable.get_address();
    rw.n_bits  = 32;
    rw.byte_en = 4'b0011;
    rw.data    = 32'hCAFE_0155;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rw.status, UVM_IS_OK, "32-bit partial write (byte_en=4'b0011) to intr_enable must succeed")
    csr_rd(.ptr(ral.intr_enable), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[15:0], 16'h0155, "Selected bytes [1:0] of intr_enable must update to 0x0155")
    `DV_CHECK_EQ(rd_val[31:16], 16'h0000, "Unselected upper bytes [3:2] of intr_enable must remain 0")

    rw.kind    = UVM_WRITE;
    rw.addr    = ral.intr_enable.get_address();
    rw.n_bits  = 32;
    rw.byte_en = 4'b1100;
    rw.data    = 32'h0000_00AA;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rw.status, UVM_NOT_OK, "TL-UL d_error on partial write (byte_en=4'b1100) to intr_enable must return UVM_NOT_OK (BRespSlverr)")
    csr_rd(.ptr(ral.intr_enable), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[7:0], 8'h55, "Unselected byte 0 of intr_enable must remain unchanged (0x55)")
    `DV_CHECK_EQ(rd_val[15:8], 8'h01, "Unselected byte 1 of intr_enable must remain unchanged (0x01)")

    // Re-read FIFO_CTRL without reprogramming it after programming INTR_ENABLE with a distinct payload
    // to verify register storage isolation (original 0x54 payload remains intact).
    csr_rd(.ptr(ral.fifo_ctrl), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[7:0], 8'h54, "fifo_ctrl original payload (0x54) must remain intact after programming intr_enable")

    // 3. TIMEOUT_CTRL (UART_PERMIT = 4'b1111):
    // Initialize to 32'h805A_A5C3, issue 32-bit partial writes with each partial byte_en mask,
    // and verify that unselected bytes remain unchanged.
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h805A_A5C3), .predict(1'b1));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    foreach (partial_masks[p_i]) begin
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      rw.kind    = UVM_WRITE;
      rw.addr    = ral.timeout_ctrl.get_address();
      rw.n_bits  = 32;
      rw.byte_en = partial_masks[p_i];
      rw.data    = 32'h0011_2233;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(rw.status, UVM_NOT_OK,
                   $sformatf("TL-UL d_error on partial write (byte_en=4'b%04b) to timeout_ctrl must return UVM_NOT_OK",
                             partial_masks[p_i]))
      csr_rd(.ptr(ral.timeout_ctrl), .value(rd_val), .check(UVM_NO_CHECK));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(rd_val, 32'h805A_A5C3,
                   $sformatf("Rejected partial write (byte_en=4'b%04b) must leave timeout_ctrl unchanged",
                             partial_masks[p_i]))
    end

    // Re-read FIFO_CTRL and INTR_ENABLE again without reprogramming them after programming TIMEOUT_CTRL
    // to verify their original payloads (0x54 and 0x0155) remain intact.
    csr_rd(.ptr(ral.fifo_ctrl), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[7:0], 8'h54, "fifo_ctrl original payload (0x54) must remain intact after programming timeout_ctrl")
    csr_rd(.ptr(ral.intr_enable), .value(rd_val), .check(UVM_NO_CHECK));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rd_val[15:0], 16'h0155, "intr_enable original payload (0x0155) must remain intact after programming timeout_ctrl")

    // Restore original values
    csr_wr(.ptr(ral.fifo_ctrl), .value(orig_fifo_ctrl), .predict(1'b1));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    csr_wr(.ptr(ral.intr_enable), .value(orig_intr_en), .predict(1'b1));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    csr_wr(.ptr(ral.timeout_ctrl), .value(orig_timeout_val), .predict(1'b1));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // 4. Verify TL-UL d_error on unmapped read (0x30) translates to RRespSlverr (UVM_NOT_OK)
    rw.kind    = UVM_READ;
    rw.addr    = 32'h0000_0030;
    rw.n_bits  = 32;
    rw.byte_en = 4'b1111;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(rw.status, UVM_NOT_OK, "TL-UL d_error on unmapped read (0x30) must return UVM_NOT_OK (RRespSlverr)")

    // 5. Verify FIFO partial-word strobe propagation and byte-for-byte transfer on WDATA
    //    (24 bus-write checks + invalid/full-mask negative controls + no-reset follow-up traffic):
    // - 3-byte strobe (4'b0111) and unselected lane-0 strobe (4'b1110) must be rejected (UVM_NOT_OK) without
    //   inserting spurious zero bytes into the TX FIFO.
    // - Full-mask negative control: writing a padded zero byte with 4'b1111 inserts a spurious 8'h00 into the FIFO,
    //   confirming that advertising padding zeros as valid bytes corrupts the stream unless byte enables are masked.
    // - 24 partial-word (byte_en=4'b0001) bus-write checks via write_wdata_with_mask() integrating both bus and
    //   prediction byte enables:
    //   (a) 9-byte payload (01..08, 99) [9 writes] -> final write has {byte_en, data} == 36'h1_0000_0099.
    //   (b) 3-byte payload (11, 22, 33) [3 writes] -> sends exact 11, 22, 33 without padding zeros.
    //   (c) Distinct follow-up transfer without FIFO reset (21, 43, 65, 87) [4 writes] -> starts with 8'h21.
    //   (d) System-loopback 3-byte payload (11, 22, 33) [3 writes] followed immediately without FIFO reset by a
    //       distinct 5-byte follow-up transfer (21, 43, 55, 77, 99) [5 writes] -> RDATA readback verifies first
    //       transfer is 11, 22, 33 and subsequent transfer without reset starts with 8'h21 (not stale 8'h33).
    begin
      byte payload_9b[9]        = '{8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07, 8'h08, 8'h99};
      byte payload_3b[3]        = '{8'h11, 8'h22, 8'h33};
      byte payload_next[4]      = '{8'h21, 8'h43, 8'h65, 8'h87};
      byte payload_lpbk_next[5] = '{8'h21, 8'h43, 8'h55, 8'h77, 8'h99};
      int unsigned prev_tx_cnt  = cfg.scb_tx_compared_cnt;
      int unsigned bus_wr_checks = 0;
      uvm_status_e wr_status;
      bit [TL_DW-1:0] ctrl_val, status_val, lpbk_rdata;

      // Reject unselected lane-0 strobes (4'b0010 and 4'b1110) on WDATA
      rw.kind    = UVM_WRITE;
      rw.addr    = ral.wdata.get_address();
      rw.n_bits  = 32;
      rw.byte_en = 4'b0010;
      rw.data    = 32'h0000_1100;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(rw.status, UVM_NOT_OK, "Unselected lane-0 strobe (4'b0010) to WDATA must return UVM_NOT_OK")

      rw.kind    = UVM_WRITE;
      rw.addr    = ral.wdata.get_address();
      rw.n_bits  = 32;
      rw.byte_en = 4'b1110;
      rw.data    = 32'h0000_2200;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(rw.status, UVM_NOT_OK, "Unselected lane-0 strobe (4'b1110) to WDATA must return UVM_NOT_OK without inserting zero bytes")

      // Full-mask negative control in system loopback:
      // If a caller issues a full-mask (4'b1111) write with lane-0 padding zero (32'h0033_2200),
      // lane 0 (8'h00) is advertised as a valid byte and received as 8'h00 instead of 8'h22.
      csr_rd(.ptr(ral.ctrl), .value(ctrl_val), .check(UVM_NO_CHECK));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      csr_wr(.ptr(ral.ctrl), .value(ctrl_val | (32'h1 << 4)), .predict(1'b1));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

      rw.kind    = UVM_WRITE;
      rw.addr    = ral.wdata.get_address();
      rw.n_bits  = 32;
      rw.byte_en = 4'b1111;
      rw.data    = 32'h0033_2200;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(rw.status, UVM_IS_OK, "Full-mask (4'b1111) negative-control write to WDATA completes on bus")
      spinwait_txidle();
      spinwait_rxidle();
      do begin
        cfg.clk_rst_vif.wait_clks(20);
        csr_rd(.ptr(ral.status), .value(status_val), .check(UVM_NO_CHECK));
      end while (status_val[5] == 1'b1 && !cfg.under_reset);
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      csr_rd(.ptr(ral.rdata), .value(lpbk_rdata), .check(UVM_NO_CHECK));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      `DV_CHECK_EQ(lpbk_rdata[7:0], 8'h00,
                   "Full-mask negative control: advertising lane-0 padding zero with byte_en=4'hf enqueues 0x00 instead of 0x22")
      `DV_CHECK_NE(lpbk_rdata[7:0], 8'h22,
                   "Full-mask negative control: upper byte 0x22 is not selected when lane-0 padding zero is enabled")

      csr_wr(.ptr(ral.ctrl), .value(ctrl_val), .predict(1'b1));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

      // 5a. 9-byte payload ending in 8'h99 (9 bus writes):
      // Verify final partial write has {byte_en, data} == 36'h1_0000_0099 and both bus & prediction use byte_en=4'b0001
      foreach (payload_9b[b_i]) begin
        bit [3:0]  exp_be    = 4'b0001;
        bit [3:0]  obs_wstrb = '0;
        bit [31:0] obs_wdata = '0;
        bit        saw_w_hs  = 1'b0;
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        fork
          write_wdata_with_mask(.data(payload_9b[b_i]), .mask(exp_be), .status(wr_status));
          begin
            @(posedge cfg.m_axi_agent_cfg.write_data_vif.clk_i iff
              ((cfg.m_axi_agent_cfg.write_data_vif.wvalid === 1'b1 &&
                cfg.m_axi_agent_cfg.write_data_vif.wready === 1'b1) || cfg.under_reset));
            if (!cfg.under_reset) begin
              obs_wstrb = cfg.m_axi_agent_cfg.write_data_vif.wstrb[3:0];
              obs_wdata = cfg.m_axi_agent_cfg.write_data_vif.wdata[31:0];
              saw_w_hs  = 1'b1;
            end
          end
        join
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(saw_w_hs, 1'b1, "Expected AXI W handshake during write_wdata_with_mask")
        `DV_CHECK_EQ(obs_wstrb, exp_be,
                     "Observed AXI bus wstrb must match requested byte_en (4'b0001)")
        `DV_CHECK_EQ(obs_wdata[7:0], payload_9b[b_i],
                     "Observed AXI bus wdata[7:0] must match written payload byte")
        if (b_i == 8) begin
          `DV_CHECK_EQ({obs_wstrb, obs_wdata}, 36'h1_0000_0099,
                       "Observed AXI bus final write of 9-byte payload must have {wstrb, wdata} == 36'h1_0000_0099 (not 4'hf)")
        end
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(wr_status, UVM_IS_OK, "Single-byte strobe (4'b0001) write to WDATA must return UVM_IS_OK")
        `DV_CHECK_EQ(ral.wdata.get_mirrored_value()[7:0], payload_9b[b_i],
                     "RAL predicted wdata must match partial-write byte")
        bus_wr_checks++;
        cfg.clk_rst_vif.wait_clks(1);
        spinwait_txidle();
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        `DV_CHECK_EQ(cfg.scb_tx_compared_cnt, prev_tx_cnt + 9,
                     "All 9 bytes of 9-byte payload ending in 0x99 must be verified byte-for-byte in scoreboard")
      end

      // 5b. 3-byte payload (8'h11, 8'h22, 8'h33) [3 bus writes] followed immediately by a distinct
      // 4-byte transfer (8'h21, 8'h43, 8'h65, 8'h87) [4 bus writes] WITHOUT resetting the FIFO:
      foreach (payload_3b[b_i]) begin
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        write_wdata_with_mask(.data(payload_3b[b_i]), .mask(4'b0001), .status(wr_status));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(wr_status, UVM_IS_OK, "Single-byte strobe (4'b0001) write to WDATA must return UVM_IS_OK")
        `DV_CHECK_EQ(ral.wdata.get_mirrored_value()[7:0], payload_3b[b_i],
                     "RAL predicted wdata must match 3-byte transfer payload")
        bus_wr_checks++;
        cfg.clk_rst_vif.wait_clks(1);
        spinwait_txidle();
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        `DV_CHECK_EQ(cfg.scb_tx_compared_cnt, prev_tx_cnt + 12,
                     "Bytes 11, 22, 33 must be transmitted and verified byte-for-byte in scoreboard without spurious zero bytes")
      end

      // Distinct following transfer (8'h21, 8'h43, 8'h65, 8'h87) WITHOUT resetting the FIFO
      foreach (payload_next[b_i]) begin
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        write_wdata_with_mask(.data(payload_next[b_i]), .mask(4'b0001), .status(wr_status));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(wr_status, UVM_IS_OK, "Subsequent transfer write to WDATA without FIFO reset must return UVM_IS_OK")
        `DV_CHECK_EQ(ral.wdata.get_mirrored_value()[7:0], payload_next[b_i],
                     "RAL predicted wdata must match subsequent transfer byte")
        bus_wr_checks++;
        cfg.clk_rst_vif.wait_clks(1);
        spinwait_txidle();
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end
      if (!cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
        `DV_CHECK_EQ(cfg.scb_tx_compared_cnt, prev_tx_cnt + 16,
                     "Subsequent transfer (21, 43, 65, 87) without FIFO reset must start with 0x21 (not stale 0x33) and match in scoreboard")
      end

      // 5c. System-loopback verification of 3-byte transfer (11, 22, 33) [3 bus writes] followed immediately
      // WITHOUT FIFO reset by a distinct 5-byte transfer (21, 43, 55, 77, 99) [5 bus writes], bringing total
      // partial-word bus-write checks to 24 (9 + 3 + 4 + 3 + 5 = 24):
      csr_wr(.ptr(ral.ctrl), .value(ctrl_val | (32'h1 << 4)), .predict(1'b1));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

      foreach (payload_3b[b_i]) begin
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        write_wdata_with_mask(.data(payload_3b[b_i]), .mask(4'b0001), .status(wr_status));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(wr_status, UVM_IS_OK, "Loopback 3-byte transfer write with mask=4'b0001 must return UVM_IS_OK")
        `DV_CHECK_EQ(ral.wdata.get_mirrored_value()[7:0], payload_3b[b_i],
                     "RAL predicted wdata must match loopback 3-byte transfer payload")
        bus_wr_checks++;
        spinwait_txidle();
        spinwait_rxidle();
        do begin
          cfg.clk_rst_vif.wait_clks(20);
          csr_rd(.ptr(ral.status), .value(status_val), .check(UVM_NO_CHECK));
        end while (status_val[5] == 1'b1 && !cfg.under_reset);
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        csr_rd(.ptr(ral.rdata), .value(lpbk_rdata), .check(UVM_NO_CHECK));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(lpbk_rdata[7:0], payload_3b[b_i],
                     $sformatf("Loopback 3-byte transfer byte %0d must match 0x%02x", b_i, payload_3b[b_i]))
      end

      // Immediately run distinct 5-byte transfer (21, 43, 55, 77, 99) WITHOUT resetting the FIFO
      foreach (payload_lpbk_next[b_i]) begin
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        write_wdata_with_mask(.data(payload_lpbk_next[b_i]), .mask(4'b0001), .status(wr_status));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        `DV_CHECK_EQ(wr_status, UVM_IS_OK, "Loopback follow-up transfer write without FIFO reset must return UVM_IS_OK")
        `DV_CHECK_EQ(ral.wdata.get_mirrored_value()[7:0], payload_lpbk_next[b_i],
                     "RAL predicted wdata must match loopback follow-up transfer payload")
        bus_wr_checks++;
        spinwait_txidle();
        spinwait_rxidle();
        do begin
          cfg.clk_rst_vif.wait_clks(20);
          csr_rd(.ptr(ral.status), .value(status_val), .check(UVM_NO_CHECK));
        end while (status_val[5] == 1'b1 && !cfg.under_reset);
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        csr_rd(.ptr(ral.rdata), .value(lpbk_rdata), .check(UVM_NO_CHECK));
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        if (b_i == 0) begin
          `DV_CHECK_EQ(lpbk_rdata[7:0], 8'h21,
                       "Subsequent transfer without FIFO reset must start with expected first byte 0x21 (not stale 0x33)")
        end
        `DV_CHECK_EQ(lpbk_rdata[7:0], payload_lpbk_next[b_i],
                     $sformatf("Loopback follow-up transfer byte %0d without FIFO reset must match 0x%02x",
                               b_i, payload_lpbk_next[b_i]))
      end

      `DV_CHECK_EQ(bus_wr_checks, 24, "All 24 partial-word bus-write checks must complete and pass")

      csr_wr(.ptr(ral.ctrl), .value(ctrl_val), .predict(1'b1));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
      csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1), .predict(1'b1));
      if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
    end
  endtask : verify_partial_writes_and_csr_isolation

  // Verify RX FIFO and TX FIFO storage isolation:
  // Programming and immediately reading each channel independently does not establish storage isolation.
  // 1. Buffer an initial payload (rx_orig_byte = 8'hA5) in the RX FIFO and verify rxlvl == 1.
  // 2. Program the TX FIFO (WDATA) with a distinct payload (tx_distinct_byte = 8'h5A) and transmit it.
  // 3. Read the RX FIFO (RDATA) without reprogramming/resending to RX and verify that rx_orig_byte (8'hA5)
  //    remains intact.
  virtual task verify_rx_tx_fifo_isolation();
    byte rx_orig_byte     = 8'hA5;
    byte tx_distinct_byte = 8'h5A;
    bit [TL_DW-1:0] status_val, fifo_status_val, dut_rdata;

    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    `uvm_info(`gfn, $sformatf("Verifying RX/TX FIFO storage isolation: buffering RX=0x%02x, then transmitting distinct TX=0x%02x",
                              rx_orig_byte, tx_distinct_byte), UVM_LOW)
    send_rx_byte(rx_orig_byte);
    do begin
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (status_val[5] == 1'b1 && !cfg.under_reset);
    if (cfg.under_reset) return;

    csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fifo_status_val), 1,
                   "RX FIFO must hold 1 byte (rx_orig_byte) before programming TX FIFO")
    end

    // Program TX FIFO with distinct payload while rx_orig_byte remains stored in RX FIFO
    send_tx_byte(tx_distinct_byte);
    cfg.clk_rst_vif.wait_clks(1);
    spinwait_txidle();
    cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
    cfg.clk_rst_vif.wait_clks(10);

    // Read RX FIFO without reprogramming/resending to RX and verify original payload remains intact
    csr_rd(.ptr(ral.rdata), .value(dut_rdata));
    if (!cfg.under_reset) begin
      if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
      rx_bytes_read_cnt++;
      `DV_CHECK_EQ(dut_rdata[7:0], rx_orig_byte,
                   "RX FIFO original payload (0xA5) must remain intact after programming TX FIFO with distinct payload (0x5A)")
    end
  endtask : verify_rx_tx_fifo_isolation

  // Verify the scoreboard checks in regression:
  // 1. Clean traffic and register reads pass in the scoreboard (TX, RX, STATUS, FIFO_STATUS, INTR_STATE).
  // 2. Corrupted TX data fails in the scoreboard (triggers "TX item mismatch!" UVM_ERROR).
  // 3. Corrupted RX data fails in the scoreboard (triggers "rdata read comparison" UVM_ERROR).
  // 4. Forcing STATUS.RXIDLE = 1 during an active RX frame fails in the scoreboard ("check rx_idle fail").
  // 5. Corrupted FIFO_STATUS fails in the scoreboard ("rxlvl mismatch" / "txlvl mismatch").
  // 6. Corrupted INTR_STATE fails in the scoreboard ("Interrupt:" UVM_ERROR).
  virtual task verify_scb_tx_rx_corruption_detection();
    uart_scb_corrupt_catcher catcher;
    bit [TL_DW-1:0] status_val, fstatus_val, intr_val, dut_rdata;

    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // Ensure INTR_STATE is sampled on clean traffic before checking comparison counters
    csr_rd(.ptr(ral.intr_state), .value(intr_val));
    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // 1. Verify clean traffic and STATUS/FIFO_STATUS/INTR_STATE predictions passed in the scoreboard
    `DV_CHECK_EQ(cfg.en_scb, 1'b1, "Scoreboard must be enabled")
    `DV_CHECK_GT(cfg.scb_tx_compared_cnt, 0, "Clean TX traffic must pass in the scoreboard")
    `DV_CHECK_GT(cfg.scb_rx_compared_cnt, 0, "Clean RX traffic must pass in the scoreboard")
    `DV_CHECK_GT(cfg.scb_status_compared_cnt, 0,
                 "STATUS must be checked against independent prediction in the scoreboard")
    `DV_CHECK_GT(cfg.scb_fifo_status_compared_cnt, 0,
                 "FIFO_STATUS must be checked against independent prediction in the scoreboard")
    `DV_CHECK_GT(cfg.scb_intr_compared_cnt, 0,
                 "INTR_STATE must be checked against independent prediction in the scoreboard")

    catcher = uart_scb_corrupt_catcher::type_id::create("catcher");
    uvm_report_cb::add(null, catcher);

    // 2. Verify corrupted TX fails in the scoreboard
    `uvm_info(`gfn, "Verifying corrupted TX data fails in the scoreboard", UVM_LOW)
    catcher.expect_tx_err     = 1'b1;
    cfg.inject_scb_tx_corrupt = 1'b1;
    send_tx_byte(8'hA3);
    cfg.clk_rst_vif.wait_clks(1);
    spinwait_txidle();
    cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
    cfg.clk_rst_vif.wait_clks(10);
    cfg.inject_scb_tx_corrupt = 1'b0;
    catcher.expect_tx_err     = 1'b0;
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(catcher.caught_tx_err_cnt, 1,
                   "Corrupted TX data must fail in the scoreboard with TX item mismatch")
    end

    // 3. Verify corrupted RX fails in the scoreboard
    `uvm_info(`gfn, "Verifying corrupted RX data fails in the scoreboard", UVM_LOW)
    catcher.expect_rx_err     = 1'b1;
    cfg.inject_scb_rx_corrupt = 1'b1;
    send_rx_byte(8'h3C);
    do begin
      cfg.clk_rst_vif.wait_clks(50);
      csr_rd(.ptr(ral.status), .value(status_val));
    end while (status_val[5] == 1'b1 && !cfg.under_reset);
    if (!cfg.under_reset) begin
      csr_rd(.ptr(ral.rdata), .value(dut_rdata));
      if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
      rx_bytes_read_cnt++;
    end
    cfg.inject_scb_rx_corrupt = 1'b0;
    catcher.expect_rx_err     = 1'b0;
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(catcher.caught_rx_err_cnt, 1,
                   "Corrupted RX data must fail in the scoreboard with rdata read comparison error")
    end

    // 4. Verify forcing STATUS.RXIDLE = 1 during active RX reception fails in the scoreboard
    if (cfg.sec_cm_vif != null && !$test$plusargs("force_rxidle_stuck_1") && !cfg.under_reset) begin
      `uvm_info(`gfn, "Verifying forced STATUS.RXIDLE=1 during active RX frame fails in the scoreboard", UVM_LOW)
      catcher.expect_status_err = 1'b1;
      cfg.sec_cm_vif.set_force_status_rxidle(1'b1);
      fork
        send_rx_byte(8'h96);
        begin
          bit [TL_DW-1:0] mid_status_val;
          wait (cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == 5 || cfg.under_reset);
          if (!cfg.under_reset) begin
            csr_rd(.ptr(ral.status), .value(mid_status_val));
          end
        end
      join
      cfg.sec_cm_vif.set_force_status_rxidle(1'b0);
      catcher.expect_status_err = 1'b0;
      do begin
        cfg.clk_rst_vif.wait_clks(50);
        csr_rd(.ptr(ral.status), .value(status_val));
      end while (status_val[5] == 1'b1 && !cfg.under_reset);
      if (!cfg.under_reset) begin
        csr_rd(.ptr(ral.rdata), .value(dut_rdata));
        if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
        rx_bytes_read_cnt++;
        `DV_CHECK_EQ(catcher.caught_status_err_cnt, 1,
                     "Forced STATUS.RXIDLE=1 during active RX must fail in the scoreboard with check rx_idle fail")
      end
    end

    // 5. Verify corrupted FIFO_STATUS fails in the scoreboard
    if (!cfg.under_reset) begin
      `uvm_info(`gfn, "Verifying corrupted FIFO_STATUS fails in the scoreboard", UVM_LOW)
      catcher.expect_fifo_lvl_err        = 1'b1;
      cfg.inject_scb_fifo_status_corrupt = 1'b1;
      csr_rd(.ptr(ral.fifo_status), .value(fstatus_val));
      cfg.inject_scb_fifo_status_corrupt = 1'b0;
      catcher.expect_fifo_lvl_err        = 1'b0;
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(catcher.caught_fifo_lvl_err_cnt, 1,
                     "Corrupted FIFO_STATUS must fail in the scoreboard with rxlvl/txlvl mismatch")
      end
    end

    // 6. Verify corrupted INTR_STATE fails in the scoreboard
    if (!cfg.under_reset) begin
      `uvm_info(`gfn, "Verifying corrupted INTR_STATE fails in the scoreboard", UVM_LOW)
      catcher.expect_intr_err     = 1'b1;
      cfg.inject_scb_intr_corrupt = 1'b1;
      csr_rd(.ptr(ral.intr_state), .value(intr_val));
      cfg.inject_scb_intr_corrupt = 1'b0;
      catcher.expect_intr_err     = 1'b0;
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(catcher.caught_intr_err_cnt, NumUartIntr,
                     "Corrupted INTR_STATE must fail in the scoreboard on all 9 interrupt bits")
      end
    end

    uvm_report_cb::delete(null, catcher);
  endtask : verify_scb_tx_rx_corruption_detection

  // Verify that initializing UART via uart_init() with en_tx == 0 keeps TX checks enabled and
  // catches any unexpected serial TX frame emitted while CTRL.TX == 0.
  virtual task verify_unexpected_tx_while_disabled_detection();
    uart_scb_corrupt_catcher catcher;
    bit uncaught_neg_mode = $test$plusargs("force_spurious_tx_while_disabled");

    if (cfg.sec_cm_vif == null || cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    `uvm_info(`gfn, "Verifying unexpected TX frame while initialized with en_tx=0 fails in the scoreboard", UVM_LOW)
    en_tx                = 1'b0;
    en_rx                = 1'b1;
    en_tx_monitor_checks = 1'b1;
    uart_init();
    `DV_CHECK_EQ(cfg.m_uart_agent_cfg.en_tx_checks, 1'b1,
                 "uart_init() with en_tx=0 must keep cfg.m_uart_agent_cfg.en_tx_checks enabled")

    if (!uncaught_neg_mode) begin
      catcher = uart_scb_corrupt_catcher::type_id::create("unexp_tx_catcher");
      catcher.expect_unexp_tx_err = 1'b1;
      uvm_report_cb::add(null, catcher);
    end

    begin
      bit orig_agent_en_cov = cfg.m_uart_agent_cfg.en_cov;
      cfg.m_uart_agent_cfg.en_cov = 1'b0;
      cfg.sec_cm_vif.inject_spurious_tx_frame(
          .data(8'hA5),
          .bit_period(cfg.m_uart_agent_cfg.vif.uart_clk_period),
          .en_parity(en_parity),
          .odd_parity(odd_parity));
      cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      cfg.clk_rst_vif.wait_clks(10);
      cfg.m_uart_agent_cfg.en_cov = orig_agent_en_cov;
    end

    if (!uncaught_neg_mode) begin
      catcher.expect_unexp_tx_err = 1'b0;
      uvm_report_cb::delete(null, catcher);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(catcher.caught_unexp_tx_err_cnt, 1,
                     "Injected TX frame with en_tx=0 must trigger scoreboard unexpected-TX UVM_ERROR")
      end
    end

    // Restore en_tx=1 and clean idle state
    en_tx = 1'b1;
    uart_init();
  endtask : verify_unexpected_tx_while_disabled_detection

  // program one Tx item in register and wait for it to complete before send another one
  virtual task process_tx();
    for (int j = 1; j <= num_tx_bytes; j++) begin
      byte tx_byte;
      uart_item tx_pkt;

      `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
      tx_pkt = uart_item::type_id::create("tx_pkt");
      tx_pkt.data = tx_byte;
      tx_pkt.start_bit = 1'b0;
      tx_pkt.stop_bit = 1'b1;
      if (en_parity) begin
        tx_pkt.parity = `GET_PARITY(tx_byte, odd_parity);
      end else begin
        tx_pkt.parity = 1'b0;
      end

      `uvm_info(`gfn, $sformatf("Sending TX transaction pkt [%0d/%0d]:\n%0s", j, num_tx_bytes, tx_pkt.sprint()), UVM_LOW)
      send_tx_byte(tx_byte);
      // if no delay in TL-UL trans, DUT takes 1 more cycle to update status reg
      cfg.clk_rst_vif.wait_clks(1);
      spinwait_txidle();
      `uvm_info(`gfn, $sformatf("Completed TX transaction pkt [%0d/%0d]: data=0x%02x", j, num_tx_bytes, tx_byte), UVM_LOW)
      if (!cfg.under_reset && this.get_type_name() == "uart_smoke_vseq") begin
        bit [TL_DW-1:0] status_val, fifo_status_val;
        csr_rd(.ptr(ral.status), .value(status_val));
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(get_field_val(ral.status.txempty, status_val), 1'b1, "status.txempty must be 1");
        end
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status_val));
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(get_field_val(ral.fifo_status.txlvl, fifo_status_val), 0, "fifo_status.txlvl must be 0");
        end
      end
    end
  endtask : process_tx

  // sequentially send one Rx byte, then immediately read from register and check it
  virtual task process_rx();
    cfg.clk_rst_vif.wait_clks(100);
    for (int j = 1; j <= num_rx_bytes; j++) begin
      byte rx_byte;
      bit [TL_DW-1:0] dut_rdata;
      uart_item rx_pkt;

      `DV_CHECK_STD_RANDOMIZE_FATAL(rx_byte)
      rx_pkt = uart_item::type_id::create("rx_pkt");
      rx_pkt.data = rx_byte;
      rx_pkt.start_bit = 1'b0;
      rx_pkt.stop_bit = 1'b1;
      if (en_parity) begin
        rx_pkt.parity = `GET_PARITY(rx_byte, odd_parity);
      end else begin
        rx_pkt.parity = 1'b0;
      end

      `uvm_info(`gfn, $sformatf("Sending RX transaction pkt [%0d/%0d]:\n%0s", j, num_rx_bytes, rx_pkt.sprint()), UVM_LOW)
      fork
        send_rx_byte(rx_byte);
        begin
          bit [TL_DW-1:0] mid_status_val;
          wait (cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses == 5 || cfg.under_reset);
          if (!cfg.under_reset) begin
            csr_rd(.ptr(ral.status), .value(mid_status_val));
          end
        end
      join
      reset_aware_simple_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0),
                                  .spinwait_delay_ns(500), .timeout_ns(50_000_000));
      if (cfg.under_reset) return;
      csr_rd(.ptr(ral.rdata), .value(dut_rdata));
      `uvm_info(`gfn, $sformatf("Received RX transaction pkt [%0d/%0d]: expected=0x%02x, actual=0x%02x", j, num_rx_bytes, rx_byte, dut_rdata[7:0]), UVM_LOW)
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(rx_byte, dut_rdata)
        if (this.get_type_name() == "uart_smoke_vseq") begin
          bit [TL_DW-1:0] st_val, fst_val;
          csr_rd(.ptr(ral.status), .value(st_val));
          if (!cfg.under_reset) begin
            `DV_CHECK_EQ(get_field_val(ral.status.rxempty, st_val), 1'b1, "status.rxempty must be 1");
          end
          csr_rd(.ptr(ral.fifo_status), .value(fst_val));
          if (!cfg.under_reset) begin
            `DV_CHECK_EQ(get_field_val(ral.fifo_status.rxlvl, fst_val), 0, "fifo_status.rxlvl must be 0");
          end
        end
      end
    end
  endtask : process_rx

  virtual task process_remaining_data();
    dut_shutdown();
  endtask : process_remaining_data

  virtual task post_start();
    super.post_start();
    if (this.get_type_name() == "uart_smoke_vseq" && do_apply_reset && !cfg.under_reset) begin
      `DV_CHECK_EQ(cfg.en_scb, 1'b1, "Scoreboard must be enabled in uart_smoke_vseq")
      `DV_CHECK_GT(cfg.scb_tx_compared_cnt, 0, "uart_smoke_vseq must complete non-zero TX scoreboard comparisons")
      `DV_CHECK_GT(cfg.scb_rx_compared_cnt, 0, "uart_smoke_vseq must complete non-zero RX scoreboard comparisons")
      `uvm_info(`gfn, $sformatf("Verified uart_smoke_vseq completed all TX/RX transfers and scoreboard comparisons (tx_compared=%0d, rx_compared=%0d)",
                                cfg.scb_tx_compared_cnt, cfg.scb_rx_compared_cnt), UVM_LOW)
    end
  endtask

endclass : uart_smoke_vseq
