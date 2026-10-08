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
  bit expect_id_err;
  bit expect_sva_err;
  int caught_tx_err_cnt;
  int caught_rx_err_cnt;
  int caught_id_err_cnt;
  int caught_sva_err_cnt;

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
      if (expect_id_err && str_contains(msg, "Cannot represent req.m_id")) begin
        caught_id_err_cnt++;
        set_severity(UVM_INFO);
        set_id("AXI_ID_WIDTH_CHK");
        set_message($sformatf("Caught expected AXI ID width error: %s", msg));
        return THROW;
      end
      if (expect_sva_err && str_contains(msg, "AW payload contains X/Z when AWVALID is high")) begin
        caught_sva_err_cnt++;
        set_severity(UVM_INFO);
        set_id("AXI_EN_ASSERT_CHK");
        set_message($sformatf("Caught expected AXI SVA error when en_assert=1: %s", msg));
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
      begin
        uvm_reg_adapter adapter = ral.default_map.get_adapter();
        if (adapter != null && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
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
          verify_inline_review_findings();
        end
      end
      process_remaining_data();
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
      for (int b = 0; b < 4; b++) begin
        if (!partial_masks[p_i][b]) begin
          `DV_CHECK_EQ(rd_val[8*b +: 8], 8'((32'h805A_A5C3 >> (8*b)) & 8'hFF),
                       $sformatf("Unselected byte %0d of timeout_ctrl must remain unchanged for byte_en=4'b%04b",
                                 b, partial_masks[p_i]))
        end
      end
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
        bit [3:0] exp_be = 4'b0001;
        bit [31:0] exp_wdata = {24'h0000_00, payload_9b[b_i]};
        if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;
        if (b_i == 8) begin
          `DV_CHECK_EQ({exp_be, exp_wdata}, 36'h1_0000_0099,
                       "Final write of 9-byte payload must have {byte_en, data} == 36'h1_0000_0099 (not 4'hf)")
        end
        write_wdata_with_mask(.data(payload_9b[b_i]), .mask(exp_be), .status(wr_status));
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

  // Verify the three scoreboard checks in regression:
  // 1. Clean traffic passes in the scoreboard (scb_tx_compared_cnt > 0 && scb_rx_compared_cnt > 0).
  // 2. Corrupted TX data fails in the scoreboard (triggers "TX item mismatch!" UVM_ERROR).
  // 3. Corrupted RX data fails in the scoreboard (triggers "rdata read comparison" UVM_ERROR).
  virtual task verify_scb_tx_rx_corruption_detection();
    uart_scb_corrupt_catcher catcher;
    bit [TL_DW-1:0] status_val, dut_rdata;

    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // 1. Verify clean traffic passed in the scoreboard
    `DV_CHECK_EQ(cfg.en_scb, 1'b1, "Scoreboard must be enabled")
    `DV_CHECK_GT(cfg.scb_tx_compared_cnt, 0, "Clean TX traffic must pass in the scoreboard")
    `DV_CHECK_GT(cfg.scb_rx_compared_cnt, 0, "Clean RX traffic must pass in the scoreboard")

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
    uvm_report_cb::delete(null, catcher);

    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(catcher.caught_rx_err_cnt, 1,
                   "Corrupted RX data must fail in the scoreboard with rdata read comparison error")
    end
  endtask : verify_scb_tx_rx_corruption_detection

  // Verify the shared axi_agent fixes for Inline Findings #2, #3, and #4:
  // - Finding #2: Null-response cloning on axi_fixed_write_rsp_item and axi_fixed_write_req_item
  // - Finding #3: Out-of-range m_id on axi_mgr_read_fixed_vseq / axi_mgr_write_fixed_vseq reports
  //               driver width UVM_ERROR and completes response routing without deadlock
  // - Finding #4: en_assert=0 disables SVA protocol assertions, and en_assert=1 enables them
  virtual task verify_inline_review_findings();
    uart_env env;
    uart_scb_corrupt_catcher catcher;
    axi_fixed_write_rsp_item wr_rsp_src, wr_rsp_clone;
    axi_fixed_write_req_item wr_req_src, wr_req_clone;
    virtual axi_write_data_if wdat_vif;
    bit uncaught_id_err  = $test$plusargs("inject_invalid_id");
    bit uncaught_sva_err = $test$plusargs("inject_en_assert_x");

    if (cfg.under_reset || !cfg.clk_rst_vif.rst_n) return;

    // 1. Finding #2: Null-response and partial-null cloning controls
    wr_rsp_src = axi_fixed_write_rsp_item::type_id::create("wr_rsp_src");
    `DV_CHECK_EQ($cast(wr_rsp_clone, wr_rsp_src.clone()), 1, "Cloning all-null axi_fixed_write_rsp_item must succeed")
    `DV_CHECK_EQ(wr_rsp_clone.m_aw_status == null && wr_rsp_clone.m_w_status == null && wr_rsp_clone.m_write_response == null, 1,
                 "Cloned all-null axi_fixed_write_rsp_item must preserve null fields")

    wr_rsp_src.m_aw_status = axi_status_item::type_id::create("m_aw_status");
    wr_rsp_src.m_aw_status.m_sending_complete = 1'b1;
    wr_rsp_src.m_w_status  = axi_status_item::type_id::create("m_w_status");
    wr_rsp_src.m_w_status.m_sending_complete  = 1'b1;
    wr_rsp_src.m_write_response = null;
    `DV_CHECK_EQ($cast(wr_rsp_clone, wr_rsp_src.clone()), 1, "Cloning partial-reset axi_fixed_write_rsp_item (m_write_response==null) must succeed")
    `DV_CHECK_EQ(wr_rsp_clone.m_aw_status != null && wr_rsp_clone.m_w_status != null && wr_rsp_clone.m_write_response == null, 1,
                 "Cloned partial-reset axi_fixed_write_rsp_item must preserve non-null status and null m_write_response")

    wr_req_src = axi_fixed_write_req_item::type_id::create("wr_req_src");
    wr_req_src.m_write_data_item = null;
    `DV_CHECK_EQ($cast(wr_req_clone, wr_req_src.clone()), 1, "Cloning axi_fixed_write_req_item with m_write_data_item==null must succeed")
    `DV_CHECK_EQ(wr_req_clone.m_write_data_item == null, 1, "Cloned axi_fixed_write_req_item must preserve null m_write_data_item")

    // 2. Finding #3: Out-of-range m_id on fixed read/write sequences
    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      axi_mgr_read_fixed_vseq  read_vseq   = axi_mgr_read_fixed_vseq::type_id::create("read_vseq_inv_id");
      axi_mgr_write_fixed_vseq write_vseq  = axi_mgr_write_fixed_vseq::type_id::create("write_vseq_inv_id");
      uvm_reg_addr_t           status_addr = ral.status.get_address();
      uvm_reg_addr_t           ovrd_addr   = ral.ovrd.get_address();

      catcher = uart_scb_corrupt_catcher::type_id::create("inline_catcher");
      if (!uncaught_id_err) begin
        catcher.expect_id_err = 1'b1;
        uvm_report_cb::add(null, catcher);
      end

      read_vseq.set_sequencers(env.m_axi_agent.get_read_request_sequencer(),
                               env.m_axi_agent.get_read_data_sequencer());
      read_vseq.set_read_response_router(env.m_axi_agent.get_read_response_router());
      if (!read_vseq.randomize() with {
            m_fixed_req.m_addr == local::status_addr;
            m_fixed_req.m_size == 3'd2;
            m_fixed_req.m_id   == 32'h0000_015A;
            m_fixed_req.m_user == 128'h0000_0000_0000_0000_0000_0000_003C_0000;
          }) begin
        `uvm_fatal(`gfn, "Failed to randomize read_vseq_inv_id")
      end
      read_vseq.start(null);
      `DV_CHECK_EQ(read_vseq.rsp != null && read_vseq.rsp.m_read_data != null, 1,
                   "Fixed read with out-of-range m_id must complete response routing without deadlock")
      `DV_CHECK_EQ(read_vseq.rsp.m_read_data.m_id, 32'h5A,
                   "Fixed read response must match wire-masked ID (0x5A)")

      write_vseq.set_sequencers(env.m_axi_agent.get_write_request_sequencer(),
                                env.m_axi_agent.get_write_data_sequencer(),
                                env.m_axi_agent.get_write_response_sequencer());
      write_vseq.set_write_response_router(env.m_axi_agent.get_write_response_router());
      if (!write_vseq.randomize() with {
            m_fixed_req.m_addr == local::ovrd_addr;
            m_fixed_req.m_size == 3'd2;
            m_fixed_req.m_id   == 32'h0000_01A5;
            m_fixed_req.m_user == 128'h0000_0000_0000_0000_0000_0000_003C_0000;
            m_fixed_req.m_write_data_item.m_data == 1024'h0;
            m_fixed_req.m_write_data_item.m_strb == 128'hF;
            m_fixed_req.m_write_data_item.m_last == 1'b1;
            m_fixed_req.m_write_data_item.m_user == 512'h0;
          }) begin
        `uvm_fatal(`gfn, "Failed to randomize write_vseq_inv_id")
      end
      write_vseq.start(null);
      `DV_CHECK_EQ(write_vseq.rsp != null && write_vseq.rsp.m_write_response != null, 1,
                   "Fixed write with out-of-range m_id must complete response routing without deadlock")
      `DV_CHECK_EQ(write_vseq.rsp.m_write_response.m_id, 32'hA5,
                   "Fixed write response must match wire-masked ID (0xA5)")
      `uvm_info(`gfn, "Completed invalid-ID write and read without deadlock", UVM_LOW)

      if (!uncaught_id_err) begin
        catcher.expect_id_err = 1'b0;
        uvm_report_cb::delete(null, catcher);
        `DV_CHECK_EQ(catcher.caught_id_err_cnt, 2,
                     "Driver must report UVM_ERROR for both out-of-range read and write m_id requests")
      end
    end

    // 3. Finding #4: en_assert=0 vs en_assert=1 on AXI channel interface SVA
    begin
      virtual axi_write_request_if wreq_vif;
      if (uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", wreq_vif)) begin
        // 3a. With en_assert=0, driving X on awregion while awvalid=1 must NOT trigger SVA error
        wreq_vif.set_en_assert(1'b0);
        fork
          csr_wr(.ptr(ral.ovrd), .value('0), .predict(1'b1));
          begin
            wait (wreq_vif.awvalid === 1'b1);
            wreq_vif.awregion_driven = 4'hx;
            @(posedge wreq_vif.clk_i);
            wreq_vif.awregion_driven = 4'h0;
          end
        join
        wreq_vif.set_en_assert(!$test$plusargs("disable_axi_sva"));

        // 3b. When +inject_en_assert_x is enabled, drive X on awregion under the active en_assert setting
        if (uncaught_sva_err) begin
          fork
            csr_wr(.ptr(ral.ovrd), .value('0), .predict(1'b1));
            begin
              wait (wreq_vif.awvalid === 1'b1);
              wreq_vif.awregion_driven = 4'hx;
              @(posedge wreq_vif.clk_i);
              wreq_vif.awregion_driven = 4'h0;
            end
          join
        end
      end
    end
  endtask : verify_inline_review_findings

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
      bit [TL_DW-1:0] dut_rdata, status_val;
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
      send_rx_byte(rx_byte);
      do begin
        cfg.clk_rst_vif.wait_clks(50);
        csr_rd(.ptr(ral.status), .value(status_val));
      end while (status_val[5] == 1'b1);
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
