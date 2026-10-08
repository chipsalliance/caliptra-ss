// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_reg_parent_seq extends uvm_sequence_base;
  `uvm_object_utils(uart_reg_parent_seq)
  function new(string name = "uart_reg_parent_seq");
    super.new(name);
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

    // Read RX FIFO without reprogramming/resending to RX and verify original payload remains intact
    csr_rd(.ptr(ral.rdata), .value(dut_rdata));
    if (!cfg.under_reset) begin
      if (exp_rx_fifo_q.size() > 0) void'(exp_rx_fifo_q.pop_front());
      rx_bytes_read_cnt++;
      `DV_CHECK_EQ(dut_rdata[7:0], rx_orig_byte,
                   "RX FIFO original payload (0xA5) must remain intact after programming TX FIFO with distinct payload (0x5A)")
    end
  endtask : verify_rx_tx_fifo_isolation

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
    if (this.get_type_name() == "uart_smoke_vseq") begin
      `uvm_info(`gfn, "Verified uart_smoke_vseq completed all TX/RX transfers and FIFO empty checks", UVM_LOW)
    end
    super.post_start();
  endtask

endclass : uart_smoke_vseq
