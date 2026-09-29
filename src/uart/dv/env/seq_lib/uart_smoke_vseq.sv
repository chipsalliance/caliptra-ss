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

  constraint baud_rate_c {
    baud_rate == BaudRate230400;
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
      process_remaining_data();
      `uvm_info(`gfn, $sformatf("finished smoke run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

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
