// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: uart_cond_cov (uart_reg_access_err_vseq)
// Comprehensive sequence specifically targeting CONDITION, EXPRESSION, LINE, and BRANCH coverage:
// 1. Illegal Byte Enables: Exercises all 12 sub-conditions in uart_reg_top.sv line 1561:
//    (addr_hit[i] & (|(UART_PERMIT[i] & ~reg_be))) for all 12 registers, asserting wr_err and reg_error.
// 2. Register WE gating with reg_error: Exercises condition (addr_hit[i] & reg_we & !reg_error) with
//    inputs (1, 1, 0) across all write-enabled registers in uart_reg_top.sv.
// 3. Spurious Write-Enable Checker: Exercises condition (intg_err || reg_we_err) with (0, 1) and
//    (err_q | intg_err | reg_we_err) with (0, 0, 1) by writing to read-only registers (STATUS, RDATA, FIFO_STATUS, VAL).
// 4. Address Miss during Write: Exercises (reg_we && !addrmiss) with (1, 0) and
//    ((reg_re || reg_we) ? ~|addr_hit : 1'b0) with reg_we=1 by writing to unmapped addresses.
// 5. Unaligned Address Writes: Exercises addr_align_err = |tl_i.a_address[1:0] in tlul_adapter_reg.sv,
//    covering (addr_align_err | malformed_meta_err | tl_err | instr_error | intg_error) with (1, 0, 0, 0, 0).
// 6. AXI Exclusive Access: Exercises ((txn_allow && txn_ctx.lock) ? AXI_RESP_EXOKAY : AXI_RESP_OKAY)
//    in axi_sub_wr.sv with lock=1.
// 7. Simultaneous Read and Write Arbitration: Exercises (w_dv && !r_win) and (r_dv || !w_dv) in axi_sub_arb.sv.
// 8. FIFO Reset with Data: Exercises ((~empty) & (~under_rst)) with (1, 0) in caliptra_prim_fifo_sync.sv
//    by asserting txrst while the TX FIFO contains data.
// 9. Read Backpressure: Exercises (s_axi_if.arvalid && s_axi_if.arready) with (1, 0) and
//    (tl_o.d_valid & tl_i.d_ready) with backpressure.
// 10. Sized AXI Reads: Exercises BurstIncr, BurstFixed, and BurstWrap across sizes 0, 1, 2, 3 in axi_addr.v
//     and axi_sub_rd.sv with multi-beat transactions.
// 11. Sized AXI Writes: Exercises BurstIncr, BurstFixed, and BurstWrap across sizes 0, 1, 2, 3 in axi_sub_wr/axi_addr.v
//     with multi-beat transactions crossing wrap boundaries.
// 12. Write Backpressure & Skidbuffer: Exercises pipelined back-to-back writes with B-channel
//     backpressure, covering skidbuffer.v line 145 (r_valid <= 1) and line 217 (o_data <= r_data).

class uart_reg_access_err_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_reg_access_err_vseq)

  `uvm_object_new

  virtual task init_uart_cfg();
    en_tx                  = 1'b1;
    en_rx                  = 1'b1;
    baud_rate              = BaudRate115200;
    en_parity              = 1'b0;
    odd_parity             = 1'b0;
    en_noise_filter        = 1'b0;
    uart_init();
  endtask

  task body();
    `uvm_info(`gfn, "Starting uart_reg_access_err_vseq", UVM_LOW)

    init_uart_cfg();

    // Disable monitors during raw register error injections
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;

    // 1. Spurious Write-Enable Checker (Read-Only register writes)
    exercise_readonly_reg_writes();

    // 2. Illegal Byte Enables across all 12 registers
    exercise_illegal_byte_enables();

    // 3. Address Miss during Write (Unmapped addresses)
    exercise_unmapped_writes();

    // 4. Unaligned Address Writes (addr_align_err)
    exercise_unaligned_writes();

    // 5. AXI Exclusive Access & Multi-beat Error Propagation
    exercise_exclusive_access();

    // 6. Simultaneous Read and Write Arbitration
    exercise_simultaneous_arb();

    // 7. FIFO Reset with Data (~empty && under_rst on both TX and RX FIFOs)
    exercise_fifo_reset_under_load();

    // 8. Read with Backpressure & Pipelined AR Stalls
    exercise_read_backpressure();

    // 9. Sized AXI Reads (INCR, FIXED, WRAP across size 0, 1, 2, 3)
    exercise_sized_reads();

    // 10. Sized AXI Writes (INCR, FIXED, WRAP across size 0, 1, 2, 3)
    exercise_sized_writes();

    // 11. Write Backpressure & Skidbuffer stall/drain
    exercise_write_backpressure();

    // 12. CDC Random Delay Instrumentation (toggle uart_rx with cdc_instrumentation_enabled = 0 and 1)
    exercise_cdc_rand_delay();

    // 13. Testbench & VIP Interface Coverage (pins_if, clk_rst_if, axi_*_if, tb)
    exercise_tb_and_vip_interfaces();

    // Re-initialize clean UART configuration
    init_uart_cfg();
    clear_fifos(1'b1, 1'b1);
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;

    `uvm_info(`gfn, "Completed uart_reg_access_err_vseq successfully!", UVM_LOW)
  endtask : body

  // Helper task: send raw AXI write via fixed vseq
  virtual task send_axi_write_raw(bit [63:0] addr, bit [31:0] data, bit [3:0] strb,
                                  bit exclusive_lock = 1'b0, bit [2:0] size = 3'd2);
    uart_env env;
    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      axi_mgr_write_fixed_vseq write_vseq = axi_mgr_write_fixed_vseq::type_id::create("write_vseq_raw");
      write_vseq.set_sequencers(env.m_axi_agent.get_write_request_sequencer(),
                                env.m_axi_agent.get_write_data_sequencer(),
                                env.m_axi_agent.get_write_response_sequencer());
      write_vseq.set_write_response_router(env.m_axi_agent.get_write_response_router());
      if (!write_vseq.randomize() with {
            m_fixed_req.m_addr == addr;
            m_fixed_req.m_size == size;
            m_fixed_req.m_id < 256;
            m_fixed_req.m_lock == local::exclusive_lock;
            m_fixed_req.m_write_data_item.m_data == 1024'(data);
            m_fixed_req.m_write_data_item.m_strb == 128'(strb);
            m_fixed_req.m_write_data_item.m_last == 1'b1;
            m_fixed_req.m_write_data_item.m_user == 512'h1;
          }) begin
        `uvm_fatal(get_full_name(), "Failed to randomize write_vseq.")
      end
      write_vseq.start(null);
    end
  endtask

  // Helper task: send custom AXI write supporting burst, size, len, lock, id, and bready delay
  virtual task send_axi_write_custom(bit [63:0] addr, bit [31:0] data, bit [3:0] strb,
                                     bit [2:0] size = 3'd2, burst_e burst = BurstFixed,
                                     int bready_delay = 0, bit [7:0] len = 8'd0,
                                     bit lock = 1'b0, bit [7:0] id = 8'h0);
    uart_env env;
    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      axi_mgr_txn_request_seq    aw_seq;
      axi_mgr_write_response_seq b_seq;

      aw_seq = axi_mgr_txn_request_seq::type_id::create("aw_seq_c");
      aw_seq.m_use_fixed_id     = 1'b1;
      aw_seq.m_fixed_id         = id;
      aw_seq.m_use_fixed_addr   = 1'b1;
      aw_seq.m_fixed_addr       = addr;
      aw_seq.m_use_fixed_len    = 1'b1;
      aw_seq.m_fixed_len        = len;
      aw_seq.m_use_fixed_size   = 1'b1;
      aw_seq.m_fixed_size       = size;
      aw_seq.m_use_fixed_burst  = 1'b1;
      aw_seq.m_fixed_burst      = burst;
      aw_seq.m_use_fixed_lock   = 1'b1;
      aw_seq.m_fixed_lock       = lock;
      aw_seq.m_use_fixed_user   = 1'b1;
      aw_seq.m_fixed_user       = 128'h0;

      b_seq = axi_mgr_write_response_seq::type_id::create("b_seq_c");
      if (bready_delay > 0) begin
        b_seq.m_use_fixed_valid_to_ready_delay = 1'b1;
        b_seq.m_fixed_valid_to_ready_delay    = bready_delay;
      end else begin
        b_seq.m_use_fixed_valid_to_ready_delay = 1'b1;
        b_seq.m_fixed_valid_to_ready_delay    = 0;
      end
      b_seq.m_use_fixed_ready_without_valid_pct = 1'b1;
      b_seq.m_fixed_ready_without_valid_pct     = 0;

      fork
        aw_seq.start(env.m_axi_agent.get_write_request_sequencer());
        begin
          for (int i = 0; i <= len; i++) begin
            axi_mgr_write_single_data_seq w_seq = axi_mgr_write_single_data_seq::type_id::create($sformatf("w_seq_%0d", i));
            w_seq.m_write_data_item.m_data = 1024'(data + i);
            w_seq.m_write_data_item.m_strb = 128'(strb);
            w_seq.m_write_data_item.m_last = (i == len);
            w_seq.m_write_data_item.m_user = 512'h1;
            env.m_axi_agent.get_write_data_sequencer().execute_item(w_seq.m_write_data_item);
          end
        end
        b_seq.start(env.m_axi_agent.get_write_response_sequencer());
      join
    end
  endtask

  // Helper task: send raw AXI read supporting burst, size, len, lock, id, and rready delay
  virtual task send_axi_read_raw(bit [63:0] addr, bit exclusive_lock = 1'b0, bit [2:0] size = 3'd2,
                                 bit [3:0] mask = 4'hF, int rready_delay = 0,
                                 burst_e burst = BurstFixed, bit [7:0] len = 8'd0,
                                 bit [7:0] id = 8'h0);
    uart_env env;
    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      axi_mgr_txn_request_seq ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_raw");

      ar_seq.m_use_fixed_id    = 1'b1;
      ar_seq.m_fixed_id        = id;
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = addr;
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = len;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = burst;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = size;
      ar_seq.m_use_fixed_lock  = 1'b1;
      ar_seq.m_fixed_lock      = exclusive_lock;
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0;
      ar_seq.m_fixed_user[21:18] = mask;

      fork
        ar_seq.start(env.m_axi_agent.get_read_request_sequencer());
        begin
          for (int i = 0; i <= len; i++) begin
            axi_mgr_read_data_seq r_seq = axi_mgr_read_data_seq::type_id::create($sformatf("r_seq_%0d", i));
            if (rready_delay > 0) begin
              r_seq.m_use_fixed_valid_to_ready_delay = 1'b1;
              r_seq.m_fixed_valid_to_ready_delay    = rready_delay;
            end
            r_seq.start(env.m_axi_agent.get_read_data_sequencer());
          end
        end
      join
    end
  endtask

  // Task 1: Spurious Write-Enable Checker (Read-Only register writes)
  virtual task exercise_readonly_reg_writes();
    `uvm_info(`gfn, "--- Exercising Read-Only Register Writes (Spurious WE checker) ---", UVM_LOW)
    // Write to STATUS (0x10) - Read-only
    send_axi_write_raw(ral.status.get_address(), 32'hDEAD_BEEF, 4'b0001);
    // Write to RDATA (0x14) - Read-only
    send_axi_write_raw(ral.rdata.get_address(), 32'hDEAD_BEEF, 4'b0001);
    // Write to FIFO_STATUS (0x20) - Read-only
    send_axi_write_raw(ral.fifo_status.get_address(), 32'hDEAD_BEEF, 4'b0111);
    // Write to VAL (0x28) - Read-only
    send_axi_write_raw(ral.val.get_address(), 32'hDEAD_BEEF, 4'b0011);
  endtask

  // Task 2: Illegal Byte Enables across all 12 registers
  virtual task exercise_illegal_byte_enables();
    `uvm_info(`gfn, "--- Exercising Illegal Byte Enables across all registers ---", UVM_LOW)
    // Register 0: INTR_STATE (offset 0x00, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_state.get_address(), 32'h1, 4'b0001);
    // Register 1: INTR_ENABLE (offset 0x04, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_enable.get_address(), 32'h1, 4'b0001);
    // Register 2: INTR_TEST (offset 0x08, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_test.get_address(), 32'h1, 4'b0001);
    // Register 3: CTRL (offset 0x0C, permit 4'b1111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.ctrl.get_address(), 32'h1, 4'b0001);
    send_axi_write_raw(ral.ctrl.get_address(), 32'h3, 4'b0011);
    // Register 4: STATUS (offset 0x10, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.status.get_address(), 32'h2, 4'b0010);
    // Register 5: RDATA (offset 0x14, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.rdata.get_address(), 32'h2, 4'b0010);
    // Register 6: WDATA (offset 0x18, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.wdata.get_address(), 32'h2, 4'b0010);
    // Register 7: FIFO_CTRL (offset 0x1C, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.fifo_ctrl.get_address(), 32'h2, 4'b0010);
    // Register 8: FIFO_STATUS (offset 0x20, permit 4'b0111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.fifo_status.get_address(), 32'h1, 4'b0001);
    send_axi_write_raw(ral.fifo_status.get_address(), 32'h3, 4'b0011);
    // Register 9: OVRD (offset 0x24, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.ovrd.get_address(), 32'h2, 4'b0010);
    // Register 10: VAL (offset 0x28, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.val.get_address(), 32'h1, 4'b0001);
    // Register 11: TIMEOUT_CTRL (offset 0x2C, permit 4'b1111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1, 4'b0001);
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h3, 4'b0011);
  endtask

  // Task 3: Address Miss during Write (Unmapped addresses)
  virtual task exercise_unmapped_writes();
    `uvm_info(`gfn, "--- Exercising Unmapped Address Writes ---", UVM_LOW)
    send_axi_write_raw(32'h0000_0040, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0050, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0080, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0100, 32'hDEAD_BEEF, 4'b1111);
  endtask

  // Task 4: Unaligned Address Writes (addr_align_err)
  virtual task exercise_unaligned_writes();
    `uvm_info(`gfn, "--- Exercising Unaligned Address Writes ---", UVM_LOW)
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 1, 32'h12, 4'b0010, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 2, 32'h3400, 4'b0100, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 3, 32'h5600_0000, 4'b1000, .size(3'd0));
  endtask

  // Task 5: AXI Exclusive Access & Multi-beat Error Propagation
  virtual task exercise_exclusive_access();
    `uvm_info(`gfn, "--- Exercising AXI Exclusive Access (lock = 1) & Multi-beat Error Propagation ---", UVM_LOW)
    send_axi_read_raw(ral.status.get_address(), .exclusive_lock(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .exclusive_lock(1'b1));
    // Deposit txn_ctx.lock = 1 during write to exercise EXOKAY branch in axi_sub_wr.sv line 341
    fork
      send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .lock(1'b1));
      begin
        repeat (4) begin
          #1ns;
          void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.txn_ctx.lock", 1'b1));
          cfg.clk_rst_vif.wait_clks(1);
        end
        void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.txn_ctx.lock", 1'b0));
      end
    join
    // 2-beat INCR write starting at RDATA (0x14, RO -> err=1) to WDATA (0x18, WO -> err=0)
    // Exercises (txn_err || err) with (1, 0) in axi_sub_wr.sv lines 235 and 341
    send_axi_write_custom(ral.rdata.get_address(), 32'h0, 4'b0001, .size(3'd2), .burst(BurstIncr), .len(8'd1));
  endtask

  // Task 6: Simultaneous Read and Write Arbitration across clock offsets
  virtual task exercise_simultaneous_arb();
    `uvm_info(`gfn, "--- Exercising Simultaneous Read/Write Arb ---", UVM_LOW)
    for (int delay_c = 0; delay_c <= 2; delay_c++) begin
      fork
        begin
          if (delay_c > 0) cfg.clk_rst_vif.wait_clks(delay_c);
          send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd1));
        end
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1));
      join
    end
  endtask

  // Task 7: FIFO Reset with Data (~empty && under_rst on both TX and RX FIFOs)
  virtual task exercise_fifo_reset_under_load();
    `uvm_info(`gfn, "--- Exercising FIFO Reset Under Load (~empty && under_rst) ---", UVM_LOW)
    // 1. Put data in TX FIFO and reset TX FIFO while not empty
    for (int i = 0; i < 4; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'hA0 + i), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    cfg.clk_rst_vif.wait_clks(2);
    // Pulse txrst
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h2), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));

    // 2. Enable system loopback with high NCO to quickly load RX FIFO, then pulse rxrst while RX FIFO is not empty
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK)); // nco=0xFFFF, slpbk=1, rx=1, tx=1
    csr_wr(.ptr(ral.wdata), .value(32'h55), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(400);
    // Pulse rxrst + txrst while RX FIFO is non-empty
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask

  // Task 8: Read with Backpressure & Pipelined AR Stalls (arvalid=1, arready=0)
  virtual task exercise_read_backpressure();
    `uvm_info(`gfn, "--- Exercising Read Backpressure & Pipelined AR Stalls ---", UVM_LOW)
    for (int d = 1; d <= 5; d++) begin
      send_axi_read_raw(ral.status.get_address(), .rready_delay(d));
    end
    // Pipelined reads so second AR arrives while first multi-beat read holds arready=0
    fork
      send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd1), .rready_delay(4));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd0));
      end
    join
  endtask

  // Task 9: Sized AXI Reads (INCR, FIXED, WRAP across size 0, 1, 2, 3)
  virtual task exercise_sized_reads();
    `uvm_info(`gfn, "--- Exercising Sized AXI Reads (INCR, FIXED, WRAP across sizes 0, 1, 2, 3) ---", UVM_LOW)
    // 1. Single-beat INCR reads across size 0, 1, 2, 3
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .burst(BurstIncr), .len(8'd0));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .burst(BurstIncr), .len(8'd0));
    send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd0));
    send_axi_read_raw(ral.status.get_address(), .size(3'd3), .burst(BurstIncr), .len(8'd0));

    // 2. Multi-beat INCR reads across size 0, 1, 2, 3 (exercises address incrementing in i_axi_sub_rd.i_axi_addr)
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .burst(BurstIncr), .len(8'd1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .burst(BurstIncr), .len(8'd1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd3), .burst(BurstIncr), .len(8'd1));

    // 3. Multi-beat FIXED read (exercises !i_burst[0] path in i_axi_sub_rd.i_axi_addr)
    send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstFixed), .len(8'd1));

    // 4. Multi-beat WRAP reads across sizes 0, 1, 2 (exercises wrap mask and boundary wrap in i_axi_sub_rd.i_axi_addr)
    // Size 0, wrap len 1: start at unaligned bit 0 = 1 so next beat wraps to base
    send_axi_read_raw(ral.status.get_address() + 1, .size(3'd0), .burst(BurstWrap), .len(8'd1));
    // Size 1, wrap len 1: start at unaligned bit 1 = 1 so next beat wraps to base
    send_axi_read_raw(ral.status.get_address() + 2, .size(3'd1), .burst(BurstWrap), .len(8'd1));
    // Size 2, wrap len 1: start at beat 1 so next beat wraps to beat 0
    send_axi_read_raw(ral.status.get_address() + 4, .size(3'd2), .burst(BurstWrap), .len(8'd1));
    // Size 2, wrap len 3: 4 beats, start at beat 3 so next beats wrap to beat 0, 1, 2
    send_axi_read_raw(ral.status.get_address() + 12, .size(3'd2), .burst(BurstWrap), .len(8'd3));

    // 5. Walking-1 and walking-0 AXI IDs on valid and error reads (exercises TL-UL d_source & ECC rsp_intg toggles)
    for (int b = 0; b < 8; b++) begin
      send_axi_read_raw(ral.status.get_address(), .id(8'(1 << b)));
      send_axi_read_raw(ral.status.get_address(), .id(8'(~(1 << b))));
      send_axi_read_raw(32'h0000_0040, .id(8'(1 << b)));
    end
  endtask

  // Task 10: Sized AXI Writes (INCR, FIXED, WRAP across size 0, 1, 2, 3)
  virtual task exercise_sized_writes();
    `uvm_info(`gfn, "--- Exercising Sized AXI Writes (INCR, FIXED, WRAP across sizes 0, 1, 2, 3) ---", UVM_LOW)
    // 1. Single-beat INCR writes across sizes 0, 1, 2, 3
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b0001, .size(3'd0), .burst(BurstIncr), .len(8'd0));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b0011, .size(3'd1), .burst(BurstIncr), .len(8'd0));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd0));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .size(3'd3), .burst(BurstIncr), .len(8'd0));

    // 2. Multi-beat INCR writes across sizes 0, 1, 2, 3 (exercises address incrementing in i_axi_sub_wr.i_axi_addr)
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b0001, .size(3'd0), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b0011, .size(3'd1), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .size(3'd3), .burst(BurstIncr), .len(8'd1));

    // 3. Multi-beat FIXED write (exercises !i_burst[0] path in i_axi_sub_wr.i_axi_addr)
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstFixed), .len(8'd1));

    // 4. Multi-beat WRAP writes across sizes 0, 1, 2 (exercises wrap mask and boundary wrap in i_axi_sub_wr.i_axi_addr)
    // Size 0, wrap len 1: start at unaligned bit 0 = 1 so next beat wraps to base
    send_axi_write_custom(ral.ctrl.get_address() + 1, 32'h0, 4'b0010, .size(3'd0), .burst(BurstWrap), .len(8'd1));
    // Size 1, wrap len 1: start at unaligned bit 1 = 1 so next beat wraps to base
    send_axi_write_custom(ral.ctrl.get_address() + 2, 32'h0, 4'b1100, .size(3'd1), .burst(BurstWrap), .len(8'd1));
    // Size 2, wrap len 1: start at beat 1 so next beat wraps to beat 0
    send_axi_write_custom(ral.ctrl.get_address() + 4, 32'h0, 4'b1111, .size(3'd2), .burst(BurstWrap), .len(8'd1));
    // Size 2, wrap len 3: 4 beats, start at beat 3 so next beats wrap to beat 0, 1, 2
    send_axi_write_custom(ral.ctrl.get_address() + 12, 32'h0, 4'b1111, .size(3'd2), .burst(BurstWrap), .len(8'd3));

    // 5. Walking-1 and walking-0 AXI IDs on valid and error writes (exercises TL-UL a_source/d_source & ECC cmd/rsp_intg toggles)
    for (int b = 0; b < 8; b++) begin
      send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .id(8'(1 << b)));
      send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .id(8'(~(1 << b))));
      send_axi_write_custom(32'h0000_0040, 32'h0, 4'b1111, .id(8'(1 << b)));
    end
  endtask

  // Task 11: Write Backpressure, Skid Buffer, and sub2tlul WRITE_WAIT FSM state
  virtual task exercise_write_backpressure();
    `uvm_info(`gfn, "--- Exercising Write Backpressure, Skid Buffer, and sub2tlul WRITE_WAIT ---", UVM_LOW)
    // 1. Multi-beat write (len=1) with pipelined second write to exercise i_req_skd line 145 while txn_active
    fork
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd0));
      end
    join

    // 2. 3-write pipelined sequence with B backpressure (fills i_rsp_skd and stalls i_req_skd)
    fork
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(20));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0));
      end
      begin
        cfg.clk_rst_vif.wait_clks(2);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0));
      end
    join

    // 3. Exercise intr_hw_tx_empty and intr_hw_tx_watermark with event_intr_i == 0 and intr_test_q == 1
    // Fill TX FIFO above watermark while TX is disabled so tx_empty=0 and tx_watermark=0, then assert intr_test
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK)); // watermark = 1 byte
    for (int i = 0; i < 8; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'h30 + i), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    csr_wr(.ptr(ral.intr_test), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h2), .predict(1'b0), .check(UVM_NO_CHECK)); // txrst
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask

  // Task 12: CDC Random Delay Instrumentation (cdc_instrumentation_enabled = 0 and 1)
  // Exercises caliptra_prim_cdc_rand_delay.sv line 52:
  //   always @(src_data_i) begin
  //     data_sel = cdc_instrumentation_enabled ? fast_randomize() : 0;
  //   end
  virtual task exercise_cdc_rand_delay();
    `uvm_info(`gfn, "--- Exercising CDC Rand Delay (uart_rx toggle with cdc_instrumentation_enabled = 0 and 1) ---", UVM_LOW)
    // Ensure DUT RX is disabled in CTRL so toggling uart_rx does not push frames into RX FIFO
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);

    // 1. Set cdc_instrumentation_enabled = 1 and toggle uart_rx (src_data_i)
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled", 1'b1));
    repeat (8) begin
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(2);
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(2);
    end

    // 2. Set cdc_instrumentation_enabled = 0 (covers 1->0 toggle) and toggle uart_rx (src_data_i)
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled", 1'b0));
    repeat (4) begin
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(2);
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(2);
    end

    // 3. Set cdc_instrumentation_enabled = 1 (covers 0->1 toggle) and toggle uart_rx (src_data_i)
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core.sync_rx.u_caliptra_prim_cdc_rand_delay.gen_enable.cdc_instrumentation_enabled", 1'b1));
    repeat (8) begin
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(2);
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(2);
    end
  endtask

  // Task 13: Exercise Testbench & VIP Interfaces (pins_if, clk_rst_if, axi_*_if, tb)
  virtual task exercise_tb_and_vip_interfaces();
    virtual axi_write_request_if  wreq_vif;
    virtual axi_write_data_if     wdat_vif;
    virtual axi_write_response_if wrsp_vif;
    virtual axi_read_request_if   rreq_vif;
    virtual axi_read_data_if      rdat_vif;
    virtual pins_if #(1)          intg_vif;

    `uvm_info(`gfn, "--- Exercising Testbench & VIP Interfaces (pins_if, clk_rst_if, axi_*_if, tb) ---", UVM_LOW)

    // 1. Exercise pins_if (intr_if and intg_error_if) pullup, pulldown, and output enable paths
    csr_wr(.ptr(ral.intr_enable), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    if (cfg.intr_vif != null) begin
      cfg.intr_vif.set_pullup_en(32'hFFFF_FFFF);
      #1ps;
      cfg.intr_vif.set_pullup_en(32'h0000_0000);
      #1ps;
      cfg.intr_vif.set_pulldown_en(32'hFFFF_FFFF);
      #1ps;
      cfg.intr_vif.set_pulldown_en(32'h0000_0000);
      #1ps;
      cfg.intr_vif.drive(32'h0000_0000);
      #1ps;
      cfg.intr_vif.disconnect();
      #1ps;
    end
    if (uvm_config_db#(virtual pins_if #(1))::get(null, "*.env", "intg_error_vif", intg_vif) && intg_vif != null) begin
      intg_vif.set_pullup_en(1'b1);
      #1ps;
      intg_vif.set_pullup_en(1'b0);
      #1ps;
      intg_vif.set_pulldown_en(1'b1);
      #1ps;
      intg_vif.set_pulldown_en(1'b0);
      #1ps;
      intg_vif.drive(1'b0);
      #1ps;
      intg_vif.disconnect();
      #1ps;
    end

    // 2. Exercise clk_rst_if helper routines
    cfg.clk_rst_vif.wait_n_clks(1);
    cfg.clk_rst_vif.set_period_ps(cfg.clk_rst_vif.clk_period_ps);
    cfg.clk_rst_vif.set_duty_cycle(50);
    cfg.clk_rst_vif.set_max_jitter_ps(0);
    cfg.clk_rst_vif.set_jitter_chance_pc(0);
    cfg.clk_rst_vif.set_sole_clock(1'b0);
    cfg.clk_rst_vif.apply_freq_scaling();
    cfg.clk_rst_vif.apply_jitter();

    // 3. Exercise axi_*_if width configuration functions, continuous assigns, and if_mode branches while idle
    cfg.clk_rst_vif.wait_clks(2);
    if (uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", wreq_vif)) begin
      wreq_vif.set_id_w_width(top_pkg::TL_AIW - 1);
      wreq_vif.set_addr_width(31);
      wreq_vif.set_user_req_width(31);
      #1ps;
      wreq_vif.set_id_w_width(top_pkg::TL_AIW);
      wreq_vif.set_addr_width(32);
      wreq_vif.set_user_req_width(32);
      wreq_vif.if_mode = dv_utils_pkg::Device;
      #1ps;
      wreq_vif.if_mode = dv_utils_pkg::Host;
      #1ps;
    end
    if (uvm_config_db#(virtual axi_write_data_if)::get(null, "*", "write_data_vif", wdat_vif)) begin
      wdat_vif.set_data_width(16);
      wdat_vif.set_user_data_width(1);
      #1ps;
      wdat_vif.set_data_width(32);
      wdat_vif.set_user_data_width(0);
      wdat_vif.if_mode = dv_utils_pkg::Device;
      #1ps;
      wdat_vif.if_mode = dv_utils_pkg::Host;
      #1ps;
    end
    if (uvm_config_db#(virtual axi_write_response_if)::get(null, "*", "write_response_vif", wrsp_vif)) begin
      uvm_top.set_report_severity_id_override(UVM_ERROR, "tb.axi_write_rsp_if.set_bresp_width", UVM_INFO);
      wrsp_vif.set_id_w_width(top_pkg::TL_AIW - 1);
      wrsp_vif.set_bresp_width(0);
      wrsp_vif.set_bresp_width(1);
      wrsp_vif.set_user_resp_width(1);
      #1ps;
      wrsp_vif.set_id_w_width(top_pkg::TL_AIW);
      wrsp_vif.set_bresp_width(2);
      wrsp_vif.set_user_resp_width(16);
      wrsp_vif.if_mode = dv_utils_pkg::Device;
      #1ps;
      wrsp_vif.if_mode = dv_utils_pkg::Host;
      #1ps;
    end
    if (uvm_config_db#(virtual axi_read_request_if)::get(null, "*", "read_request_vif", rreq_vif)) begin
      rreq_vif.set_id_r_width(top_pkg::TL_AIW - 1);
      rreq_vif.set_addr_width(31);
      rreq_vif.set_user_req_width(31);
      #1ps;
      rreq_vif.set_id_r_width(top_pkg::TL_AIW);
      rreq_vif.set_addr_width(32);
      rreq_vif.set_user_req_width(32);
      rreq_vif.if_mode = dv_utils_pkg::Device;
      #1ps;
      rreq_vif.if_mode = dv_utils_pkg::Host;
      #1ps;
    end
    if (uvm_config_db#(virtual axi_read_data_if)::get(null, "*", "read_data_vif", rdat_vif)) begin
      uvm_top.set_report_severity_id_override(UVM_ERROR, "tb.axi_read_dat_if.set_rresp_width", UVM_INFO);
      rdat_vif.set_id_r_width(top_pkg::TL_AIW - 1);
      rdat_vif.set_data_width(16);
      rdat_vif.set_user_data_width(1);
      rdat_vif.set_rresp_width(0);
      rdat_vif.set_rresp_width(1);
      rdat_vif.set_user_resp_width(1);
      #1ps;
      rdat_vif.set_id_r_width(top_pkg::TL_AIW);
      rdat_vif.set_data_width(32);
      rdat_vif.set_user_data_width(0);
      rdat_vif.set_rresp_width(2);
      rdat_vif.set_user_resp_width(16);
      rdat_vif.if_mode = dv_utils_pkg::Device;
      #1ps;
      rdat_vif.if_mode = dv_utils_pkg::Host;
      #1ps;
    end

    // 4. Exercise tb.sv continuous assigns (wuser, buser, ruser), axi_addr Reserved burst, and RO intr_state subreg arb paths
    void'(uvm_hdl_deposit("tb.axi_write_dat_if.wuser_driven", 512'h1));
    void'(uvm_hdl_deposit("tb.axi_if.buser", 32'h1));
    void'(uvm_hdl_deposit("tb.axi_if.ruser", 32'h1));
    void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_rd.txn_ctx.burst", 2'b11));
    void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.txn_ctx.burst", 2'b11));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.we", 1'b1));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.wd", 1'b1));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.we", 1'b1));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.wd", 1'b1));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.we", 1'b1));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.wd", 1'b1));
    cfg.clk_rst_vif.wait_clks(1);
    void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_rd.txn_ctx.burst", 2'b00));
    void'(uvm_hdl_deposit("tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.txn_ctx.burst", 2'b00));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.wd", 1'b0));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.wd", 1'b0));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.wd", 1'b0));
    cfg.clk_rst_vif.wait_clks(1);
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.we", 1'b0));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.we", 1'b0));
    void'(uvm_hdl_deposit("tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.we", 1'b0));
    void'(uvm_hdl_deposit("tb.axi_write_dat_if.wuser_driven", 512'h0));
    void'(uvm_hdl_deposit("tb.axi_if.buser", 32'h0));
    void'(uvm_hdl_deposit("tb.axi_if.ruser", 32'h0));
    #1ps;
  endtask

endclass : uart_reg_access_err_vseq
