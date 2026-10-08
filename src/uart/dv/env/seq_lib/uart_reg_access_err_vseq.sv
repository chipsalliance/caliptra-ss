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

  virtual task apply_reset(string kind = "HARD");
    virtual axi_write_request_if wreq_vif;
    fork
      super.apply_reset(kind);
      cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b1), .wait_posedge(1'b1));
      begin
        @(negedge cfg.clk_rst_vif.rst_n);
        cfg.clk_rst_vif.drive_rst_pin(1'b0);
        fork
          cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b1));
        join_none
        @(negedge cfg.clk_rst_vif.clk);
        #1ns;
        cfg.clk_rst_vif.set_active(1'b0, 1'b0);
        #1ps;
        cfg.clk_rst_vif.set_active(1'b1, 1'b1);
        #1ps;
        if (uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", wreq_vif)) begin
          wreq_vif.set_en_assert(1'b0);
          wreq_vif.awvalid_driven = 1'b1;
          wreq_vif.mgr_cb.awvalid <= 1'b1;
          @(posedge cfg.clk_rst_vif.rst_n);
          #1ps;
          wreq_vif.awvalid_driven = 1'b0;
          wreq_vif.mgr_cb.awvalid <= 1'b0;
          repeat (2) @(posedge cfg.clk_rst_vif.clk);
          wreq_vif.set_en_assert(1'b1);
        end
      end
    join
  endtask

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

    // 1. TileLink Command & Data Integrity Error Injection via sec_cm_vif (while err_q == 0, then reset err_q 1->0)
    exercise_tl_intg_errors();

    // 2. Spurious Write-Enable Checker (Read-Only register writes)
    exercise_readonly_reg_writes();

    // 3. Illegal Byte Enables across all 12 registers
    exercise_illegal_byte_enables();

    // 4. Address Miss during Write (Unmapped addresses)
    exercise_unmapped_writes();

    // 5. Unaligned Address Writes (addr_align_err)
    exercise_unaligned_writes();

    // 6. AXI Exclusive Access & Multi-beat Error Propagation
    exercise_exclusive_access();

    // 7. Simultaneous Read and Write Arbitration
    exercise_simultaneous_arb();

    // 8. FIFO Reset with Data (~empty && under_rst on both TX and RX FIFOs)
    exercise_fifo_reset_under_load();

    // 9. Read with Backpressure & Pipelined AR Stalls
    exercise_read_backpressure();

    // 10. Sized AXI Reads (INCR, FIXED, WRAP across size 0, 1, 2, 3)
    exercise_sized_reads();

    // 11. Sized AXI Writes (INCR, FIXED, WRAP across size 0, 1, 2, 3)
    exercise_sized_writes();

    // 12. Write Backpressure & Skidbuffer stall/drain
    exercise_write_backpressure();

    // 13. CDC Random Delay Instrumentation (toggle uart_rx with cdc_instrumentation_enabled = 0 and 1)
    exercise_cdc_rand_delay();

    // 14. Testbench & VIP Interface Coverage (pins_if, clk_rst_if, axi_*_if, tb)
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
                                     bit lock = 1'b0, bit [7:0] id = 8'h0,
                                     bit [31:0] user = 32'h0);
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
      aw_seq.m_fixed_user       = 128'(user);

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
                                 bit [7:0] id = 8'h0, bit user_lsb = 1'b0);
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
      ar_seq.m_fixed_user[0]   = user_lsb;

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
    // Reads with illegal byte mask 4'b0000 on STATUS (4), RDATA (5), FIFO_STATUS (8), and VAL (10)
    // Covers (addr_hit[4/5/8/10] & reg_re & (!reg_error)) [1, 1, 0] in caliptra_ss_uart_reg_top
    send_axi_read_raw(ral.status.get_address(), .mask(4'b0000));
    send_axi_read_raw(ral.rdata.get_address(), .mask(4'b0000));
    send_axi_read_raw(ral.fifo_status.get_address(), .mask(4'b0000));
    send_axi_read_raw(ral.val.get_address(), .mask(4'b0000));
    // Valid reads (mask 4'b1111) to WO registers INTR_TEST (2) and WDATA (6)
    // Covers (addr_hit[2/6] & reg_we & (!reg_error)) [1, 0, 1] in caliptra_ss_uart_reg_top
    send_axi_read_raw(ral.intr_test.get_address(), .mask(4'b1111));
    send_axi_read_raw(ral.wdata.get_address(), .mask(4'b1111));
  endtask

  // Task 3: Address Miss during Write (Unmapped addresses)
  virtual task exercise_unmapped_writes();
    `uvm_info(`gfn, "--- Exercising Unmapped Address Writes ---", UVM_LOW)
    send_axi_write_raw(32'h0000_0040, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0050, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0080, 32'hDEAD_BEEF, 4'b1111);
    send_axi_write_raw(32'h0000_0100, 32'hDEAD_BEEF, 4'b1111);
  endtask

  // Task 4: Unaligned & Sub-word / Mismatched-Mask Address Reads and Writes
  virtual task exercise_unaligned_writes();
    `uvm_info(`gfn, "--- Exercising Unaligned & Sub-word/Mismatched-Mask Reads and Writes ---", UVM_LOW)
    // Unaligned byte writes (size=0)
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 1, 32'h12, 4'b0010, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 2, 32'h3400, 4'b0100, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 3, 32'h5600_0000, 4'b1000, .size(3'd0));
    // Sub-word writes with full/mismatched write strobes (exercises tlul_err mask_size_err & fulldata_chk via sub2tlul)
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1111, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b0010, .size(3'd0));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1111, .size(3'd1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1100, .size(3'd1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b0011, .size(3'd2));
    // Sub-word reads with full/partial masks (exercises tlul_err mask_size_err on Get via sub2tlul)
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b1111));
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b0010));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .mask(4'b1111));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .mask(4'b1100));
    send_axi_read_raw(ral.status.get_address(), .size(3'd2), .mask(4'b0011));
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
          cfg.clk_rst_vif.wait_clks(1);
        end
      end
    join
    // 2-beat INCR write starting at RDATA (0x14, RO -> err=1) to WDATA (0x18, WO -> err=0)
    // Exercises (txn_err || err) with (1, 0) in axi_sub_wr.sv lines 235 and 341
    send_axi_write_custom(ral.rdata.get_address(), 32'h0, 4'b0001, .size(3'd2), .burst(BurstIncr), .len(8'd1));
  endtask

  // Task 6: Simultaneous Read and Write Arbitration across clock offsets
  virtual task exercise_simultaneous_arb();
    `uvm_info(`gfn, "--- Exercising Simultaneous Read/Write Arb ---", UVM_LOW)
    // First issue a standalone Write (sets r_win <= 0) followed immediately by a standalone Read (hits r_dv=1, w_dv=0, r_win=0)
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111);
    send_axi_read_raw(ral.status.get_address());
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

    // 2b. Long INCR write bursts (len=16 and len=8'b1110_1100) starting at RDATA (0x14) / TIMEOUT_CTRL
    // Covers aw_cg.cp_len.long_brst, aw_cg.cx_burst_len[incr][long_brst], axi_sub_wr (txn_err || err) [1, 0],
    // and toggles all awlen[7:0] bits through i_axi_sub_wr.i_req_skd and i_axi_sub_wr.i_axi_addr
    send_axi_write_custom(ral.rdata.get_address(), 32'h0, 4'b0001, .size(3'd2), .burst(BurstIncr), .len(8'd16));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'b1110_1100));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd0));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));

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
    // Sweep bready_delay 1..6 on 2 back-to-back writes so bready=1 coincides with 2nd write rp_valid=1 (covers i_rsp_skd (1,1,1,0))
    for (int bd = 1; bd <= 6; bd++) begin
      fork
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(bd));
        begin
          cfg.clk_rst_vif.wait_clks(1);
          send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0));
        end
      join
    end

    // 2b. Exercise w_cg.cp_stall.zero_wait (send AW first, wait for txn_active/wready=1, then send W)
    // and aw_cg.cp_stall.long_wait (stall AW with awready=0 for >=5 cycles while W beat 1 is delayed)
    begin
      uart_env env;
      if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
        axi_mgr_txn_request_seq       aw0, aw1, aw2;
        axi_mgr_write_single_data_seq w0, w1_0, w1_1, w2;
        axi_mgr_write_response_seq    b0, b1, b2;

        // Zero-wait W: send AW0, wait 4 clocks so wready==1 before wvalid asserts
        aw0 = axi_mgr_txn_request_seq::type_id::create("aw0_zw");
        aw0.m_use_fixed_id = 1'b1; aw0.m_fixed_id = 8'h0;
        aw0.m_use_fixed_addr = 1'b1; aw0.m_fixed_addr = ral.timeout_ctrl.get_address();
        aw0.m_use_fixed_len = 1'b1; aw0.m_fixed_len = 8'd0;
        aw0.m_use_fixed_size = 1'b1; aw0.m_fixed_size = 3'd2;
        aw0.m_use_fixed_burst = 1'b1; aw0.m_fixed_burst = BurstIncr;
        aw0.m_use_fixed_lock = 1'b1; aw0.m_fixed_lock = 1'b0;
        aw0.m_use_fixed_user = 1'b1; aw0.m_fixed_user = 128'h0;

        w0 = axi_mgr_write_single_data_seq::type_id::create("w0_zw");
        w0.m_write_data_item.m_data = 1024'h0;
        w0.m_write_data_item.m_strb = 128'hF;
        w0.m_write_data_item.m_last = 1'b1;
        w0.m_write_data_item.m_user = 512'h0;

        b0 = axi_mgr_write_response_seq::type_id::create("b0_zw");
        b0.m_use_fixed_valid_to_ready_delay = 1'b1;
        b0.m_fixed_valid_to_ready_delay = 0;

        aw0.start(env.m_axi_agent.get_write_request_sequencer());
        cfg.clk_rst_vif.wait_clks(4);
        fork
          env.m_axi_agent.get_write_data_sequencer().execute_item(w0.m_write_data_item);
          b0.start(env.m_axi_agent.get_write_response_sequencer());
        join

        // Long-wait AW: start 2-beat AW1 (len=1) + AW2 (fills i_req_skd) + AW0 (stalls on AW bus for >=6 cycles)
        aw1 = axi_mgr_txn_request_seq::type_id::create("aw1_lw");
        aw1.m_use_fixed_id = 1'b1; aw1.m_fixed_id = 8'h1;
        aw1.m_use_fixed_addr = 1'b1; aw1.m_fixed_addr = ral.timeout_ctrl.get_address();
        aw1.m_use_fixed_len = 1'b1; aw1.m_fixed_len = 8'd1;
        aw1.m_use_fixed_size = 1'b1; aw1.m_fixed_size = 3'd2;
        aw1.m_use_fixed_burst = 1'b1; aw1.m_fixed_burst = BurstFixed;
        aw1.m_use_fixed_lock = 1'b1; aw1.m_fixed_lock = 1'b0;
        aw1.m_use_fixed_user = 1'b1; aw1.m_fixed_user = 128'h0;

        aw2 = axi_mgr_txn_request_seq::type_id::create("aw2_lw");
        aw2.m_use_fixed_id = 1'b1; aw2.m_fixed_id = 8'h2;
        aw2.m_use_fixed_addr = 1'b1; aw2.m_fixed_addr = ral.timeout_ctrl.get_address();
        aw2.m_use_fixed_len = 1'b1; aw2.m_fixed_len = 8'd0;
        aw2.m_use_fixed_size = 1'b1; aw2.m_fixed_size = 3'd2;
        aw2.m_use_fixed_burst = 1'b1; aw2.m_fixed_burst = BurstFixed;
        aw2.m_use_fixed_lock = 1'b1; aw2.m_fixed_lock = 1'b0;
        aw2.m_use_fixed_user = 1'b1; aw2.m_fixed_user = 128'h0;

        w1_0 = axi_mgr_write_single_data_seq::type_id::create("w1_0");
        w1_0.m_write_data_item.m_data = 1024'h0; w1_0.m_write_data_item.m_strb = 128'hF; w1_0.m_write_data_item.m_last = 1'b0; w1_0.m_write_data_item.m_user = 512'h0;
        w1_1 = axi_mgr_write_single_data_seq::type_id::create("w1_1");
        w1_1.m_write_data_item.m_data = 1024'h0; w1_1.m_write_data_item.m_strb = 128'hF; w1_1.m_write_data_item.m_last = 1'b1; w1_1.m_write_data_item.m_user = 512'h0;
        w2 = axi_mgr_write_single_data_seq::type_id::create("w2");
        w2.m_write_data_item.m_data = 1024'h0; w2.m_write_data_item.m_strb = 128'hF; w2.m_write_data_item.m_last = 1'b1; w2.m_write_data_item.m_user = 512'h0;

        b1 = axi_mgr_write_response_seq::type_id::create("b1_lw");
        b1.m_use_fixed_valid_to_ready_delay = 1'b1; b1.m_fixed_valid_to_ready_delay = 0;
        b2 = axi_mgr_write_response_seq::type_id::create("b2_lw");
        b2.m_use_fixed_valid_to_ready_delay = 1'b1; b2.m_fixed_valid_to_ready_delay = 0;

        fork
          begin
            aw1.start(env.m_axi_agent.get_write_request_sequencer());
            aw2.start(env.m_axi_agent.get_write_request_sequencer());
            aw0.start(env.m_axi_agent.get_write_request_sequencer());
          end
          begin
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_0.m_write_data_item);
            cfg.clk_rst_vif.wait_clks(10);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_1.m_write_data_item);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w2.m_write_data_item);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w0.m_write_data_item);
          end
          begin
            b1.start(env.m_axi_agent.get_write_response_sequencer());
            b2.start(env.m_axi_agent.get_write_response_sequencer());
            b0.start(env.m_axi_agent.get_write_response_sequencer());
          end
        join
        // Zero-delay back-to-back W beats during concurrent multi-beat read to exercise i_axi_sub_wr.i_dp_skd r_valid and r_data[36:0]
        w1_0.m_write_data_item.m_data = 1024'hFFFF_FFFF; w1_0.m_write_data_item.m_strb = 128'hF; w1_0.m_write_data_item.m_last = 1'b0;
        w1_1.m_write_data_item.m_data = 1024'hFFFF_FFFF; w1_1.m_write_data_item.m_strb = 128'hF; w1_1.m_write_data_item.m_last = 1'b1;
        fork
          send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd7));
          begin
            aw1.start(env.m_axi_agent.get_write_request_sequencer());
            aw2.start(env.m_axi_agent.get_write_request_sequencer());
          end
          begin
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_0.m_write_data_item);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_1.m_write_data_item);
            w2.m_write_data_item.m_data = 1024'h0000_0000; w2.m_write_data_item.m_strb = 128'h0; w2.m_write_data_item.m_last = 1'b1;
            env.m_axi_agent.get_write_data_sequencer().execute_item(w2.m_write_data_item);
          end
          begin
            b1.start(env.m_axi_agent.get_write_response_sequencer());
            b2.start(env.m_axi_agent.get_write_response_sequencer());
          end
        join
      end
    end

    // 3. Exercise intr_hw_tx_empty and intr_hw_tx_watermark with event_intr_i == 0 and intr_test_q == 1
    // Fill all 64 entries of TX FIFO while TX is disabled so txlvl[6:0] toggles 0->64, then enable
    // system loopback at max NCO so all 64 bytes transfer into RX FIFO (toggling rxlvl[6:0] 0->64->0)
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK)); // watermark = 1 byte
    for (int i = 0; i < 64; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'h30 + i), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    csr_wr(.ptr(ral.intr_test), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    // Enable tx=1, rx=1, slpbk=1, nco=16'hFFFF to loop all 64 bytes into RX FIFO
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(11500);
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK)); // rxrst | txrst
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask

  // Task 12: CDC Random Delay & UART Break State Machine Stimulus (BRK_CHK <-> BRK_WAIT across rxblvl 0..3)
  virtual task exercise_cdc_rand_delay();
    `uvm_info(`gfn, "--- Exercising CDC Rand Delay & UART Break FSM across rxblvl 0..3 ---", UVM_LOW)
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    repeat (32) begin
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      #2ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      #2ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(2);
      #1ns;
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(2);
    end
    // Exercise break_st_q (BRK_CHK -> BRK_WAIT -> BRK_CHK) and break_err (0 -> 1 -> 0) across all 4 rxblvl levels
    for (int blvl = 0; blvl < 4; blvl++) begin
      csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0002 | (blvl << 8)), .predict(1'b0), .check(UVM_NO_CHECK));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(400 * (1 << blvl));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(64);
      csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    begin
      uvm_reg_adapter adapter = ral.default_map.get_adapter();
      uvm_reg_data_t dummy_rdata;
      uart_reg_access_err_vseq parent_seq = uart_reg_access_err_vseq::type_id::create("parent_seq");
      adapter.parent_sequence = parent_seq;
      csr_wr(.ptr(ral.timeout_ctrl), .value('0), .predict(1'b0), .check(UVM_NO_CHECK));
      csr_rd(.ptr(ral.status), .value(dummy_rdata), .check(UVM_NO_CHECK));
      adapter.parent_sequence = null;
    end
  endtask

  // Task 13: Exercise Testbench & VIP Interfaces via Virtual Interface API Methods Only (no force/deposit)
  virtual task exercise_tb_and_vip_interfaces();
    virtual axi_write_request_if  wreq_vif;
    virtual axi_write_data_if     wdat_vif;
    virtual axi_write_response_if wrsp_vif;
    virtual axi_read_request_if   rreq_vif;
    virtual axi_read_data_if      rdat_vif;
    virtual pins_if #(1)          intg_err_vif;

    `uvm_info(`gfn, "--- Exercising Testbench & VIP Interfaces via API calls (no force/deposit) ---", UVM_LOW)

    // 1. Exercise pins_if (cfg.intr_vif and intg_err_vif) via virtual interface API methods
    csr_wr(.ptr(ral.intr_enable), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    // 1a. Pullup enabled when pins_oe transitions 1 -> 0
    cfg.intr_vif.set_pullup_en('1);
    cfg.intr_vif.set_pulldown_en('0);
    cfg.intr_vif.drive('1);
    #1ns;
    cfg.intr_vif.drive_en('0);
    #1ns;
    // 1b. Pulldown enabled when pins_oe transitions 1 -> 0
    cfg.intr_vif.set_pullup_en('0);
    cfg.intr_vif.set_pulldown_en('1);
    cfg.intr_vif.drive('0);
    #1ns;
    cfg.intr_vif.drive_en('0);
    #1ns;
    // 1c. Neither pullup nor pulldown enabled when pins_oe transitions 1 -> 0
    cfg.intr_vif.set_pulldown_en('0);
    cfg.intr_vif.drive('1);
    #1ns;
    cfg.intr_vif.disconnect();
    #1ns;

    if (uvm_config_db#(virtual pins_if #(1))::get(null, "*.env", "intg_error_vif", intg_err_vif)) begin
      intg_err_vif.set_pullup_en(1'b1);
      intg_err_vif.set_pulldown_en(1'b0);
      intg_err_vif.drive(1'b1);
      #1ns;
      intg_err_vif.drive_en(1'b0);
      #1ns;
      intg_err_vif.set_pullup_en(1'b0);
      intg_err_vif.set_pulldown_en(1'b1);
      intg_err_vif.drive(1'b0);
      #1ns;
      intg_err_vif.drive_en(1'b0);
      #1ns;
      intg_err_vif.set_pulldown_en(1'b0);
      intg_err_vif.drive(1'b1);
      #1ns;
      intg_err_vif.disconnect();
      #1ns;
    end

    // 2. Exercise clk_rst_if API methods across clock edges
    cfg.clk_rst_vif.wait_n_clks(1);
    cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b0));
    cfg.clk_rst_vif.set_period_ps(cfg.clk_rst_vif.clk_period_ps);
    cfg.clk_rst_vif.set_freq_mhz(50);
    cfg.clk_rst_vif.set_duty_cycle(50);
    cfg.clk_rst_vif.set_active(1'b1, 1'b1);
    #1ns;
    begin
      int orig_period_ps = cfg.clk_rst_vif.clk_period_ps;
      uvm_top.set_report_severity_id_override(UVM_FATAL, cfg.clk_rst_vif.msg_id, UVM_INFO);
      cfg.clk_rst_vif.set_period_ps(2000000);
      cfg.clk_rst_vif.set_active(1'b1, 1'b1);
      #1ps;
      uvm_top.set_report_id_verbosity(cfg.clk_rst_vif.msg_id, -1);
      uvm_top.set_report_severity_id_verbosity(UVM_FATAL, cfg.clk_rst_vif.msg_id, -1);
      uvm_top.set_report_severity_id_verbosity(UVM_INFO,  cfg.clk_rst_vif.msg_id, -1);
      cfg.clk_rst_vif.set_active(1'b1, 1'b1);
      #1ps;
      cfg.clk_rst_vif.set_period_ps(orig_period_ps);
      uvm_top.set_report_id_verbosity(cfg.clk_rst_vif.msg_id, UVM_LOW);
      uvm_top.set_report_severity_id_verbosity(UVM_FATAL, cfg.clk_rst_vif.msg_id, UVM_LOW);
      uvm_top.set_report_severity_id_verbosity(UVM_INFO,  cfg.clk_rst_vif.msg_id, UVM_LOW);
      #1ps;
    end
    cfg.clk_rst_vif.set_freq_scaling(10, 50, 1'b1);
    cfg.clk_rst_vif.wait_clks(16);
    cfg.clk_rst_vif.set_freq_scaling(10, 50, 1'b0);
    cfg.clk_rst_vif.wait_clks(16);
    cfg.clk_rst_vif.set_freq_scaling(0, 0, 1'b0);
    cfg.clk_rst_vif.set_max_jitter_ps(10);
    cfg.clk_rst_vif.set_jitter_chance_pc(50);
    cfg.clk_rst_vif.wait_clks(20);
    cfg.clk_rst_vif.set_max_jitter_ps(0);
    cfg.clk_rst_vif.set_jitter_chance_pc(0);
    cfg.clk_rst_vif.wait_clks(2);
    cfg.clk_rst_vif.set_sole_clock(1'b0);
    cfg.clk_rst_vif.stop_clk();
    cfg.clk_rst_vif.start_clk(1'b0);
    cfg.clk_rst_vif.stop_clk();
    cfg.clk_rst_vif.start_clk(1'b1);

    // 3. Exercise axi_*_if configuration API methods
    // First drive awid[0]=1, awuser[0]=1, arid[0]=1, aruser[0]=1 so bit-0 mask=0 conditions are covered
    send_axi_write_custom(.addr(32'h14), .data(32'h0), .strb(4'hF), .id(8'hFF), .user(32'hFFFF_FFFF));
    send_axi_read_raw(.addr(32'h10), .id(8'hFF), .user_lsb(1'b1));
    cfg.clk_rst_vif.wait_clks(2);
    if (uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", wreq_vif)) begin
      string ids[$] = '{"tb.axi_write_req_if.set_id_w_width",
                        "tb.axi_write_req_if.set_addr_width",
                        "tb.axi_write_req_if.set_user_req_width"};
      wreq_vif.set_en_assert(1'b0);
      #1ps;
      foreach (ids[i]) uvm_top.set_report_severity_id_override(UVM_ERROR, ids[i], UVM_INFO);
      wreq_vif.set_id_w_width(33);      #1ps;
      wreq_vif.set_addr_width(0);       #1ps;
      wreq_vif.set_addr_width(65);      #1ps;
      wreq_vif.set_user_req_width(129); #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], -1);
      end
      wreq_vif.set_id_w_width(33);      #1ps;
      wreq_vif.set_addr_width(0);       #1ps;
      wreq_vif.set_addr_width(65);      #1ps;
      wreq_vif.set_user_req_width(129); #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], UVM_LOW);
      end
      wreq_vif.set_id_w_width(0);       #1ps;
      wreq_vif.set_user_req_width(0);   #1ps;
      wreq_vif.set_id_w_width(top_pkg::TL_AIW - 1); #1ps;
      wreq_vif.set_addr_width(31);      #1ps;
      wreq_vif.set_user_req_width(31);  #1ps;
      wreq_vif.set_id_w_width(top_pkg::TL_AIW); #1ps;
      wreq_vif.set_addr_width(32);      #1ps;
      wreq_vif.set_user_req_width(32);  #1ps;
      wreq_vif.if_mode = dv_utils_pkg::Device; #1ps;
      wreq_vif.if_mode = dv_utils_pkg::Host;   #1ps;
      wreq_vif.set_en_assert(1'b1);     #1ps;
    end
    if (uvm_config_db#(virtual axi_write_data_if)::get(null, "*", "write_data_vif", wdat_vif)) begin
      string ids[$] = '{"tb.axi_write_dat_if.set_data_width",
                        "tb.axi_write_dat_if.set_user_data_width"};
      wdat_vif.set_en_assert(1'b0);
      #1ps;
      foreach (ids[i]) uvm_top.set_report_severity_id_override(UVM_ERROR, ids[i], UVM_INFO);
      wdat_vif.set_user_data_width(0);   #1ps;
      wdat_vif.set_data_width(0);        #1ps;
      wdat_vif.set_user_data_width(32);  #1ps;
      wdat_vif.set_data_width(8);        #1ps;
      wdat_vif.set_data_width(16);       #1ps;
      wdat_vif.set_data_width(32);       #1ps;
      wdat_vif.set_user_data_width(17);  #1ps;
      wdat_vif.set_user_data_width(513); #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], -1);
      end
      wdat_vif.set_user_data_width(0);   #1ps;
      wdat_vif.set_data_width(0);        #1ps;
      wdat_vif.set_user_data_width(32);  #1ps;
      wdat_vif.set_data_width(8);        #1ps;
      wdat_vif.set_data_width(32);       #1ps;
      wdat_vif.set_user_data_width(17);  #1ps;
      wdat_vif.set_user_data_width(513); #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], UVM_LOW);
      end
      wdat_vif.set_user_data_width(1);   #1ps;
      wdat_vif.set_data_width(32);       #1ps;
      wdat_vif.set_user_data_width(0);   #1ps;
      wdat_vif.if_mode = dv_utils_pkg::Device; #1ps;
      wdat_vif.if_mode = dv_utils_pkg::Host;   #1ps;
      wdat_vif.set_en_assert(1'b1);      #1ps;
    end
    if (uvm_config_db#(virtual axi_write_response_if)::get(null, "*", "write_response_vif", wrsp_vif)) begin
      string ids[$] = '{"tb.axi_write_rsp_if.set_id_w_width",
                        "tb.axi_write_rsp_if.set_bresp_width",
                        "tb.axi_write_rsp_if.set_user_resp_width"};
      wrsp_vif.set_en_assert(1'b0);
      #1ps;
      foreach (ids[i]) uvm_top.set_report_severity_id_override(UVM_ERROR, ids[i], UVM_INFO);
      wrsp_vif.set_id_w_width(33);       #1ps;
      wrsp_vif.set_user_resp_width(17);  #1ps;
      wrsp_vif.set_bresp_width(1);       #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], -1);
      end
      wrsp_vif.set_id_w_width(33);       #1ps;
      wrsp_vif.set_bresp_width(1);       #1ps;
      wrsp_vif.set_user_resp_width(17);  #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], UVM_LOW);
      end
      wrsp_vif.set_id_w_width(top_pkg::TL_AIW - 1); #1ps;
      wrsp_vif.set_bresp_width(0);       #1ps;
      wrsp_vif.set_user_resp_width(1);   #1ps;
      wrsp_vif.set_id_w_width(top_pkg::TL_AIW); #1ps;
      wrsp_vif.set_bresp_width(2);       #1ps;
      wrsp_vif.set_user_resp_width(16);  #1ps;
      wrsp_vif.if_mode = dv_utils_pkg::Device; #1ps;
      wrsp_vif.if_mode = dv_utils_pkg::Host;   #1ps;
      wrsp_vif.set_en_assert(1'b1);      #1ps;
    end
    if (uvm_config_db#(virtual axi_read_request_if)::get(null, "*", "read_request_vif", rreq_vif)) begin
      string ids[$] = '{"tb.axi_read_req_if.set_id_r_width",
                        "tb.axi_read_req_if.set_addr_width",
                        "tb.axi_read_req_if.set_user_req_width"};
      rreq_vif.set_en_assert(1'b0);
      #1ps;
      foreach (ids[i]) uvm_top.set_report_severity_id_override(UVM_ERROR, ids[i], UVM_INFO);
      rreq_vif.set_id_r_width(33);       #1ps;
      rreq_vif.set_addr_width(0);        #1ps;
      rreq_vif.set_addr_width(65);       #1ps;
      rreq_vif.set_user_req_width(129);  #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], -1);
      end
      rreq_vif.set_id_r_width(33);       #1ps;
      rreq_vif.set_addr_width(0);        #1ps;
      rreq_vif.set_addr_width(65);       #1ps;
      rreq_vif.set_user_req_width(129);  #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], UVM_LOW);
      end
      rreq_vif.set_id_r_width(0);        #1ps;
      rreq_vif.set_user_req_width(0);    #1ps;
      rreq_vif.set_id_r_width(top_pkg::TL_AIW - 1); #1ps;
      rreq_vif.set_addr_width(31);       #1ps;
      rreq_vif.set_user_req_width(31);   #1ps;
      rreq_vif.set_id_r_width(top_pkg::TL_AIW); #1ps;
      rreq_vif.set_addr_width(32);       #1ps;
      rreq_vif.set_user_req_width(32);   #1ps;
      rreq_vif.if_mode = dv_utils_pkg::Device; #1ps;
      rreq_vif.if_mode = dv_utils_pkg::Host;   #1ps;
      rreq_vif.set_en_assert(1'b1);      #1ps;
    end
    if (uvm_config_db#(virtual axi_read_data_if)::get(null, "*", "read_data_vif", rdat_vif)) begin
      string ids[$] = '{"tb.axi_read_dat_if.set_id_r_width",
                        "tb.axi_read_dat_if.set_data_width",
                        "tb.axi_read_dat_if.set_user_data_width",
                        "tb.axi_read_dat_if.set_rresp_width",
                        "tb.axi_read_dat_if.set_user_resp_width"};
      rdat_vif.set_en_assert(1'b0);
      #1ps;
      foreach (ids[i]) uvm_top.set_report_severity_id_override(UVM_ERROR, ids[i], UVM_INFO);
      rdat_vif.set_user_data_width(0);   #1ps;
      rdat_vif.set_id_r_width(33);       #1ps;
      rdat_vif.set_data_width(0);        #1ps;
      rdat_vif.set_user_data_width(32);  #1ps;
      rdat_vif.set_data_width(8);        #1ps;
      rdat_vif.set_data_width(16);       #1ps;
      rdat_vif.set_data_width(32);       #1ps;
      rdat_vif.set_user_data_width(17);  #1ps;
      rdat_vif.set_user_data_width(513); #1ps;
      rdat_vif.set_user_resp_width(17);  #1ps;
      rdat_vif.set_rresp_width(1);       #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], -1);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], -1);
      end
      rdat_vif.set_user_data_width(0);   #1ps;
      rdat_vif.set_id_r_width(33);       #1ps;
      rdat_vif.set_data_width(0);        #1ps;
      rdat_vif.set_user_data_width(32);  #1ps;
      rdat_vif.set_data_width(8);        #1ps;
      rdat_vif.set_data_width(32);       #1ps;
      rdat_vif.set_user_data_width(17);  #1ps;
      rdat_vif.set_user_data_width(513); #1ps;
      rdat_vif.set_rresp_width(1);       #1ps;
      rdat_vif.set_user_resp_width(17);  #1ps;
      foreach (ids[i]) begin
        uvm_top.set_report_id_verbosity(ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_ERROR, ids[i], UVM_LOW);
        uvm_top.set_report_severity_id_verbosity(UVM_INFO,  ids[i], UVM_LOW);
      end
      rdat_vif.set_id_r_width(top_pkg::TL_AIW - 1); #1ps;
      rdat_vif.set_user_data_width(1);   #1ps;
      rdat_vif.set_rresp_width(0);       #1ps;
      rdat_vif.set_user_resp_width(1);   #1ps;
      rdat_vif.set_id_r_width(top_pkg::TL_AIW); #1ps;
      rdat_vif.set_data_width(32);       #1ps;
      rdat_vif.set_user_data_width(0);   #1ps;
      rdat_vif.set_rresp_width(2);       #1ps;
      rdat_vif.set_user_resp_width(16);  #1ps;
      rdat_vif.if_mode = dv_utils_pkg::Device; #1ps;
      rdat_vif.if_mode = dv_utils_pkg::Host;   #1ps;
      rdat_vif.set_en_assert(1'b1);      #1ps;
    end
  endtask

  // Task 15: TileLink command and data integrity errors via sec_cm_vif
  virtual task exercise_tl_intg_errors();
    bit [31:0] ro_addrs[4];
    bit [31:0] rw_addrs[8];
    virtual axi_read_data_if rdat_vif;
    if (cfg.sec_cm_vif == null) return;
    `uvm_info(`gfn, "--- Exercising TileLink Command and Data Integrity Errors ---", UVM_LOW)

    // 0a. Drive real AXI writes to all 8 writeable registers while u_reg.err_q == 0 and intg_err == 0
    // Naturally exercises u_caliptra_prim_onehot_check single-hot oh_i == (1 << b) with matching addr_i == b
    rw_addrs = '{
      ral.intr_state.get_address(),
      ral.intr_enable.get_address(),
      ral.intr_test.get_address(),
      ral.ctrl.get_address(),
      ral.wdata.get_address(),
      ral.fifo_ctrl.get_address(),
      ral.ovrd.get_address(),
      ral.timeout_ctrl.get_address()
    };
    foreach (rw_addrs[i]) begin
      send_axi_write_raw(rw_addrs[i], 32'h0, 4'b1111);
    end

    // 0b. Exercise remaining onehot_check fault-injection and tied-off RO corners while u_reg.err_q == 0
    cfg.sec_cm_vif.exercise_pre_intg_corners();

    // 1. Sweep all 127 non-zero command integrity ECC masks across complementary command patterns
    for (int m = 1; m < 128; m++) begin
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(128 + m);
        send_axi_write_raw(32'h0000_0000, 32'h0, 4'b0000);
      join
      cfg.clk_rst_vif.wait_clks(2);
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(128 + m);
        send_axi_write_raw(32'hFFFF_FFFC, 32'h0, 4'b1111);
      join
      cfg.clk_rst_vif.wait_clks(2);
    end

    // 2. Sweep all 127 non-zero data integrity ECC masks across all-0 and all-1 write data
    for (int m = 1; m < 128; m++) begin
      fork
        cfg.sec_cm_vif.inject_data_intg_flip(128 + m);
        send_axi_write_raw(ral.ctrl.get_address(), 32'h0000_0000, 4'b1111);
      join
      cfg.clk_rst_vif.wait_clks(2);
      fork
        cfg.sec_cm_vif.inject_data_intg_flip(128 + m);
        send_axi_write_raw(ral.ctrl.get_address(), 32'hFFFF_FFFF, 4'b1111);
      join
      cfg.clk_rst_vif.wait_clks(2);
    end

    // 3. Flip command integrity during reads to RO registers (status, rdata, fifo_status, val)
    // Temporarily disable rdat_vif X-check assertion during forced cmd_intg read error injection
    if (uvm_config_db#(virtual axi_read_data_if)::get(null, "*", "read_data_vif", rdat_vif)) begin
      rdat_vif.set_en_assert(1'b0);
    end
    ro_addrs = '{
      ral.status.get_address(),
      ral.rdata.get_address(),
      ral.fifo_status.get_address(),
      ral.val.get_address()
    };
    foreach (ro_addrs[i]) begin
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(0);
        send_axi_read_raw(ro_addrs[i], .mask(4'b1111));
      join
      cfg.clk_rst_vif.wait_clks(2);
    end
    fork
      cfg.sec_cm_vif.inject_cmd_intg_flip(128 + 7'h15);
      send_axi_read_raw(ro_addrs[0], .mask(4'b1111));
    join
    cfg.clk_rst_vif.wait_clks(2);
    if (rdat_vif != null) begin
      rdat_vif.set_en_assert(1'b1);
    end

    // 4. Exercise break_st_q default branch via sec_cm_vif
    cfg.sec_cm_vif.exercise_uart_core_break_default();

    // Reset once to clear err_q (1 -> 0) and intg_err_o (1 -> 0) before exercise_readonly_reg_writes()
    apply_reset("HARD");
    ral.reset("HARD");
    cfg.clk_rst_vif.wait_clks(4);
    init_uart_cfg();
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
  endtask

endclass : uart_reg_access_err_vseq
