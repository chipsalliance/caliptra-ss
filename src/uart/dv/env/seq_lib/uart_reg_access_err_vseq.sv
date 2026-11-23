// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: uart_cond_cov (uart_reg_access_err_vseq)
// Comprehensive sequence specifically targeting CONDITION, EXPRESSION, LINE, and BRANCH coverage:
// 1. Illegal Byte Enables: Exercises all 12 sub-conditions in uart_reg_top.sv line 1561:
//    (addr_hit[i] & (|(UART_PERMIT[i] & ~reg_be))) for all 12 registers, asserting wr_err and reg_error.
// 2. Register WE gating with reg_error: Exercises condition (addr_hit[i] & reg_we & !reg_error) with
//    inputs (1, 1, 0) across all write-enabled registers in uart_reg_top.sv.
// 3. Read-Only Register Write Immunity & Spurious Write-Enable Fault: Verifies writes to RO registers
//    (STATUS, RDATA, FIFO_STATUS, VAL) leave register values unchanged (reg_we_check[4,5,8,10]=1'b0,
//    StrictCheck=0 so reg_we_err=0), while exercise_tl_intg_errors() triggers (intg_err || reg_we_err)
//    with (0, 1) and (err_q | intg_err | reg_we_err) with (0, 0, 1) via inject_spurious_idle_we().
// 4. Address Miss during Write: Exercises (reg_we && !addrmiss) with (1, 0) and
//    ((reg_re || reg_we) ? ~|addr_hit : 1'b0) with reg_we=1 by writing to unmapped addresses.
// 5. Sub-Word / Unaligned Address Writes: Exercises sub-word AXI addresses and byte-strobe masking
//    through axi_sub (axi_sub aligns addr[1:0]=2'b00 before sub2tlul; tlul_adapter_reg.addr_align_err
//    is excluded in uart_cov_excl.el).
// 6. AXI Lock Signaling (EX_EN=0): Exercises awlock=1 / arlock=1 transactions to cover cp_lock
//    and confirm OKAY completion when EX_EN=0 (EXOKAY excluded in uart_cov_excl.el).
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

    // 1. TileLink Command & Data Integrity Error Injection via sec_cm_vif (while err_q == 0, then reset err_q 1->0)
    exercise_tl_intg_errors();

    // 2. Read-Only register write immunity (STATUS, RDATA, FIFO_STATUS, VAL)
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
                                  bit exclusive_lock = 1'b0, bit [2:0] size = 3'd2,
                                  bit check_err = 1'b0, bit exp_err = 1'b1);
    axi_mgr_agent            axi_agent  = get_axi_agent();
    axi_mgr_write_fixed_vseq write_vseq = axi_mgr_write_fixed_vseq::type_id::create("write_vseq_raw");
    write_vseq.set_sequencers(axi_agent.get_write_request_sequencer(),
                              axi_agent.get_write_data_sequencer(),
                              axi_agent.get_write_response_sequencer());
    write_vseq.set_write_response_router(axi_agent.get_write_response_router());
    if (!write_vseq.randomize() with {
          m_fixed_req.m_addr == addr;
          m_fixed_req.m_size == size;
          m_fixed_req.m_id < 256;
          m_fixed_req.m_user[127:32] == '0;
          m_fixed_req.m_lock == local::exclusive_lock;
          m_fixed_req.m_write_data_item.m_data == 1024'(data);
          m_fixed_req.m_write_data_item.m_strb == 128'(strb);
          m_fixed_req.m_write_data_item.m_last == 1'b1;
          m_fixed_req.m_write_data_item.m_user == 512'h0;
        }) begin
      `uvm_fatal(get_full_name(), "Failed to randomize write_vseq.")
    end
    write_vseq.start(null);
    if (check_err && !cfg.under_reset && cfg.clk_rst_vif.rst_n &&
        write_vseq.rsp != null && write_vseq.rsp.m_write_response != null) begin
      axi_write_response_item::bresp_e exp_bresp = exp_err ?
          axi_write_response_item::BRespSlverr : axi_write_response_item::BRespOkay;
      `DV_CHECK_EQ(write_vseq.rsp.m_write_response.m_resp, exp_bresp,
                   $sformatf("Write response mismatch at addr=0x%0h (strb=4'b%04b)", addr, strb))
    end
  endtask

  // Task 1: Read-Only register write immunity (STATUS, RDATA, FIFO_STATUS, VAL)
  virtual task exercise_readonly_reg_writes();
    uvm_reg_data_t rdata;
    `uvm_info(`gfn, "--- Exercising Read-Only Register Writes (Write Immunity) ---", UVM_LOW)
    // Write to STATUS (0x10) - Read-only; verify value is not overwritten
    send_axi_write_raw(ral.status.get_address(), 32'hDEAD_BEEF, 4'b0001);
    csr_rd(.ptr(ral.status), .value(rdata), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_NE(rdata[7:0], 8'hEF, "RO register STATUS must not be overwritten")
    // Write to RDATA (0x14) - Read-only; verify value is not overwritten
    send_axi_write_raw(ral.rdata.get_address(), 32'hDEAD_BEEF, 4'b0001);
    csr_rd(.ptr(ral.rdata), .value(rdata), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(rdata[7:0], 8'h00, "RO register RDATA must remain 0 when RX FIFO is empty")
    // Write to FIFO_STATUS (0x20) - Read-only; verify value is not overwritten
    send_axi_write_raw(ral.fifo_status.get_address(), 32'hDEAD_BEEF, 4'b0111);
    csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(rdata, 32'h0, "RO register FIFO_STATUS must remain 0 when FIFOs are empty")
    // Write to VAL (0x28) - Read-only; verify value is not overwritten
    send_axi_write_raw(ral.val.get_address(), 32'hDEAD_BEEF, 4'b0011);
    csr_rd(.ptr(ral.val), .value(rdata), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_NE(rdata[15:0], 16'hBEEF, "RO register VAL must not be overwritten")
  endtask

  // Task 2: Illegal Byte Enables across all 12 registers
  virtual task exercise_illegal_byte_enables();
    `uvm_info(`gfn, "--- Exercising Illegal Byte Enables across all registers ---", UVM_LOW)
    // Register 0: INTR_STATE (offset 0x00, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_state.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    // Register 1: INTR_ENABLE (offset 0x04, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_enable.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    // Register 2: INTR_TEST (offset 0x08, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.intr_test.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    // Register 3: CTRL (offset 0x0C, permit 4'b1111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.ctrl.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.ctrl.get_address(), 32'h3, 4'b0011, .check_err(1'b1), .exp_err(1'b1));
    // Register 4: STATUS (offset 0x10, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.status.get_address(), 32'h2, 4'b0010, .check_err(1'b1), .exp_err(1'b1));
    // Register 5: RDATA (offset 0x14, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.rdata.get_address(), 32'h2, 4'b0010, .check_err(1'b1), .exp_err(1'b1));
    // Register 6: WDATA (offset 0x18, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.wdata.get_address(), 32'h2, 4'b0010, .check_err(1'b1), .exp_err(1'b1));
    // Register 7: FIFO_CTRL (offset 0x1C, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.fifo_ctrl.get_address(), 32'h2, 4'b0010, .check_err(1'b1), .exp_err(1'b1));
    // Register 8: FIFO_STATUS (offset 0x20, permit 4'b0111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.fifo_status.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.fifo_status.get_address(), 32'h3, 4'b0011, .check_err(1'b1), .exp_err(1'b1));
    // Register 9: OVRD (offset 0x24, permit 4'b0001) - write with wstrb 4'b0010
    send_axi_write_raw(ral.ovrd.get_address(), 32'h2, 4'b0010, .check_err(1'b1), .exp_err(1'b1));
    // Register 10: VAL (offset 0x28, permit 4'b0011) - write with wstrb 4'b0001
    send_axi_write_raw(ral.val.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    // Register 11: TIMEOUT_CTRL (offset 0x2C, permit 4'b1111) - write with wstrb 4'b0001, 4'b0011
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h3, 4'b0011, .check_err(1'b1), .exp_err(1'b1));
    // Reads with sub-word size (size=0) and full mask on STATUS (4), RDATA (5), FIFO_STATUS (8), and VAL (10)
    // Covers (addr_hit[4/5/8/10] & reg_re & (!reg_error)) [1, 1, 0] in caliptra_ss_uart_reg_top
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.rdata.get_address(), .size(3'd0), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.fifo_status.get_address(), .size(3'd0), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.val.get_address(), .size(3'd0), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b0000));
    // Valid reads (mask 4'b1111) to WO registers INTR_TEST (2) and WDATA (6)
    // Covers (addr_hit[2/6] & reg_we & (!reg_error)) [1, 0, 1] in caliptra_ss_uart_reg_top
    send_axi_read_raw(ral.intr_test.get_address(), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b0));
    send_axi_read_raw(ral.wdata.get_address(), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b0));
  endtask

  // Task 3: Address Miss during Write (Unmapped addresses in 6-bit register aperture: 0x30..0x3C)
  virtual task exercise_unmapped_writes();
    `uvm_info(`gfn, "--- Exercising Unmapped Address Writes ---", UVM_LOW)
    send_axi_write_raw(32'h0000_0030, 32'hDEAD_BEEF, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(32'h0000_0034, 32'hDEAD_BEEF, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(32'h0000_0038, 32'hDEAD_BEEF, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(32'h0000_003C, 32'hDEAD_BEEF, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
  endtask

  // Task 4: Unaligned & Sub-word / Mismatched-Mask Address Reads and Writes
  virtual task exercise_unaligned_writes();
    `uvm_info(`gfn, "--- Exercising Unaligned & Sub-word/Mismatched-Mask Reads and Writes ---", UVM_LOW)
    // Unaligned byte writes (size=0) -> verify BRespSlverr
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 1, 32'h12, 4'b0010, .size(3'd0), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 2, 32'h3400, 4'b0100, .size(3'd0), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address() + 3, 32'h5600_0000, 4'b1000, .size(3'd0), .check_err(1'b1), .exp_err(1'b1));
    // Sub-word writes with full/mismatched write strobes (exercises tlul_err mask_size_err & fulldata_chk via sub2tlul)
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1111, .size(3'd0), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b0010, .size(3'd0), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1111, .size(3'd1), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b1100, .size(3'd1), .check_err(1'b1), .exp_err(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h1234_5678, 4'b0011, .size(3'd2), .check_err(1'b1), .exp_err(1'b1));
    // Sub-word reads with full/partial masks (exercises tlul_err mask_size_err on Get via sub2tlul)
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd0), .mask(4'b0010), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd1), .mask(4'b1100), .check_err(1'b1), .exp_err(1'b1));
    send_axi_read_raw(ral.status.get_address(), .size(3'd2), .mask(4'b0011));
  endtask

  // Task 5: AXI Exclusive Access & Multi-beat Error Propagation
  virtual task exercise_exclusive_access();
    `uvm_info(`gfn, "--- Exercising AXI Exclusive Access (lock = 1) & Multi-beat Error Propagation ---", UVM_LOW)
    send_axi_read_raw(ral.status.get_address(), .exclusive_lock(1'b1));
    send_axi_write_raw(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .exclusive_lock(1'b1));
    // Exclusive write (lock = 1) completes with OKAY when EX_EN = 0 in uart_axi
    send_axi_write_custom(ral.ctrl.get_address(), 32'h0, 4'b1111, .lock(1'b1));
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
    uvm_reg_data_t fstat;
    `uvm_info(`gfn, "--- Exercising FIFO Reset Under Load (~empty && under_rst) ---", UVM_LOW)
    // Ensure TX/RX FIFOs are empty and TX is disabled before loading 4 bytes
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    // 1. Put data in TX FIFO and reset TX FIFO while not empty
    for (int i = 0; i < 4; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'hA0 + i), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    cfg.clk_rst_vif.wait_clks(2);
    csr_rd(.ptr(ral.fifo_status), .value(fstat), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(fstat[7:0], 8'd4, "TX FIFO depth must be 4 before txrst")
    // Pulse txrst
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h2), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_rd(.ptr(ral.fifo_status), .value(fstat), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(fstat[7:0], 8'd0, "TX FIFO depth must be 0 after txrst")

    // 2. Enable system loopback with high NCO to quickly load RX FIFO, then pulse rxrst while RX FIFO is not empty
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK)); // nco=0xFFFF, slpbk=1, rx=1, tx=1
    csr_wr(.ptr(ral.wdata), .value(32'h55), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(400);
    csr_rd(.ptr(ral.fifo_status), .value(fstat), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(fstat[23:16], 8'd1, "RX FIFO depth must be 1 before rxrst")
    // Pulse rxrst + txrst while RX FIFO is non-empty
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_rd(.ptr(ral.fifo_status), .value(fstat), .check(UVM_NO_CHECK));
    if (!cfg.under_reset) `DV_CHECK_EQ(fstat[23:16], 8'd0, "RX FIFO depth must be 0 after rxrst")
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask

  // Task 8: Read with Backpressure & Pipelined AR Stalls (arvalid=1, arready=0)
  virtual task exercise_read_backpressure();
    `uvm_info(`gfn, "--- Exercising Read Backpressure & Pipelined AR Stalls ---", UVM_LOW)
    for (int d = 1; d <= 5; d++) begin
      send_axi_read_raw(ral.status.get_address(), .rready_delay(d), .check_err(1'b1), .exp_err(1'b0));
      // Verify TL-UL d_error read response is translated to RRespSlverr and preserved through backpressure
      send_axi_read_raw(32'h0000_0030, .rready_delay(d), .check_err(1'b1), .exp_err(1'b1));
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
      send_axi_read_raw(32'h0000_0030, .id(8'(1 << b)));
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
      send_axi_write_custom(32'h0000_0030, 32'h0, 4'b1111, .id(8'(1 << b)));
    end
  endtask

  // Task 11: Write Backpressure, Skid Buffer, and sub2tlul WRITE_WAIT FSM state
  virtual task exercise_write_backpressure();
    `uvm_info(`gfn, "--- Exercising Write Backpressure, Skid Buffer, and sub2tlul WRITE_WAIT ---", UVM_LOW)
    // 1. Multi-beat write (len=1) with pipelined second write to exercise i_req_skd line 145 while txn_active
    fork
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1), .id(8'h1));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd0), .id(8'h2));
      end
    join

    // 2. 3-write pipelined sequence with B backpressure (fills i_rsp_skd and stalls i_req_skd)
    fork
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(20), .id(8'h1));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0), .id(8'h2));
      end
      begin
        cfg.clk_rst_vif.wait_clks(2);
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0), .id(8'h3));
      end
    join
    // Sweep bready_delay 1..6 on 2 back-to-back writes so bready=1 coincides with 2nd write rp_valid=1 (covers i_rsp_skd (1,1,1,0))
    for (int bd = 1; bd <= 6; bd++) begin
      fork
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(bd), .id(8'h1), .check_err(1'b1), .exp_err(1'b0));
        begin
          cfg.clk_rst_vif.wait_clks(1);
          send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0), .id(8'h2), .check_err(1'b1), .exp_err(1'b0));
        end
      join
      // Verify TL-UL d_error write response is translated to BRespSlverr and preserved through backpressure
      send_axi_write_custom(32'h0000_0030, 32'hDEAD_BEEF, 4'b1111, .bready_delay(bd), .check_err(1'b1), .exp_err(1'b1));
    end

    // 2b. Exercise w_cg.cp_stall.zero_wait (send AW first, wait for txn_active/wready=1, then send W)
    // and aw_cg.cp_stall.short_wait / long_wait (stall AW with awready=0 for 1..4 and >=5 cycles
    // while W beat 1 is delayed)
    begin
      axi_mgr_agent                 axi_agent = get_axi_agent();
      write_request_sequencer_t     aw_sqr    = axi_agent.get_write_request_sequencer();
      write_data_sequencer_t        w_sqr     = axi_agent.get_write_data_sequencer();
      write_response_sequencer_t    b_sqr     = axi_agent.get_write_response_sequencer();
      axi_mgr_txn_request_seq       aw0, aw1_dp, aw2_dp;
      axi_mgr_write_single_data_seq w0;
      uart_beat_list_write_data_seq w_dp1, w_dp2;
      axi_mgr_write_response_seq    b0, b1_dp, b2_dp;

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
      w0.m_write_data_item.rand_mode(0);
      w0.m_write_data_item.m_data = 1024'h0;
      w0.m_write_data_item.m_strb = 128'hF;
      w0.m_write_data_item.m_last = 1'b1;
      w0.m_write_data_item.m_user = 512'h0;
      if (!w0.randomize()) `uvm_fatal(`gfn, "Failed to randomize w0_zw.")

      b0 = axi_mgr_write_response_seq::type_id::create("b0_zw");
      b0.m_use_fixed_valid_to_ready_delay = 1'b1;
      b0.m_fixed_valid_to_ready_delay = 0;

      axi_seq_lock_mgr::acquire_aw_w_issue(aw_sqr);
      aw0.start(aw_sqr);
      cfg.clk_rst_vif.wait_clks(4);
      fork
        w0.start(w_sqr);
        b0.start(b_sqr);
      join
      axi_seq_lock_mgr::release_aw_w_issue(aw_sqr);

      // Short-wait (1..4 cyc) & long-wait (>=5 cyc) AW stalls: start 2-beat AW1 (len=1) + AW2
      // (fills i_req_skd) + AW0_st (stalls on AW bus while W beat 1 of AW1 is delayed)
      begin
        int unsigned stall_delays[2] = '{0, 10};
        foreach (stall_delays[sd_i]) begin
          axi_mgr_txn_request_seq       aw1_s, aw2_s, aw0_s;
          uart_beat_list_write_data_seq w_s1, w_s2, w_s0;
          axi_mgr_write_response_seq    b1_s, b2_s, b0_s;

          aw1_s = axi_mgr_txn_request_seq::type_id::create($sformatf("aw1_st_%0d", sd_i));
          aw1_s.m_use_fixed_id = 1'b1; aw1_s.m_fixed_id = 8'h1;
          aw1_s.m_use_fixed_addr = 1'b1; aw1_s.m_fixed_addr = ral.timeout_ctrl.get_address();
          aw1_s.m_use_fixed_len = 1'b1; aw1_s.m_fixed_len = 8'd1;
          aw1_s.m_use_fixed_size = 1'b1; aw1_s.m_fixed_size = 3'd2;
          aw1_s.m_use_fixed_burst = 1'b1; aw1_s.m_fixed_burst = BurstFixed;
          aw1_s.m_use_fixed_lock = 1'b1; aw1_s.m_fixed_lock = 1'b0;
          aw1_s.m_use_fixed_user = 1'b1; aw1_s.m_fixed_user = 128'h0;

          aw2_s = axi_mgr_txn_request_seq::type_id::create($sformatf("aw2_st_%0d", sd_i));
          aw2_s.m_use_fixed_id = 1'b1; aw2_s.m_fixed_id = 8'h2;
          aw2_s.m_use_fixed_addr = 1'b1; aw2_s.m_fixed_addr = ral.timeout_ctrl.get_address();
          aw2_s.m_use_fixed_len = 1'b1; aw2_s.m_fixed_len = 8'd0;
          aw2_s.m_use_fixed_size = 1'b1; aw2_s.m_fixed_size = 3'd2;
          aw2_s.m_use_fixed_burst = 1'b1; aw2_s.m_fixed_burst = BurstFixed;
          aw2_s.m_use_fixed_lock = 1'b1; aw2_s.m_fixed_lock = 1'b0;
          aw2_s.m_use_fixed_user = 1'b1; aw2_s.m_fixed_user = 128'h0;

          aw0_s = axi_mgr_txn_request_seq::type_id::create($sformatf("aw0_st_%0d", sd_i));
          aw0_s.m_use_fixed_id = 1'b1; aw0_s.m_fixed_id = 8'h0;
          aw0_s.m_use_fixed_addr = 1'b1; aw0_s.m_fixed_addr = ral.timeout_ctrl.get_address();
          aw0_s.m_use_fixed_len = 1'b1; aw0_s.m_fixed_len = 8'd0;
          aw0_s.m_use_fixed_size = 1'b1; aw0_s.m_fixed_size = 3'd2;
          aw0_s.m_use_fixed_burst = 1'b1; aw0_s.m_fixed_burst = BurstIncr;
          aw0_s.m_use_fixed_lock = 1'b1; aw0_s.m_fixed_lock = 1'b0;
          aw0_s.m_use_fixed_user = 1'b1; aw0_s.m_fixed_user = 128'h0;

          w_s1 = uart_beat_list_write_data_seq::type_id::create($sformatf("w_st1_%0d", sd_i));
          w_s1.m_clk_rst_vif = cfg.clk_rst_vif;
          w_s1.add_beat(32'h0, 4'hF, 1'b0, 1'b0, 0);
          w_s1.add_beat(32'h0, 4'hF, 1'b1, 1'b0, stall_delays[sd_i]);

          w_s2 = uart_beat_list_write_data_seq::type_id::create($sformatf("w_st2_%0d", sd_i));
          w_s2.add_beat(32'h0, 4'hF, 1'b1);

          w_s0 = uart_beat_list_write_data_seq::type_id::create($sformatf("w_st0_%0d", sd_i));
          w_s0.add_beat(32'h0, 4'hF, 1'b1);

          b1_s = axi_mgr_write_response_seq::type_id::create($sformatf("b1_st_%0d", sd_i));
          b1_s.m_use_fixed_valid_to_ready_delay = 1'b1; b1_s.m_fixed_valid_to_ready_delay = 0;
          b2_s = axi_mgr_write_response_seq::type_id::create($sformatf("b2_st_%0d", sd_i));
          b2_s.m_use_fixed_valid_to_ready_delay = 1'b1; b2_s.m_fixed_valid_to_ready_delay = 0;
          b0_s = axi_mgr_write_response_seq::type_id::create($sformatf("b0_st_%0d", sd_i));
          b0_s.m_use_fixed_valid_to_ready_delay = 1'b1; b0_s.m_fixed_valid_to_ready_delay = 0;

          axi_seq_lock_mgr::acquire_aw_w_issue(aw_sqr);
          fork
            begin
              aw1_s.start(aw_sqr);
              aw2_s.start(aw_sqr);
              aw0_s.start(aw_sqr);
            end
            begin
              w_s1.start(w_sqr);
              w_s2.start(w_sqr);
              w_s0.start(w_sqr);
            end
            begin
              b1_s.start(b_sqr);
              b2_s.start(b_sqr);
              b0_s.start(b_sqr);
            end
          join
          axi_seq_lock_mgr::release_aw_w_issue(aw_sqr);
        end
      end

      // Zero-delay back-to-back W beats during concurrent multi-beat read to exercise i_axi_sub_wr.i_dp_skd r_valid and r_data[36:0]
      aw1_dp = axi_mgr_txn_request_seq::type_id::create("aw1_dp");
      aw1_dp.m_use_fixed_id = 1'b1; aw1_dp.m_fixed_id = 8'h1;
      aw1_dp.m_use_fixed_addr = 1'b1; aw1_dp.m_fixed_addr = ral.timeout_ctrl.get_address();
      aw1_dp.m_use_fixed_len = 1'b1; aw1_dp.m_fixed_len = 8'd1;
      aw1_dp.m_use_fixed_size = 1'b1; aw1_dp.m_fixed_size = 3'd2;
      aw1_dp.m_use_fixed_burst = 1'b1; aw1_dp.m_fixed_burst = BurstFixed;
      aw1_dp.m_use_fixed_lock = 1'b1; aw1_dp.m_fixed_lock = 1'b0;
      aw1_dp.m_use_fixed_user = 1'b1; aw1_dp.m_fixed_user = 128'h0;

      aw2_dp = axi_mgr_txn_request_seq::type_id::create("aw2_dp");
      aw2_dp.m_use_fixed_id = 1'b1; aw2_dp.m_fixed_id = 8'h2;
      aw2_dp.m_use_fixed_addr = 1'b1; aw2_dp.m_fixed_addr = ral.timeout_ctrl.get_address();
      aw2_dp.m_use_fixed_len = 1'b1; aw2_dp.m_fixed_len = 8'd0;
      aw2_dp.m_use_fixed_size = 1'b1; aw2_dp.m_fixed_size = 3'd2;
      aw2_dp.m_use_fixed_burst = 1'b1; aw2_dp.m_fixed_burst = BurstFixed;
      aw2_dp.m_use_fixed_lock = 1'b1; aw2_dp.m_fixed_lock = 1'b0;
      aw2_dp.m_use_fixed_user = 1'b1; aw2_dp.m_fixed_user = 128'h0;

      w_dp1 = uart_beat_list_write_data_seq::type_id::create("w_dp1");
      w_dp1.add_beat(32'hFFFF_FFFF, 4'hF, 1'b0);
      w_dp1.add_beat(32'hFFFF_FFFF, 4'hF, 1'b1);

      w_dp2 = uart_beat_list_write_data_seq::type_id::create("w_dp2");
      w_dp2.add_beat(32'h0000_0000, 4'h0, 1'b1);

      b1_dp = axi_mgr_write_response_seq::type_id::create("b1_dp");
      b1_dp.m_use_fixed_valid_to_ready_delay = 1'b1; b1_dp.m_fixed_valid_to_ready_delay = 0;
      b2_dp = axi_mgr_write_response_seq::type_id::create("b2_dp");
      b2_dp.m_use_fixed_valid_to_ready_delay = 1'b1; b2_dp.m_fixed_valid_to_ready_delay = 0;

      axi_seq_lock_mgr::acquire_aw_w_issue(aw_sqr);
      fork
        send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd7));
        begin
          aw1_dp.start(aw_sqr);
          aw2_dp.start(aw_sqr);
        end
        begin
          w_dp1.start(w_sqr);
          w_dp2.start(w_sqr);
        end
        begin
          b1_dp.start(b_sqr);
          b2_dp.start(b_sqr);
        end
      join
      axi_seq_lock_mgr::release_aw_w_issue(aw_sqr);

      // Continuous 4-beat zero-wait INCR write burst (no competing read) to stream consecutive
      // W beats across i_axi_sub_wr.i_dp_skd on d_valid/!hld release cycles (skidbuffer.v:143).
      send_axi_write_custom(ral.ovrd.get_address(), 32'h0, 4'hF,
                            .size(3'd2), .burst(BurstIncr), .bready_delay(0),
                            .len(8'd3), .id(8'h3));
    end

    // 3. Exercise intr_hw_tx_empty and intr_hw_tx_watermark with event_intr_i == 0 and intr_test_q == 1
    // Fill all 32 entries of TX FIFO (TxFifoDepth = 32) across two passes while TX is disabled,
    // enabling system loopback at max NCO after each 32-byte pass so all 64 entries of RX FIFO fill
    // (toggling txlvl[5:0] 0->32->0 and rxlvl[6:0] 0->64->0 without overflowing TX FIFO).
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK)); // watermark = 1 byte
    for (int pass = 0; pass < 2; pass++) begin
      csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
      for (int i = 0; i < TxFifoDepth; i++) begin
        csr_wr(.ptr(ral.wdata), .value(8'h30 + (pass * TxFifoDepth) + i), .predict(1'b0), .check(UVM_NO_CHECK));
      end
      if (pass == 0) begin
        csr_wr(.ptr(ral.intr_test), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
      end
      // Enable tx=1, rx=1, slpbk=1, nco=16'hFFFF to loop all 32 TX FIFO bytes into RX FIFO
      csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK));
      cfg.clk_rst_vif.wait_clks(6000);
    end
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK)); // rxrst | txrst
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
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
      uvm_reg_data_t intr_val;
      csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0002 | (blvl << 8)), .predict(1'b0), .check(UVM_NO_CHECK));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks(400 * (1 << blvl));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(64);
      csr_rd(.ptr(ral.intr_state), .value(intr_val), .check(UVM_NO_CHECK));
      if (!cfg.under_reset) `DV_CHECK_EQ(intr_val[RxBreakErr], 1'b1, $sformatf("Expected RxBreakErr for rxblvl=%0d", blvl))
      csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    if (do_apply_reset && !cfg.under_reset && cfg.clk_rst_vif.rst_n) begin
      uvm_reg_adapter adapter = ral.default_map.get_adapter();
      if (adapter != null) begin
        uvm_reg_data_t dummy_rdata;
        uart_reg_access_err_vseq parent_seq = uart_reg_access_err_vseq::type_id::create("parent_seq");
        adapter.parent_sequence = parent_seq;
        csr_wr(.ptr(ral.timeout_ctrl), .value('0), .predict(1'b0), .check(UVM_NO_CHECK));
        csr_rd(.ptr(ral.status), .value(dummy_rdata), .check(UVM_NO_CHECK));
        adapter.parent_sequence = null;
      end
    end
  endtask

  // Task 13: TileLink command and data integrity errors via sec_cm_vif
  virtual task exercise_tl_intg_errors();
    bit [31:0] ro_addrs[4];
    bit [31:0] rw_addrs[8];
    int unsigned prev_intg_cnt;
    uvm_reg_data_t read_val;
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
    cfg.clk_rst_vif.wait_clks(2);
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1,
                   "DUT must assert intg_err_o on u_prim_reg_we_check spurious idle write-enable fault")
    end
    apply_reset("HARD");
    ral.reset("HARD");
    cfg.clk_rst_vif.wait_clks(4);
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset before Test 1 cmd_intg sweep")

    // 1. Sweep all 127 non-zero command integrity ECC masks across complementary valid mapped writes
    // (0x0000_0000 INTR_STATE w/ strb 4'b0011, 0xFFFF_FFEC TIMEOUT_CTRL w/ strb 4'b1111, and
    // 0xFFFF_FFDC FIFO_CTRL w/ strb 4'b0001) so addrmiss == 0 and wr_err == 0 on every access while
    // toggling all bits of a_address[31:2], a_opcode, and a_mask.
    for (int m = 1; m < 128; m++) begin
      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(7'(m));
        send_axi_write_raw(32'h0000_0000, 32'h0, 4'b0011, .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert on cmd_intg mask 0x%02x (0x0000_0000)", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, $sformatf("intg_err_cnt must increment on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_addrmiss_or_wr_err, 1'b0, "Mapped INTR_STATE write must not co-trigger addrmiss/wr_err")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Register write-enables must be suppressed on cmd_intg fault")
      end

      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(7'(m));
        send_axi_write_raw(32'hFFFF_FFEC, 32'h0, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert on cmd_intg mask 0x%02x (0xFFFF_FFEC)", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, $sformatf("intg_err_cnt must increment on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_addrmiss_or_wr_err, 1'b0, "Mapped TIMEOUT_CTRL write must not co-trigger addrmiss/wr_err")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Register write-enables must be suppressed on cmd_intg fault")
      end

      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(7'(m));
        send_axi_write_raw(32'hFFFF_FFDC, 32'h0, 4'b0001, .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert on cmd_intg mask 0x%02x (0xFFFF_FFDC)", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, $sformatf("intg_err_cnt must increment on cmd_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_addrmiss_or_wr_err, 1'b0, "Mapped FIFO_CTRL write must not co-trigger addrmiss/wr_err")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Register write-enables must be suppressed on cmd_intg fault")
      end

      // Reset across initial single-bit (m=1,2) and multi-bit (m=3) masks so 0->1 sticky err_q
      // latching is also directly verified from a clean reset state on multi-bit syndromes.
      if (m <= 3) begin
        apply_reset("HARD");
        ral.reset("HARD");
        cfg.clk_rst_vif.wait_clks(4);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset during cmd_intg sweep")
      end
    end

    // Reset between Test 1 and Test 2 so sticky intg_err_o clears to 0 before testing data_intg faults
    apply_reset("HARD");
    ral.reset("HARD");
    cfg.clk_rst_vif.wait_clks(4);
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset before Test 2 data_intg sweep")

    // 2. Sweep all 127 non-zero data integrity ECC masks across all-0 and all-1 write data
    for (int m = 1; m < 128; m++) begin
      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_data_intg_flip(7'(m));
        send_axi_write_raw(ral.ctrl.get_address(), 32'h0000_0000, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on data_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert on data_intg mask 0x%02x (0x0)", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, $sformatf("intg_err_cnt must increment on data_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_addrmiss_or_wr_err, 1'b0, "Mapped CTRL write must not co-trigger addrmiss/wr_err")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Register write-enables must be suppressed on data_intg fault")
      end

      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_data_intg_flip(7'(m));
        send_axi_write_raw(ral.ctrl.get_address(), 32'hFFFF_FFFF, 4'b1111, .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, $sformatf("DUT must assert intg_err_o on data_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, $sformatf("u_chk.err_o must assert on data_intg mask 0x%02x (0xFFFF_FFFF)", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, $sformatf("intg_err_cnt must increment on data_intg mask 0x%02x", m))
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_addrmiss_or_wr_err, 1'b0, "Mapped CTRL write must not co-trigger addrmiss/wr_err")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "Register write-enables must be suppressed on data_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.get_ctrl_tx(), 1'b0, "ral.ctrl.tx must remain 0 after blocked 0xFFFF_FFFF data_intg fault")
      end

      if (m <= 3) begin
        csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
        `DV_CHECK_EQ(read_val, 32'h0000_0000, "ral.ctrl must remain 0x0 after blocked 0xFFFF_FFFF data_intg fault")
        apply_reset("HARD");
        ral.reset("HARD");
        cfg.clk_rst_vif.wait_clks(4);
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset during data_intg sweep")
      end
    end

    if (!cfg.under_reset) begin
      csr_rd(.ptr(ral.ctrl), .value(read_val), .check(UVM_NO_CHECK));
      `DV_CHECK_EQ(read_val, 32'h0000_0000, "ral.ctrl must remain 0x0 across full 127-mask data_intg sweep")
    end

    // Reset between Test 2 and Test 3 so sticky intg_err_o clears to 0 before testing RO read cmd_intg faults
    apply_reset("HARD");
    ral.reset("HARD");
    cfg.clk_rst_vif.wait_clks(4);
    `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset before Test 3 RO read cmd_intg sweep")

    // 3. Flip command integrity during reads to RO registers (status, rdata, fifo_status, val)
    ro_addrs = '{
      ral.status.get_address(),
      ral.rdata.get_address(),
      ral.fifo_status.get_address(),
      ral.val.get_address()
    };
    foreach (ro_addrs[i]) begin
      prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
      fork
        cfg.sec_cm_vif.inject_cmd_intg_flip(7'h01);
        send_axi_read_raw(ro_addrs[i], .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
      join
      cfg.clk_rst_vif.wait_clks(2);
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, "DUT must assert intg_err_o on RO read cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, "u_chk.err_o must assert on RO read cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, "intg_err_cnt must increment on RO read cmd_intg fault")
        `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "RO read side-effect enables must be suppressed on cmd_intg fault")
      end
      apply_reset("HARD");
      ral.reset("HARD");
      cfg.clk_rst_vif.wait_clks(4);
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b0, "intg_err_o must clear after reset between RO read cmd_intg faults")
    end
    prev_intg_cnt = cfg.sec_cm_vif.intg_err_cnt;
    fork
      cfg.sec_cm_vif.inject_cmd_intg_flip(7'h15);
      send_axi_read_raw(ro_addrs[0], .mask(4'b1111), .check_err(1'b1), .exp_err(1'b1));
    join
    cfg.clk_rst_vif.wait_clks(2);
    if (!cfg.under_reset) begin
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_error, 1'b1, "DUT must assert intg_err_o on multi-bit cmd_intg fault")
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_intg_err, 1'b1, "u_chk.err_o must assert on multi-bit RO read cmd_intg fault")
      `DV_CHECK_EQ(cfg.sec_cm_vif.intg_err_cnt, prev_intg_cnt + 1, "intg_err_cnt must increment on multi-bit cmd_intg fault")
      `DV_CHECK_EQ(cfg.sec_cm_vif.last_reg_side_effect, 1'b0, "RO read side-effect enables must be suppressed on multi-bit cmd_intg fault")
    end

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
