// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scenario: uart_axi_toggle (uart_axi_toggle_vseq)
// Comprehensive sequence exercising AXI subordinate and UART core scenarios cleanly:
// 1. AXI sub-word and wide accesses: 8-bit, 16-bit, 32-bit, 64-bit, and 128-bit reads/writes.
// 2. AXI bus toggle coverage: walking 1s, walking 0s, 0xAA, 0x55 on addr, data, strobes.
// 3. AXI address aperture toggles: bits [31:6] toggle on reads and writes.
// 4. AXI burst reads: INCR, WRAP, len=1, len=255 to exercise last, r_last, i_burst[1], i_len[7:0].
// 5. sub2tlul FSM transitions: interleaved back-to-back reads (get_txn) and writes (put_txn).
// 6. Skidbuffer backpressure and rapid bursts to TX FIFO.
// 7. FIFO read/write pointer wrap-around: stream 64+ bytes through RX and TX FIFOs.

class uart_axi_toggle_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_axi_toggle_vseq)

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
    `uvm_info(`gfn, "Starting uart_axi_toggle_vseq", UVM_LOW)

    init_uart_cfg();

    // 1. Exercise sub-word and wide accesses (8-bit, 16-bit, 32-bit, 64-bit, 128-bit)
    exercise_subword_accesses();

    // 2. Exercise AXI toggle coverage on addresses, data, and registers
    exercise_axi_toggles();

    // 3. Exercise AXI upper address toggles (bits [31:6])
    exercise_axi_addr_toggles();

    // 4. Exercise AXI burst reads (INCR, WRAP, len=1, len=255, last toggles)
    exercise_axi_burst_reads();

    // 5. Exercise sub2tlul FSM transitions (valid_get_txn <-> valid_put_txn)
    exercise_sub2tlul_fsm_transitions();

    // 6. Exercise skidbuffer backpressure and rapid burst writes
    exercise_skidbuffer_backpressure();

    // 7. Exercise FIFO read/write pointer wrap-around
    exercise_fifo_pointer_wrap();

    `uvm_info(`gfn, "Completed uart_axi_toggle_vseq successfully!", UVM_LOW)
  endtask : body

  // Task 1: Sub-word and wide accesses
  virtual task exercise_subword_accesses();
    uvm_reg_bus_op rw;
    uvm_sequencer_base sqr = ral.default_map.get_sequencer();
    uvm_reg_adapter adapter = ral.default_map.get_adapter();
    uvm_sequence_item item, rsp_item;

    `uvm_info(`gfn, "--- Exercising AXI Sub-word Accesses (8-bit, 16-bit, 32-bit, 64-bit, 128-bit) ---", UVM_LOW)

    // 8-bit byte reads across all 4 byte lanes
    for (int lane = 0; lane < 4; lane++) begin
      rw.kind = UVM_READ;
      rw.addr = ral.status.get_address() + lane;
      rw.n_bits = 8;
      rw.byte_en = (4'b0001 << lane);
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
    end

    // 16-bit halfword reads (lower and upper)
    for (int hw = 0; hw < 2; hw++) begin
      rw.kind = UVM_READ;
      rw.addr = ral.ctrl.get_address() + (hw * 2);
      rw.n_bits = 16;
      rw.byte_en = (4'b0011 << (hw * 2));
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
    end

    // 32-bit word read (axsize = 2, size[2] = 0)
    rw.kind = UVM_READ;
    rw.addr = ral.ctrl.get_address();
    rw.n_bits = 32;
    rw.byte_en = 4'b1111;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);

    // 64-bit read (axsize = 3)
    rw.kind = UVM_READ;
    rw.addr = ral.ctrl.get_address();
    rw.n_bits = 64;
    rw.byte_en = 4'b1111;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);

    // 128-bit read (axsize = 4, size[2] = 1) -> exercises size[2] toggle
    rw.kind = UVM_READ;
    rw.addr = ral.ctrl.get_address();
    rw.n_bits = 128;
    rw.byte_en = 4'b1111;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);

    // 8-bit byte writes across all 4 byte lanes (exercises AXI wstrb toggles)
    for (int lane = 0; lane < 4; lane++) begin
      rw.kind = UVM_WRITE;
      rw.addr = ral.timeout_ctrl.get_address() + lane;
      rw.data = (32'hAA << (lane * 8));
      rw.n_bits = 8;
      rw.byte_en = (4'b0001 << lane);
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
    end

    // 16-bit halfword writes (lower and upper)
    for (int hw = 0; hw < 2; hw++) begin
      rw.kind = UVM_WRITE;
      rw.addr = ral.timeout_ctrl.get_address() + (hw * 2);
      rw.data = (32'h5555 << (hw * 16));
      rw.n_bits = 16;
      rw.byte_en = (4'b0011 << (hw * 2));
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
    end

    // 128-bit write (axsize = 4, size[2] = 1) -> exercises wsize[2] toggle
    rw.kind = UVM_WRITE;
    rw.addr = ral.timeout_ctrl.get_address();
    rw.data = 32'h0;
    rw.n_bits = 128;
    rw.byte_en = 4'b1111;
    item = adapter.reg2bus(rw);
    start_item(item, .sequencer(sqr));
    finish_item(item);
    get_response(rsp_item);
    adapter.bus2reg(rsp_item, rw);

    csr_wr(.ptr(ral.timeout_ctrl), .value('0), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask : exercise_subword_accesses

  // Task 2: AXI toggle coverage
  virtual task exercise_axi_toggles();
    uvm_reg all_regs[$];
    uvm_reg_data_t rdata;

    `uvm_info(`gfn, "--- Exercising AXI Toggle Coverage (Data, Addr, Strobes) ---", UVM_LOW)

    // Ensure FIFOs are clear and TX/RX are idle
    spinwait_txidle();
    clear_fifos(1'b1, 1'b1);

    // Disable monitors during raw register toggles
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;

    // Toggle timeout_ctrl bits (24-bit field + enable bit 31)
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'hFFFF_FFFF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'hAAAA_AAAA), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h5555_5555), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // Toggle fifo_ctrl watermark levels (full 3-bit sweep for tx and rx)
    for (int t = 0; t < 8; t++) begin
      for (int r = 0; r < 8; r++) begin
        csr_wr(.ptr(ral.fifo_ctrl), .value((t << 5) | (r << 2)), .predict(1'b0), .check(UVM_NO_CHECK));
      end
    end
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_00FC), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_00A8), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0054), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // Toggle intr_enable, intr_test, and intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(5);
    csr_wr(.ptr(ral.intr_state), .value(32'h0000_01FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0155), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_00AA), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // Toggle ctrl register: control fields [7:0] AND full NCO field [31:16]
    // (with tx=0, rx=0 so core does not transmit)
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'hAAAA_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h5555_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // Read back all registers to exercise read data toggle
    ral.get_registers(all_regs);
    foreach (all_regs[i]) begin
      if (all_regs[i].get_rights() != "WO") begin
        csr_rd(.ptr(all_regs[i]), .value(rdata), .check(UVM_NO_CHECK));
      end
    end

    // Re-initialize clean UART configuration and clear FIFOs
    init_uart_cfg();
    clear_fifos(1'b1, 1'b1);
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
  endtask : exercise_axi_toggles

  // Task 3: AXI upper address toggles (bits [31:6])
  virtual task exercise_axi_addr_toggles();
    uvm_reg_bus_op rw;
    uvm_sequencer_base sqr = ral.default_map.get_sequencer();
    uvm_reg_adapter adapter = ral.default_map.get_adapter();
    uvm_sequence_item item, rsp_item;
    bit [31:0] test_addrs[4] = '{32'hFFFF_FFC0, 32'hAAAA_AAA0, 32'h5555_5540, 32'h0000_0000};

    `uvm_info(`gfn, "--- Exercising AXI Upper Address Toggles (bits [31:6]) ---", UVM_LOW)

    foreach (test_addrs[i]) begin
      // Read access to unmapped address (exercises araddr[31:6])
      rw.kind = UVM_READ;
      rw.addr = test_addrs[i];
      rw.n_bits = 32;
      rw.byte_en = 4'b1111;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);

      // Write access to unmapped address (exercises awaddr[31:6])
      rw.kind = UVM_WRITE;
      rw.addr = test_addrs[i];
      rw.data = 32'h0;
      rw.n_bits = 32;
      rw.byte_en = 4'b1111;
      item = adapter.reg2bus(rw);
      start_item(item, .sequencer(sqr));
      finish_item(item);
      get_response(rsp_item);
      adapter.bus2reg(rsp_item, rw);
    end
  endtask : exercise_axi_addr_toggles

  // Task 4: AXI burst reads (INCR, WRAP, len=1, len=255, last toggles)
  virtual task exercise_axi_burst_reads();
    uart_env env;
    read_request_sequencer_t ar_sqr;
    read_data_sequencer_t    r_sqr;
    axi_mgr_txn_request_seq  ar_seq;

    `uvm_info(`gfn, "--- Exercising AXI Burst Reads (WRAP, INCR, len > 0, last toggles) ---", UVM_LOW)

    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      ar_sqr = env.m_axi_agent.get_read_request_sequencer();
      r_sqr  = env.m_axi_agent.get_read_data_sequencer();

      // Burst 1: INCR burst of len=1 (2 beats) to exercise last=0 then last=1
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_incr");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd1;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstIncr;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd2; // 4 bytes
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_003C_0000;
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          axi_mgr_read_data_seq r1 = axi_mgr_read_data_seq::type_id::create("r1");
          r0.start(r_sqr);
          r1.start(r_sqr);
        end
      join

      // Burst 2: WRAP burst of len=1 (2 beats) to exercise i_burst[1] (BurstWrap)
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_wrap");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd1;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstWrap;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd2; // 4 bytes
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_003C_0000;
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          axi_mgr_read_data_seq r1 = axi_mgr_read_data_seq::type_id::create("r1");
          r0.start(r_sqr);
          r1.start(r_sqr);
        end
      join

      // Burst 3: INCR burst of len=255 (256 beats) to exercise all bits of i_len[7:0]
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_len255");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = 32'h0000_0100;
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'hFF;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstIncr;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd2;
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_003C_0000;
      fork
        ar_seq.start(ar_sqr);
        begin
          for (int b = 0; b < 256; b++) begin
            axi_mgr_read_data_seq r = axi_mgr_read_data_seq::type_id::create($sformatf("r_len255_%0d", b));
            r.start(r_sqr);
          end
        end
      join

      // Single-beat read to restore len=0, burst=BurstFixed
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_fixed");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd0;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstFixed;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd2;
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_003C_0000;
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          r0.start(r_sqr);
        end
      join

      // Burst 8-bit: INCR burst of len=1, size=0 (1 byte per beat)
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_byte");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd1;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstIncr;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd0; // 1 byte
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_0004_0000; // bit 18 = 1'b1 (mask 4'b0001)
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          axi_mgr_read_data_seq r1 = axi_mgr_read_data_seq::type_id::create("r1");
          r0.start(r_sqr);
          r1.start(r_sqr);
        end
      join

      // Burst 16-bit: INCR burst of len=1, size=1 (2 bytes per beat)
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_hword");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd1;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstIncr;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd1; // 2 bytes
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_000C_0000; // bits [19:18] = 2'b11 (mask 4'b0011)
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          axi_mgr_read_data_seq r1 = axi_mgr_read_data_seq::type_id::create("r1");
          r0.start(r_sqr);
          r1.start(r_sqr);
        end
      join

      // 16-bit read to upper halfword (addr[1]=1, mask=4'b1100) -> covers tlul_err lines 72,74
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_hword_upper");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.timeout_ctrl.get_address() + 2;
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd0;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstFixed;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd1; // 2 bytes
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_0030_0000; // bits [21:18] = 4'b1100
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          r0.start(r_sqr);
        end
      join

      // Read with delayed rready to exercise skidbuffer backpressure
      ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_bp");
      ar_seq.m_use_fixed_addr  = 1'b1;
      ar_seq.m_fixed_addr      = ral.status.get_address();
      ar_seq.m_use_fixed_len   = 1'b1;
      ar_seq.m_fixed_len       = 8'd0;
      ar_seq.m_use_fixed_burst = 1'b1;
      ar_seq.m_fixed_burst     = BurstFixed;
      ar_seq.m_use_fixed_size  = 1'b1;
      ar_seq.m_fixed_size      = 3'd2;
      ar_seq.m_use_fixed_user  = 1'b1;
      ar_seq.m_fixed_user      = 128'h0000_0000_0000_0000_0000_0000_003C_0000;
      fork
        ar_seq.start(ar_sqr);
        begin
          axi_mgr_read_data_seq r0 = axi_mgr_read_data_seq::type_id::create("r0");
          r0.m_use_fixed_valid_to_ready_delay = 1'b1;
          r0.m_fixed_valid_to_ready_delay    = 5;
          r0.start(r_sqr);
        end
      join

      // 16-bit write to upper halfword (addr[1]=1, wstrb=4'b1100)
      begin
        axi_mgr_write_fixed_vseq write_vseq = axi_mgr_write_fixed_vseq::type_id::create("write_vseq_hw_upper");
        uvm_reg_addr_t target_addr = ral.timeout_ctrl.get_address() + 2;
        write_vseq.set_sequencers(env.m_axi_agent.get_write_request_sequencer(),
                                  env.m_axi_agent.get_write_data_sequencer(),
                                  env.m_axi_agent.get_write_response_sequencer());
        write_vseq.set_write_response_router(env.m_axi_agent.get_write_response_router());
        if (!write_vseq.randomize() with {
              m_fixed_req.m_addr == target_addr;
              m_fixed_req.m_size == 3'd1; // 2 bytes
              m_fixed_req.m_id < 256;
              m_fixed_req.m_write_data_item.m_data == 1024'h5555_0000;
              m_fixed_req.m_write_data_item.m_strb == 128'hC; // 4'b1100
              m_fixed_req.m_write_data_item.m_last == 1'b1;
              m_fixed_req.m_write_data_item.m_user == 512'h0;
              m_fixed_req.m_user[21:18] == 4'hC;
            }) begin
          `uvm_fatal(get_full_name(), "Failed to randomize write_vseq_hw_upper.")
        end
        write_vseq.start(null);
      end
    end
  endtask : exercise_axi_burst_reads

  // Task 5: sub2tlul FSM transitions between valid_get_txn and valid_put_txn
  virtual task exercise_sub2tlul_fsm_transitions();
    uvm_reg_data_t rd_val;
    `uvm_info(`gfn, "--- Exercising sub2tlul FSM Transitions ---", UVM_LOW)
    for (int i = 0; i < 20; i++) begin
      csr_rd(.ptr(ral.status), .value(rd_val), .check(UVM_NO_CHECK));
      csr_wr(.ptr(ral.timeout_ctrl), .value(i), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
  endtask : exercise_sub2tlul_fsm_transitions

  // Task 6: Rapid bursts to TX FIFO
  virtual task exercise_skidbuffer_backpressure();
    `uvm_info(`gfn, "--- Exercising Rapid Burst Writes & Skidbuffer ---", UVM_LOW)
    for (int i = 0; i < 16; i++) begin
      send_tx_byte(byte'(i * 17));
    end
    spinwait_txidle();
  endtask : exercise_skidbuffer_backpressure

  // Task 7: FIFO pointer wrap-around
  virtual task exercise_fifo_pointer_wrap();
    uvm_reg_data_t rdata;
    `uvm_info(`gfn, "--- Exercising FIFO Read/Write Pointer Wrap-Around ---", UVM_LOW)
    // Stream 64 bytes through RX FIFO in batches of 16 so pointers wrap around zero
    for (int batch = 0; batch < 4; batch++) begin
      for (int b = 0; b < 16; b++) begin
        send_rx_byte(byte'(batch * 16 + b));
      end
      for (int b = 0; b < 16; b++) begin
        csr_rd(.ptr(ral.rdata), .value(rdata), .check(UVM_NO_CHECK));
      end
    end
  endtask : exercise_fifo_pointer_wrap

endclass : uart_axi_toggle_vseq

class uart_axi_toggle extends uart_axi_toggle_vseq;
  `uvm_object_utils(uart_axi_toggle)
  `uvm_object_new
endclass : uart_axi_toggle
