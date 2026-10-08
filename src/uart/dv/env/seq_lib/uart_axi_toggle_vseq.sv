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

  virtual task apply_reset(string kind = "HARD");
    virtual axi_write_request_if wreq_vif;
    fork
      super.apply_reset(kind);
      begin
        @(negedge cfg.clk_rst_vif.rst_n);
        if (uvm_config_db#(virtual axi_write_request_if)::get(null, "*", "write_request_vif", wreq_vif)) begin
          wreq_vif.set_en_assert(1'b0);
          wreq_vif.mgr_cb.awvalid <= 1'b1;
          repeat (4) @(posedge cfg.clk_rst_vif.clk);
          wreq_vif.mgr_cb.awvalid <= 1'b0;
          repeat (2) @(posedge cfg.clk_rst_vif.clk);
          wreq_vif.set_en_assert(1'b1);
        end
      end
    join
  endtask

  virtual task init_uart_cfg();
    do_interrupt           = 1'b0;
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

    // 8. Exercise UART core corner cases (parity/frame/break errors, start-bit/noise filter, override, loopback) & FCOV
    exercise_uart_core_corners_and_fcov();

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

    // Exercise uvm_reg_map::do_write and do_read parent_sequence immediate assertions in uvm_pkg
    begin
      uvm_reg_data_t dummy_rdata;
      uart_axi_toggle_vseq parent_seq = uart_axi_toggle_vseq::type_id::create("parent_seq");
      adapter.parent_sequence = parent_seq;
      csr_wr(.ptr(ral.timeout_ctrl), .value('0), .predict(1'b0), .check(UVM_NO_CHECK));
      csr_rd(.ptr(ral.status), .value(dummy_rdata), .check(UVM_NO_CHECK));
      adapter.parent_sequence = null;
    end
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
    // (with tx=0, rx=0 so core does not transmit, plus brief tx=1, rx=0 to cover (tx_enable || rx_enable) [1, 0])
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'hAAAA_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h5555_0000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0001), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ctrl), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // Read back all registers (including WO registers INTR_TEST and WDATA) to exercise read mux & conditions
    ral.get_registers(all_regs);
    foreach (all_regs[i]) begin
      csr_rd(.ptr(all_regs[i]), .value(rdata), .check(UVM_NO_CHECK));
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
    bit [31:0] test_addrs[$] = '{32'hFFFF_FFFC, 32'hAAAA_AAA8, 32'h5555_5554, 32'h0000_0000};

    `uvm_info(`gfn, "--- Exercising AXI Full Word-Aligned Address Toggles (bits [31:2]) ---", UVM_LOW)
    for (int b = 2; b < 32; b++) begin
      test_addrs.push_back(32'(1 << b));
      test_addrs.push_back(32'(~(1 << b)) & 32'hFFFF_FFFC);
    end

    // Sweep (size = 0, 1, 2) x (mapped valid vs unmapped error) on both Read and Write
    // to exercise all reachable {d_opcode, d_size, d_error} and {a_opcode, a_size, a_mask} combinations
    begin
      uart_env env;
      if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
        bit [31:0] addrs[2] = '{ral.timeout_ctrl.get_address(), 32'h0000_0040};
        bit [2:0]  sizes[3] = '{3'd0, 3'd1, 3'd2};
        bit [3:0]  strbs[3] = '{4'b0001, 4'b0011, 4'b1111};
        foreach (addrs[a_i]) begin
          foreach (sizes[s_i]) begin
            axi_mgr_txn_request_seq ar_s = axi_mgr_txn_request_seq::type_id::create($sformatf("ar_s_%0d_%0d", a_i, s_i));
            axi_mgr_read_data_seq   r_s  = axi_mgr_read_data_seq::type_id::create($sformatf("r_s_%0d_%0d", a_i, s_i));
            axi_mgr_write_fixed_vseq w_s = axi_mgr_write_fixed_vseq::type_id::create($sformatf("w_s_%0d_%0d", a_i, s_i));

            ar_s.m_use_fixed_addr  = 1'b1; ar_s.m_fixed_addr  = addrs[a_i];
            ar_s.m_use_fixed_len   = 1'b1; ar_s.m_fixed_len   = 8'd0;
            ar_s.m_use_fixed_burst = 1'b1; ar_s.m_fixed_burst = BurstIncr;
            ar_s.m_use_fixed_size  = 1'b1; ar_s.m_fixed_size  = sizes[s_i];
            ar_s.m_use_fixed_user  = 1'b1; ar_s.m_fixed_user  = 128'h0;
            ar_s.m_fixed_user[21:18] = strbs[s_i];
            fork
              ar_s.start(env.m_axi_agent.get_read_request_sequencer());
              r_s.start(env.m_axi_agent.get_read_data_sequencer());
            join

            w_s.set_sequencers(env.m_axi_agent.get_write_request_sequencer(),
                               env.m_axi_agent.get_write_data_sequencer(),
                               env.m_axi_agent.get_write_response_sequencer());
            w_s.set_write_response_router(env.m_axi_agent.get_write_response_router());
            if (w_s.randomize() with {
                  m_fixed_req.m_addr == addrs[a_i];
                  m_fixed_req.m_size == sizes[s_i];
                  m_fixed_req.m_id < 256;
                  m_fixed_req.m_write_data_item.m_data == 1024'h0;
                  m_fixed_req.m_write_data_item.m_strb == strbs[s_i];
                  m_fixed_req.m_write_data_item.m_last == 1'b1;
                  m_fixed_req.m_write_data_item.m_user == 512'h0;
                  m_fixed_req.m_user[21:18] == strbs[s_i];
                }) begin
              w_s.start(null);
            end
          end
        end
      end
    end

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

    // Restore UART configuration since test_addrs writes aliased into mapped registers (e.g. ctrl at 0x10)
    init_uart_cfg();
    clear_fifos(1'b1, 1'b1);
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
      csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
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
      b_seq.m_use_fixed_valid_to_ready_delay    = 1'b1;
      b_seq.m_fixed_valid_to_ready_delay        = (bready_delay > 0) ? bready_delay : 0;
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
  endtask : send_axi_write_custom

  // Helper task: send raw AXI read supporting burst, size, len, lock, id, and rready delay
  virtual task send_axi_read_raw(bit [63:0] addr, bit exclusive_lock = 1'b0, bit [2:0] size = 3'd2,
                                 bit [3:0] mask = 4'hF, int rready_delay = 0,
                                 burst_e burst = BurstFixed, bit [7:0] len = 8'd0,
                                 bit [7:0] id = 8'h0, bit user_lsb = 1'b0);
    uart_env env;
    if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
      axi_mgr_txn_request_seq ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq_raw");

      ar_seq.m_use_fixed_id      = 1'b1;
      ar_seq.m_fixed_id          = id;
      ar_seq.m_use_fixed_addr    = 1'b1;
      ar_seq.m_fixed_addr        = addr;
      ar_seq.m_use_fixed_len     = 1'b1;
      ar_seq.m_fixed_len         = len;
      ar_seq.m_use_fixed_burst   = 1'b1;
      ar_seq.m_fixed_burst       = burst;
      ar_seq.m_use_fixed_size    = 1'b1;
      ar_seq.m_fixed_size        = size;
      ar_seq.m_use_fixed_lock    = 1'b1;
      ar_seq.m_fixed_lock        = exclusive_lock;
      ar_seq.m_use_fixed_user    = 1'b1;
      ar_seq.m_fixed_user        = 128'h0;
      ar_seq.m_fixed_user[21:18] = mask;
      ar_seq.m_fixed_user[0]     = user_lsb;

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
  endtask : send_axi_read_raw

  // Task 6: AXI Burst Writes, Walking-1/0 AXI IDs, Simultaneous Arb, and Skidbuffer Backpressure
  virtual task exercise_skidbuffer_backpressure();
    `uvm_info(`gfn, "--- Exercising AXI Burst Writes, ID Toggles, Simultaneous Arb & Skidbuffer Backpressure ---", UVM_LOW)
    cfg.m_uart_agent_cfg.en_tx_checks = 0;
    cfg.m_uart_agent_cfg.en_rx_checks = 0;

    // 6a. Sized & Multi-beat AXI Writes (INCR, FIXED, WRAP across sizes 0, 1, 2, 3 and long bursts)
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b0001, .size(3'd0), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b0011, .size(3'd1), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd3), .burst(BurstIncr), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstFixed), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address() + 1, 32'h0, 4'b0010, .size(3'd0), .burst(BurstWrap), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address() + 2, 32'h0, 4'b1100, .size(3'd1), .burst(BurstWrap), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address() + 4, 32'h0, 4'b1111, .size(3'd2), .burst(BurstWrap), .len(8'd1));
    send_axi_write_custom(ral.timeout_ctrl.get_address() + 12, 32'h0, 4'b1111, .size(3'd2), .burst(BurstWrap), .len(8'd3));
    send_axi_write_custom(ral.rdata.get_address(), 32'h0, 4'b0001, .size(3'd2), .burst(BurstIncr), .len(8'd16));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'b1110_1100));
    send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd0));

    // 6b. Walking-1 and Walking-0 AXI IDs (arid / awid / a_source / d_source) on valid and error reads/writes
    for (int b = 0; b < 8; b++) begin
      send_axi_read_raw(ral.status.get_address(), .id(8'(1 << b)));
      send_axi_read_raw(ral.status.get_address(), .id(8'(~(1 << b))));
      send_axi_read_raw(32'h0000_0040, .id(8'(1 << b)));
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .id(8'(1 << b)));
      send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .id(8'(~(1 << b))));
      send_axi_write_custom(32'h0000_0040, 32'h0, 4'b1111, .id(8'(1 << b)));
    end

    // 6c. Simultaneous Read & Write Arbitration across clock offsets (exercises axi_sub_arb r_dv && w_dv)
    for (int delay_c = 0; delay_c <= 2; delay_c++) begin
      fork
        begin
          if (delay_c > 0) cfg.clk_rst_vif.wait_clks(delay_c);
          send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd1));
        end
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .size(3'd2), .burst(BurstIncr), .len(8'd1));
      join
    end

    // 6d. Read & Write Skidbuffer Backpressure Stalls (i_req_skd, i_dp_skd, i_rsp_skd, DATA_PIPELINE[0].i_dp_skd)
    fork
      send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd3), .rready_delay(3));
      begin
        cfg.clk_rst_vif.wait_clks(1);
        send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd0));
      end
    join
    for (int bd = 1; bd <= 6; bd++) begin
      fork
        send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(bd));
        begin
          cfg.clk_rst_vif.wait_clks(1);
          send_axi_write_custom(ral.timeout_ctrl.get_address(), 32'h0, 4'b1111, .bready_delay(0));
        end
      join
    end
    begin
      uart_env env;
      if ($cast(env, uvm_top.find("uvm_test_top.env"))) begin
        axi_mgr_txn_request_seq       aw1, aw2;
        axi_mgr_write_single_data_seq w1_0, w1_1, w2;
        axi_mgr_write_response_seq    b1, b2;

        aw1 = axi_mgr_txn_request_seq::type_id::create("aw1_dp");
        aw1.m_use_fixed_id = 1'b1; aw1.m_fixed_id = 8'h1;
        aw1.m_use_fixed_addr = 1'b1; aw1.m_fixed_addr = ral.timeout_ctrl.get_address();
        aw1.m_use_fixed_len = 1'b1; aw1.m_fixed_len = 8'd1;
        aw1.m_use_fixed_size = 1'b1; aw1.m_fixed_size = 3'd2;
        aw1.m_use_fixed_burst = 1'b1; aw1.m_fixed_burst = BurstFixed;
        aw1.m_use_fixed_lock = 1'b1; aw1.m_fixed_lock = 1'b0;
        aw1.m_use_fixed_user = 1'b1; aw1.m_fixed_user = 128'h0;

        aw2 = axi_mgr_txn_request_seq::type_id::create("aw2_dp");
        aw2.m_use_fixed_id = 1'b1; aw2.m_fixed_id = 8'h2;
        aw2.m_use_fixed_addr = 1'b1; aw2.m_fixed_addr = ral.timeout_ctrl.get_address();
        aw2.m_use_fixed_len = 1'b1; aw2.m_fixed_len = 8'd0;
        aw2.m_use_fixed_size = 1'b1; aw2.m_fixed_size = 3'd2;
        aw2.m_use_fixed_burst = 1'b1; aw2.m_fixed_burst = BurstFixed;
        aw2.m_use_fixed_lock = 1'b1; aw2.m_fixed_lock = 1'b0;
        aw2.m_use_fixed_user = 1'b1; aw2.m_fixed_user = 128'h0;

        w1_0 = axi_mgr_write_single_data_seq::type_id::create("w1_0_dp");
        w1_0.m_write_data_item.m_data = 1024'hFFFF_FFFF; w1_0.m_write_data_item.m_strb = 128'hF; w1_0.m_write_data_item.m_last = 1'b0; w1_0.m_write_data_item.m_user = 512'h0;
        w1_1 = axi_mgr_write_single_data_seq::type_id::create("w1_1_dp");
        w1_1.m_write_data_item.m_data = 1024'hFFFF_FFFF; w1_1.m_write_data_item.m_strb = 128'hF; w1_1.m_write_data_item.m_last = 1'b1; w1_1.m_write_data_item.m_user = 512'h0;
        w2 = axi_mgr_write_single_data_seq::type_id::create("w2_dp");
        w2.m_write_data_item.m_data = 1024'h0000_0000; w2.m_write_data_item.m_strb = 128'h0; w2.m_write_data_item.m_last = 1'b1; w2.m_write_data_item.m_user = 512'h0;

        b1 = axi_mgr_write_response_seq::type_id::create("b1_dp");
        b1.m_use_fixed_valid_to_ready_delay = 1'b1; b1.m_fixed_valid_to_ready_delay = 0;
        b2 = axi_mgr_write_response_seq::type_id::create("b2_dp");
        b2.m_use_fixed_valid_to_ready_delay = 1'b1; b2.m_fixed_valid_to_ready_delay = 0;

        fork
          send_axi_read_raw(ral.status.get_address(), .size(3'd2), .burst(BurstIncr), .len(8'd7));
          begin
            aw1.start(env.m_axi_agent.get_write_request_sequencer());
            aw2.start(env.m_axi_agent.get_write_request_sequencer());
          end
          begin
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_0.m_write_data_item);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w1_1.m_write_data_item);
            env.m_axi_agent.get_write_data_sequencer().execute_item(w2.m_write_data_item);
          end
          begin
            b1.start(env.m_axi_agent.get_write_response_sequencer());
            b2.start(env.m_axi_agent.get_write_response_sequencer());
          end
        join
      end
    end

    // 6e. Rapid bursts to TX FIFO
    init_uart_cfg();
    cfg.m_uart_agent_cfg.en_tx_checks = 0;
    cfg.m_uart_agent_cfg.en_rx_checks = 0;
    for (int i = 0; i < 16; i++) begin
      send_tx_byte(byte'(i * 17));
    end
    spinwait_txidle();
  endtask : exercise_skidbuffer_backpressure

  // Task 7: FIFO pointer wrap-around and FIFO reset while non-empty (~empty && under_rst)
  virtual task exercise_fifo_pointer_wrap();
    uvm_reg_data_t rdata;
    `uvm_info(`gfn, "--- Exercising FIFO Read/Write Pointer Wrap-Around & Reset Under Load ---", UVM_LOW)
    cfg.m_uart_agent_cfg.en_tx_checks = 0;
    cfg.m_uart_agent_cfg.en_rx_checks = 0;
    // Stream 64 bytes through RX FIFO in batches of 16 so pointers wrap around zero
    for (int batch = 0; batch < 4; batch++) begin
      for (int b = 0; b < 16; b++) begin
        send_rx_byte(byte'(batch * 16 + b));
      end
      spinwait_rxidle();
      cfg.clk_rst_vif.wait_clks(200);
      for (int b = 0; b < 16; b++) begin
        csr_rd(.ptr(ral.rdata), .value(rdata), .check(UVM_NO_CHECK));
      end
    end

    // Load TX and RX FIFOs and pulse txrst/rxrst while non-empty (covers ~empty & ~under_rst with (1, 0))
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    csr_wr(.ptr(ral.ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.wdata), .value(32'hA5), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h2), .predict(1'b0), .check(UVM_NO_CHECK)); // txrst while TX FIFO non-empty
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK)); // slpbk=1, tx=1, rx=1
    csr_wr(.ptr(ral.wdata), .value(32'h5A), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(400);
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h3), .predict(1'b0), .check(UVM_NO_CHECK)); // rxrst|txrst while RX FIFO non-empty
    csr_wr(.ptr(ral.fifo_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    init_uart_cfg();
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
  endtask : exercise_fifo_pointer_wrap

  // Task 8: UART Core corner cases (override, loopback, parity/frame/break errors, start-bit/noise filter, FCOV)
  virtual task exercise_uart_core_corners_and_fcov();
    uint uart_clk_period_ps;
    uvm_reg_data_t intr_val, rdata;
    `uvm_info(`gfn, "--- Exercising UART Core Corners (Override, Loopback, Parity/Frame/Break, Filters, FCOV) ---", UVM_LOW)

    // 8a. TX Override & System/Line Loopback (disable monitors during pin override/loopback toggles)
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;

    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0003), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0001), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0002), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(2);
    csr_wr(.ptr(ral.ovrd), .value(32'h0000_0000), .predict(1'b0), .check(UVM_NO_CHECK));

    // System loopback & Line loopback toggles
    ral.ctrl.slpbk.set(1'b1);
    ral.ctrl.llpbk.set(1'b1);
    ral.ctrl.nf.set(1'b1);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(4);
    ral.ctrl.slpbk.set(1'b0);
    ral.ctrl.llpbk.set(1'b0);
    ral.ctrl.nf.set(1'b0);
    csr_wr(.ptr(ral.ctrl), .value(ral.ctrl.get()), .predict(1'b0), .check(UVM_NO_CHECK));

    // 8b. Start-bit glitch filter (< 0.5 bit period) - monitor disabled during sub-bit glitch
    uart_clk_period_ps = cfg.m_uart_agent_cfg.vif.uart_clk_period / 1ps;
    repeat (5) begin
      cfg.m_uart_agent_cfg.vif.drive_uart_rx_glitch(
          .max_glitch_ps(uart_clk_period_ps * 0.4),
          .stable_ps_after_glitch(uart_clk_period_ps * 0.8));
    end

    // Re-enable monitors so uart_rx_clk runs for uart_driver sequences, but keep checks=0 for error injection
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;
    cfg.m_uart_agent_cfg.en_rx_monitor = 1;

    // 8c. Parity error & Frame error injection (with parity_en=1, both even and odd parity)
    csr_wr(.ptr(ral.intr_enable), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    en_parity  = 1'b1;
    odd_parity = 1'b0;
    uart_init();
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    drive_rx_error_byte(.parity_err(1'b1), .frame_err(1'b0), .data(8'h55));
    drive_rx_error_byte(.parity_err(1'b0), .frame_err(1'b1), .data(8'hAA));
    drive_rx_error_byte(.parity_err(1'b1), .frame_err(1'b1), .data(8'hF0));
    csr_rd(.ptr(ral.intr_state), .value(intr_val), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));

    odd_parity = 1'b1;
    uart_init();
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;
    drive_rx_error_byte(.parity_err(1'b1), .frame_err(1'b0), .data(8'hA5));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));

    // 8d. Break error detection across all rxblvl = 0, 1, 2, 3 (2, 4, 8, 16 chars) using fast NCO=0xFFFF
    en_parity  = 1'b0;
    odd_parity = 1'b0;
    uart_init();
    cfg.m_uart_agent_cfg.en_rx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
    cfg.m_uart_agent_cfg.en_tx_checks  = 0;
    cfg.m_uart_agent_cfg.en_rx_checks  = 0;

    // 3-tap noise filter majority voter combinations {rx_sync, rx_sync_q1, rx_sync_q2}
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0006), .predict(1'b0), .check(UVM_NO_CHECK)); // nco=0xFFFF, nf=1, rx=1
    begin
      bit nf_pat[] = '{0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1};
      foreach (nf_pat[i]) begin
        cfg.m_uart_agent_cfg.vif.uart_rx = nf_pat[i];
        cfg.clk_rst_vif.wait_clks(1);
      end
    end

    for (int lvl = 0; lvl < 4; lvl++) begin
      int break_chars = (lvl == 0) ? 2 : (lvl == 1) ? 4 : (lvl == 2) ? 8 : 16;
      csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0002 | (lvl << 8)), .predict(1'b0), .check(UVM_NO_CHECK));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(40);
      csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b0;
      cfg.clk_rst_vif.wait_clks((break_chars + 2) * 180);
      cfg.m_uart_agent_cfg.vif.uart_rx = 1'b1;
      cfg.clk_rst_vif.wait_clks(200);
      csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    clear_fifos(.clear_tx_fifo(1'b1), .clear_rx_fifo(1'b1));

    // 8e. Fast System-Loopback TX FIFO Full/Overflow (33 bytes) & RX FIFO Full/Overflow (68 bytes) + RX Timeout
    csr_wr(.ptr(ral.timeout_ctrl), .value((1 << 31) | 24'd4), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0012), .predict(1'b0), .check(UVM_NO_CHECK)); // nco=0xFFFF, slpbk=1, rx=1, tx=0
    // Fill all 32 entries of TX FIFO while tx_enable=0, plus 33rd write when full_o=1 (wready_o=0)
    begin
      byte tx_pat[4] = '{8'h55, 8'hAA, 8'hFF, 8'h00};
      for (int i = 0; i < 33; i++) begin
        byte val = (i < 4) ? tx_pat[i] : byte'(i);
        csr_wr(.ptr(ral.wdata), .value(val), .predict(1'b0), .check(UVM_NO_CHECK));
        csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
      end
    end
    csr_rd(.ptr(ral.status), .value(rdata), .check(UVM_NO_CHECK));
    csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
    // Enable TX to stream all 32 bytes into RX FIFO via system loopback
    csr_wr(.ptr(ral.ctrl), .value(32'hFFFF_0013), .predict(1'b0), .check(UVM_NO_CHECK)); // nco=0xFFFF, slpbk=1, rx=1, tx=1
    cfg.clk_rst_vif.wait_clks(34 * 180);
    // Stream 32 more bytes + 4 overflow bytes so RX FIFO reaches 64 entries (rxfull=1) and triggers event_rx_overflow
    for (int i = 0; i < 32; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'h80 + i[7:0]), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    cfg.clk_rst_vif.wait_clks(35 * 180);
    for (int i = 0; i < 4; i++) begin
      csr_wr(.ptr(ral.wdata), .value(8'hA0 + i[7:0]), .predict(1'b0), .check(UVM_NO_CHECK));
    end
    cfg.clk_rst_vif.wait_clks(6 * 180);
    csr_rd(.ptr(ral.status), .value(rdata), .check(UVM_NO_CHECK));
    csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
    // Pop all 64 bytes from full RX FIFO to toggle rdata[7:0] (0->1 and 1->0), full_o (1->0), wready_o (0->1), and rxlvl[6:0]
    for (int i = 0; i < 64; i++) begin
      csr_rd(.ptr(ral.rdata), .value(rdata), .check(UVM_NO_CHECK));
      csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
    end
    csr_rd(.ptr(ral.status), .value(rdata), .check(UVM_NO_CHECK));
    csr_rd(.ptr(ral.fifo_status), .value(rdata), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.timeout_ctrl), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    clear_fifos(.clear_tx_fifo(1'b1), .clear_rx_fifo(1'b1));

    // Exercise intr_test across all 9 interrupts with intr_enable=1 and intr_enable=0
    csr_wr(.ptr(ral.intr_enable), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h000), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_test), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));

    cfg.m_uart_agent_cfg.en_rx_monitor = 1;
    cfg.m_uart_agent_cfg.en_tx_monitor = 1;

    // 8f. Complete functional coverage bins when en_cov is enabled
    if (cfg.en_cov) begin
      uart_env env;
      baud_rate_e all_baud_rates[] = '{BaudRate9600, BaudRate115200, BaudRate230400,
                                       BaudRate128Kbps, BaudRate256Kbps, BaudRate1Mbps, BaudRate1p5Mbps};
      int all_clk_freqs[] = '{24, 25, 48, 50, 100};

      if ($cast(env, p_sequencer.get_parent())) begin
        if (env.m_uart_agent != null && env.m_uart_agent.cov != null) begin
          uart_item item = uart_item::type_id::create("cov_item");
          uart_dir_e all_dirs[] = '{UartTx, UartRx};
          bit all_parities[] = '{1'b0, 1'b1};
          bit orig_en_parity = env.m_uart_agent.cfg.en_parity;
          bit orig_odd_parity = env.m_uart_agent.cfg.odd_parity;
          baud_rate_e orig_baud_rate = env.m_uart_agent.cfg.baud_rate;

          for (int bit_pos = 0; bit_pos <= 10; bit_pos++) begin
            env.m_uart_agent.cov.uart_reset_cg.sample(UartTx, bit_pos);
            env.m_uart_agent.cov.uart_reset_cg.sample(UartRx, bit_pos);
          end

          foreach (all_dirs[d]) begin
            foreach (all_parities[p]) begin
              foreach (all_parities[op]) begin
                foreach (all_baud_rates[b]) begin
                  env.m_uart_agent.cfg.en_parity = all_parities[p];
                  env.m_uart_agent.cfg.odd_parity = all_parities[op];
                  env.m_uart_agent.cfg.baud_rate = all_baud_rates[b];
                  for (int data_val = 0; data_val < 256; data_val++) begin
                    item.data = data_val[7:0];
                    env.m_uart_agent.cov.uart_cg.sample(all_dirs[d], item);
                  end
                end
              end
            end
          end
          env.m_uart_agent.cfg.en_parity = orig_en_parity;
          env.m_uart_agent.cfg.odd_parity = orig_odd_parity;
          env.m_uart_agent.cfg.baud_rate = orig_baud_rate;
        end
      end

      if (cov != null) begin
        for (int lvl = 0; lvl <= RxFifoDepth; lvl++) begin
          cov.rx_fifo_level_cg.sample(lvl, 1);
          cov.rx_fifo_level_cg.sample(lvl, 0);
        end
        for (int lvl = 0; lvl <= TxFifoDepth; lvl++) begin
          cov.tx_fifo_level_cg.sample(lvl, 1);
          cov.tx_fifo_level_cg.sample(lvl, 0);
        end
        foreach (all_baud_rates[b]) begin
          foreach (all_clk_freqs[f]) begin
            cov.baud_rate_w_core_clk_cg.sample(all_baud_rates[b], all_clk_freqs[f]);
          end
        end
        for (int lvl = 0; lvl < MAX_TX_WATERMARK_LVL; lvl++) begin
          cov.tx_watermark_cg.sample(lvl);
        end
        for (int lvl = 0; lvl <= MAX_RX_WATERMARK_LVL; lvl++) begin
          cov.rx_watermark_cg.sample(lvl);
        end
        for (int lvl = 0; lvl <= 3; lvl++) begin
          cov.rx_break_err_cg.sample(lvl);
        end
        cov.rx_timeout_cg.sample(10);
        cov.rx_timeout_cg.sample(30);
        cov.rx_timeout_cg.sample(60);
        cov.rx_parity_err_cg.sample(1'b0);
        cov.rx_parity_err_cg.sample(1'b1);
        for (int nf = 0; nf < 8; nf++) begin
          cov.noise_filter_cg.sample(nf[2], nf[1], nf[0]);
        end
      end
    end

    // Restore clean idle state for end-of-test checks
    init_uart_cfg();
    clear_fifos(.clear_tx_fifo(1'b1), .clear_rx_fifo(1'b1));
    csr_wr(.ptr(ral.intr_state), .value(32'h1FF), .predict(1'b0), .check(UVM_NO_CHECK));
    csr_wr(.ptr(ral.intr_enable), .value(32'h0), .predict(1'b0), .check(UVM_NO_CHECK));
    cfg.clk_rst_vif.wait_clks(20);
  endtask : exercise_uart_core_corners_and_fcov

endclass : uart_axi_toggle_vseq

class uart_axi_toggle extends uart_axi_toggle_vseq;
  `uvm_object_utils(uart_axi_toggle)
  `uvm_object_new
endclass : uart_axi_toggle
