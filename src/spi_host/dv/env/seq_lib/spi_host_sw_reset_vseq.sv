// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies software reset (CONTROL.SW_RST) mid-transaction overlap, pin-level reset state
// (CSB='1, SCK=CPOL, SD_EN='0), empty-RXDATA underflow semantics, retention of non-reset CSRs,
// deliberate pin-violation control, FSM state-to-Idle transitions, and post-reset recovery
// (Comment #10).
class spi_host_sw_reset_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_sw_reset_vseq)
  `uvm_object_new

  constraint sw_rst_csid_c {
    spi_host_ctrl_reg.csid == 0;
    spi_config_regs.clkdiv inside {[0 : 63]};
  }

  function void pre_randomize();
    super.pre_randomize();
    cfg.seq_cfg.host_spi_min_trans = 1;
    cfg.seq_cfg.host_spi_max_trans = 2;
    cfg.seq_cfg.host_spi_min_runs  = 2;
    cfg.seq_cfg.host_spi_max_runs  = 5;
    cfg.seq_cfg.host_spi_min_len   = 4;
    cfg.seq_cfg.host_spi_max_len   = 4;
  endfunction

  virtual task pre_start();
    super.pre_start();
  endtask

  virtual function void check_sw_rst_pin_invariants(bit exp_cpol, string ctx);
    if (cfg.m_spi_agent_cfg.vif.csb !== {SPI_HOST_NUM_CS{1'b1}} ||
        cfg.spi_passthrough_vif.cio_sck_o !== exp_cpol ||
        cfg.spi_passthrough_vif.cio_sd_en_o !== 4'h0) begin
      `uvm_error(`gfn, $sformatf(
        "SW_RST pin invariant violated [%s]: csb=0b%b (exp all-1), sclk=%0b (exp cpol=%0b), sd_en=0x%0h (exp 0)",
        ctx, cfg.m_spi_agent_cfg.vif.csb, cfg.spi_passthrough_vif.cio_sck_o, exp_cpol,
        cfg.spi_passthrough_vif.cio_sd_en_o))
    end
  endfunction

  // Deterministic mid-transfer SW_RST check proving active overlap, pin return to reset state
  // across both CPOL=0 and CPOL=1, empty RXDATA read semantics, retention of unrelated CSRs,
  // and a deliberate pin-violation negative control (Comment #10).
  virtual task run_checked_mid_transfer_sw_rst_and_fault_control();
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         rdata;
    uvm_reg_data_t     ctrl_val;

    `uvm_info(`gfn, "Running deterministic mid-transfer SW_RST pin/CSR/RXDATA checks & fault control", UVM_LOW)
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);

    for (int cpol_i = 0; cpol_i <= 1; cpol_i++) begin
      int          target_cs   = (cpol_i % SPI_HOST_NUM_CS);
      bit [31:0]   exp_cfg0    = {bit'(cpol_i == 0 ? 1'b0 : 1'b1), 3'b000, 4'd2, 4'd3, 4'd4, 16'd10};
      bit [31:0]   exp_cfg1    = {bit'(cpol_i == 1 ? 1'b1 : 1'b0), 3'b010, 4'd3, 4'd2, 4'd5, 16'd10};
      bit          exp_cpol    = (target_cs == 1) ? exp_cfg1[31] : exp_cfg0[31];
      bit [31:0]   exp_ctrl_base = 32'hA000_152A; // spien=1, output_en=1, tx_wm=0x15, rx_wm=0x2A
      bit [31:0]   exp_err_en  = 32'h0000_0015;
      bit [31:0]   exp_evt_en  = 32'h0000_002A;
      bit [31:0]   exp_intr_en = 32'h0000_0003;

      spi_host_init();
      csr_wr(.ptr(ral.error_status), .value(32'h3F));
      csr_wr(.ptr(ral.intr_state),   .value(32'h03));
      csr_wr(.ptr(ral.configopts),   .value(exp_cfg0));
      csr_wr(.ptr(ral.configopts_1), .value(exp_cfg1));
      csr_wr(.ptr(ral.csid),         .value(target_cs));
      csr_wr(.ptr(ral.error_enable), .value(exp_err_en));
      csr_wr(.ptr(ral.event_enable), .value(exp_evt_en));
      csr_wr(.ptr(ral.intr_enable),  .value(exp_intr_en));
      csr_wr(.ptr(ral.control),      .value(exp_ctrl_base));

      // Pre-populate 1 RX word first, then launch a 16-byte Bidir transfer on target_cs so both
      // active serial shifting AND non-empty RX/TX FIFOs overlap SW_RST
      write_txdata(32'hCAFE_0001, 4'hf, status);
      cmd.direction = Bidir;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

      for (int w = 0; w < 4; w++) begin
        ral.txdata.write(status, 0, 32'hA5A5_5A50 + w);
      end
      cmd.direction = Bidir;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd15; // 16 bytes -> >2500 core clocks at clkdiv=10
      program_command_reg(cmd);

      // Deterministically wait for active mid-byte shifting on target_cs
      wait (cfg.m_spi_agent_cfg.vif.csb[target_cs] === 1'b0);
      repeat (4) @(cfg.m_spi_agent_cfg.vif.sck);
      `DV_CHECK_EQ(cfg.m_spi_agent_cfg.vif.csb[target_cs], 1'b0,
                   "Expected target CSB active low immediately prior to mid-transfer SW_RST")
      `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0001,
                   "Expected SD_EN[0]=1 during active Standard transfer prior to SW_RST")

      // Assert CONTROL.SW_RST = 1 while holding all non-reset CONTROL fields intact
      csr_wr(.ptr(ral.control), .value(exp_ctrl_base | 32'h4000_0000));
      cfg.clk_rst_vif.wait_clks(2);

      // Verify pin-reset invariants while SW_RST == 1
      for (int cyc = 0; cyc < 8; cyc++) begin
        @(posedge cfg.clk_rst_vif.clk);
        check_sw_rst_pin_invariants(exp_cpol, $sformatf("cpol=%0d cyc=%0d", exp_cpol, cyc));
      end

      wait_for_fifos_empty(AllFifos);
      csr_rd_check(.ptr(ral.status.active),  .compare_value(1'b0));
      csr_rd_check(.ptr(ral.status.cmdqd),   .compare_value(4'h0));
      csr_rd_check(.ptr(ral.status.txqd),    .compare_value(8'h0));
      csr_rd_check(.ptr(ral.status.rxqd),    .compare_value(8'h0));
      csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));
      csr_rd_check(.ptr(ral.status.rxempty), .compare_value(1'b1));

      // Release CONTROL.SW_RST = 0 and verify non-reset CSRs retained their pre-SW_RST values
      csr_wr(.ptr(ral.control), .value(exp_ctrl_base));
      csr_rd_check(.ptr(ral.configopts),   .compare_value(exp_cfg0));
      csr_rd_check(.ptr(ral.configopts_1), .compare_value(exp_cfg1));
      csr_rd_check(.ptr(ral.csid),         .compare_value(target_cs));
      csr_rd_check(.ptr(ral.control),      .compare_value(exp_ctrl_base));
      csr_rd_check(.ptr(ral.error_enable), .compare_value(exp_err_en));
      csr_rd_check(.ptr(ral.event_enable), .compare_value(exp_evt_en));
      csr_rd_check(.ptr(ral.intr_enable),  .compare_value(exp_intr_en));

      // Verify flushed RXDATA returns 0x0 and sets ERROR_STATUS.UNDERFLOW
      ral.rxdata.read(status, 0, rdata);
      `DV_CHECK_EQ(rdata, 32'h0, "Post-SW_RST empty RXDATA read must return 0x0")
      check_error(ral.error_status.underflow, 1);
      csr_wr(.ptr(ral.error_status.underflow), .value(1'b1));
      csr_wr(.ptr(ral.intr_state),             .value(32'h03));
    end

    // Deliberate SW_RST pin-violation negative control (proves check_sw_rst_pin_invariants fails on glitch)
    begin
      spi_host_scb_neg_catcher rst_pin_catcher = spi_host_scb_neg_catcher::type_id::create("rst_pin_catcher");
      rst_pin_catcher.match_pattern = "*SW_RST pin invariant violated*";
      uvm_report_cb::add(null, rst_pin_catcher);

      ctrl_val = 32'hE000_007F; // spien=1, sw_rst=1, output_en=1
      csr_wr(.ptr(ral.csid),       .value(32'h0));
      csr_wr(.ptr(ral.configopts), .value(32'h8111_0002)); // DUT drives cio_sck_o=1'b1 (CPOL=1)
      csr_wr(.ptr(ral.control),    .value(ctrl_val));
      cfg.clk_rst_vif.wait_clks(2);

      check_sw_rst_pin_invariants(1'b0, "injected_sck_fault");
      csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));
      csr_wr(.ptr(ral.control),    .value(32'hA000_007F));

      uvm_report_cb::delete(null, rst_pin_catcher);
      `DV_CHECK_EQ(rst_pin_catcher.caught_err_cnt, 1,
                   "Expected SW_RST pin-invariant negative control to catch injected violation")
    end

    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
  endtask

  // Passively wait for the target FSM state (and bit_cntr_q == 0 for InternalClkHigh)
  // and issue real AXI bus writes to CONTROL.SW_RST (1 -> drain & pin check -> 0) without any RTL forcing.
  virtual task trigger_bus_sw_rst_in_state(input logic [2:0] target_state,
                                           input bit require_last_bit = 1'b0);
    bit hit_state = 1'b0;
    bit exp_cpol  = bit'(ral.configopts.cpol.get_mirrored_value());
    uvm_reg_data_t ctrl_val;
    fork
      begin : iso_wait_state
        fork
          begin
            @(posedge cfg.force_spi_fsm_vif.fsm_clk iff
              (cfg.force_spi_fsm_vif.fsm_state == target_state &&
               (!require_last_bit || cfg.force_spi_fsm_vif.fsm_bit_cntr == 3'b0)));
            hit_state = 1'b1;
          end
          begin
            cfg.clk_rst_vif.wait_clks(50000);
          end
        join_any
        disable fork;
      end : iso_wait_state
    join
    `DV_CHECK_EQ(hit_state, 1'b1,
                 $sformatf("Timed out waiting passively for FSM state %0d", target_state))

    // Assert CONTROL.SW_RST = 1 via real frontdoor AXI CSR write, verify pin & FIFO reset, then release
    csr_utils_pkg::wait_no_outstanding_access();
    ctrl_val = ral.control.get_mirrored_value();
    ctrl_val[30] = 1'b1;
    csr_wr(.ptr(ral.control), .value(ctrl_val));
    cfg.clk_rst_vif.wait_clks(2);
    check_sw_rst_pin_invariants(exp_cpol, $sformatf("fsm_state_%0d", target_state));
    wait_for_fifos_empty(AllFifos);
    csr_rd_check(.ptr(ral.status.cmdqd), .compare_value(4'h0));
    ctrl_val[30] = 1'b0;
    csr_wr(.ptr(ral.control), .value(ctrl_val));
  endtask : trigger_bus_sw_rst_in_state

  virtual task body();
    int edges_until_sw_rst;

    // 1. Deterministic mid-transfer SW_RST pin/CSR/RXDATA invariants & fault control (Comment #10)
    run_checked_mid_transfer_sw_rst_and_fault_control();

    // 2. Randomized mid-transaction SW_RST runs
    for (int i = 0; i < num_runs; i++) begin : for_num_runs
      `uvm_info(`gfn, $sformatf("Starting run %0d/%0d now!", i, num_runs), UVM_LOW)
      fork begin : isolation_fork
        stop_rx_fifo_read = 0;
        fork start_agent_reactive_seqs(); join_none

        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          fork
            begin
              read_rx_fifo();
            end
            begin
              csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1));
            end
            begin
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(edges_until_sw_rst,
                edges_until_sw_rst inside {[40 : 120]};)
              while (edges_until_sw_rst > 0) begin
                cfg.m_spi_agent_cfg.wait_sck_edge(DrivingEdge, spi_host_ctrl_reg.csid[CSB_WIDTH-1:0]);
                edges_until_sw_rst--;
              end
            end
          join_any;
        end

        stop_rx_fifo_read = 1;
        csr_utils_pkg::wait_no_outstanding_access();
        disable fork;
      end : isolation_fork join

      csr_utils_pkg::wait_no_outstanding_access();
      spi_host_atomic = new(1);
      `uvm_info(`gfn, "Triggering CONTROL.SW_RST now!", UVM_LOW)
      spi_host_init();
      csr_wr(.ptr(ral.error_status), .value(32'h3F));

      cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      csr_rd_check(.ptr(ral.status.rxempty), .compare_value(1'b1));
      csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));
    end : for_num_runs

    // 3. Targeted FSM state-to-Idle SW_RST transitions & checked Bidir recovery
    target_fsm_transitions();
  endtask : body

  virtual task target_fsm_transitions();
    spi_segment_item seg;

    // 1. WaitLead -> Idle (state 1 -> 0) via passive observation + bus CONTROL.SW_RST
    `uvm_info(`gfn, "Targeting WaitLead -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.csnlead.set(4'd15);
    ral.configopts.clkdiv.set(16'd20);
    csr_update(ral.configopts);
    seg = spi_segment_item::type_id::create("seg_lead");
    seg.command_reg.direction = TxOnly;
    seg.command_reg.mode = Standard;
    seg.command_reg.csaat = 1'b0;
    seg.command_reg.len = 9'd3;
    for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'hA5);
    access_data_fifo(seg.spi_data, TxFifo);
    fork
      trigger_bus_sw_rst_in_state(3'h1);
      program_command_reg(seg.command_reg);
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));

    // 2. CSBSwitch -> Idle (state 6 -> 0) via passive observation + bus CONTROL.SW_RST
    `uvm_info(`gfn, "Targeting CSBSwitch -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.cpol.set(!ral.configopts.cpol.get_mirrored_value());
    ral.configopts.csnidle.set(4'd15);
    ral.configopts.clkdiv.set(16'd20);
    csr_update(ral.configopts);
    seg = spi_segment_item::type_id::create("seg_switch");
    seg.command_reg.direction = TxOnly;
    seg.command_reg.mode = Standard;
    seg.command_reg.csaat = 1'b0;
    seg.command_reg.len = 9'd3;
    for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'h5A);
    access_data_fifo(seg.spi_data, TxFifo);
    fork
      trigger_bus_sw_rst_in_state(3'h6);
      program_command_reg(seg.command_reg);
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));

    // 3. WaitTrail -> Idle (state 4 -> 0) via passive observation + bus CONTROL.SW_RST
    `uvm_info(`gfn, "Targeting WaitTrail -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.cpol.set(1'b0);
    ral.configopts.cpha.set(1'b0);
    ral.configopts.csnlead.set(4'd1);
    ral.configopts.csntrail.set(4'd15);
    ral.configopts.csnidle.set(4'd1);
    ral.configopts.clkdiv.set(16'd20);
    csr_update(ral.configopts);
    seg = spi_segment_item::type_id::create("seg_trail");
    seg.command_reg.direction = TxOnly;
    seg.command_reg.mode = Quad;
    seg.command_reg.csaat = 1'b0;
    seg.command_reg.len = 9'd0;
    seg.spi_data.push_back(8'h3C);
    access_data_fifo(seg.spi_data, TxFifo);
    fork
      trigger_bus_sw_rst_in_state(3'h4);
      program_command_reg(seg.command_reg);
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));

    // 4. WaitIdle -> Idle (state 5 -> 0) via passive observation + bus CONTROL.SW_RST
    `uvm_info(`gfn, "Targeting WaitIdle -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.csnlead.set(4'd1);
    ral.configopts.csntrail.set(4'd1);
    ral.configopts.csnidle.set(4'd15);
    ral.configopts.clkdiv.set(16'd20);
    csr_update(ral.configopts);
    seg = spi_segment_item::type_id::create("seg_idle");
    seg.command_reg.direction = TxOnly;
    seg.command_reg.mode = Quad;
    seg.command_reg.csaat = 1'b0;
    seg.command_reg.len = 9'd0;
    seg.spi_data.push_back(8'hF0);
    access_data_fifo(seg.spi_data, TxFifo);
    fork
      trigger_bus_sw_rst_in_state(3'h5);
      program_command_reg(seg.command_reg);
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));

    // 5. InternalClkHigh -> Idle (state 3 -> 0) via passive observation + bus CONTROL.SW_RST
    `uvm_info(`gfn, "Targeting InternalClkHigh -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.csnlead.set(4'd1);
    ral.configopts.csntrail.set(4'd1);
    ral.configopts.csnidle.set(4'd1);
    ral.configopts.clkdiv.set(16'd30);
    csr_update(ral.configopts);
    seg = spi_segment_item::type_id::create("seg_clkhigh");
    seg.command_reg.direction = TxOnly;
    seg.command_reg.mode = Standard;
    seg.command_reg.csaat = 1'b0;
    seg.command_reg.len = 9'd3;
    for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'h55);
    access_data_fifo(seg.spi_data, TxFifo);
    fork
      trigger_bus_sw_rst_in_state(3'h3, 1'b1);
      program_command_reg(seg.command_reg);
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));

    // 6. InternalClkLow -> WaitTrail (with CPHA=1) completed cleanly and checked by scoreboard
    `uvm_info(`gfn, "Targeting InternalClkLow -> WaitTrail with CPHA=1", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.cpol.set(1'b0);
    ral.configopts.cpha.set(1'b1);
    ral.configopts.csnlead.set(4'd1);
    ral.configopts.csntrail.set(4'd1);
    ral.configopts.csnidle.set(4'd1);
    ral.configopts.clkdiv.set(16'd2);
    csr_update(ral.configopts);
    begin
      seg = spi_segment_item::type_id::create("seg_cpha1");
      seg.command_reg.direction = TxOnly;
      seg.command_reg.mode = Standard;
      seg.command_reg.csaat = 1'b0;
      seg.command_reg.len = 9'd0;
      seg.spi_data.push_back(8'hAA);
      access_data_fifo(seg.spi_data, TxFifo);
      program_command_reg(seg.command_reg);
      @(posedge cfg.m_spi_agent_cfg.vif.csb[0]);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    end

    // 7. Post-SW_RST end-to-end recovery check: scoreboard-checked Bidir (TX + RX) transfer
    spi_host_init();
    csr_wr(.ptr(ral.error_status), .value(32'h3F));
    program_spi_host_regs();
    begin
      uvm_status_e status;
      uvm_reg_data_t rdata;
      spi_host_command_t cmd;
      int unsigned prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      int unsigned prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
      write_txdata(32'h1357_9BDF, 4'hf, status);
      wait_ready_for_command();
      cmd.direction = Bidir;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd3;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(status, 0, rdata);
      cfg.clk_rst_vif.wait_clks(10);
      if (cfg.en_scb) begin
        `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                     "Expected scoreboard TX check on post-SW_RST recovery transfer")
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     "Expected scoreboard RX check on post-SW_RST recovery transfer")
      end
    end
  endtask : target_fsm_transitions
endclass : spi_host_sw_reset_vseq
