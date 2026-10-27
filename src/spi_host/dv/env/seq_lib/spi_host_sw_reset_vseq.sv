// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger a software reset (CONTROL.SW_RST) randomly during an ongoing transaction

// - Check rx and tx queues are empty post SW_RST application
// From Documentation (hw/ip/spi_host/data/spi_host.hjson):
// >  In the current implementation, the CDC FIFOs are drained (not reset).
// >  Therefore, software must confirm that both FIFO's are empty before releasing the IP from reset
//
class spi_host_sw_reset_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_sw_reset_vseq)
  `uvm_object_new

  constraint sw_rst_csid_c {
    spi_host_ctrl_reg.csid == 0;
  }

  function void pre_randomize();
    super.pre_randomize();
    cfg.seq_cfg.host_spi_min_trans = 1;
    cfg.seq_cfg.host_spi_max_trans = 2;
    cfg.seq_cfg.host_spi_min_runs = 2;
    cfg.seq_cfg.host_spi_max_runs = 5;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
  endfunction

  virtual task pre_start();
    super.pre_start();
  endtask

  // Passively wait for the target FSM state (and bit_cntr_q == 0 for InternalClkHigh)
  // and issue real AXI bus writes to CONTROL.SW_RST (1 -> drain -> 0) without any RTL forcing.
  virtual task trigger_bus_sw_rst_in_state(input logic [2:0] target_state,
                                           input bit require_last_bit = 1'b0);
    bit hit_state = 1'b0;
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

    // Assert CONTROL.SW_RST = 1 via real frontdoor AXI CSR write, verify FIFOs drain, then release
    ctrl_val = ral.control.get_mirrored_value();
    ctrl_val[30] = 1'b1;
    csr_wr(.ptr(ral.control), .value(ctrl_val));
    wait_for_fifos_empty(AllFifos);
    csr_rd_check(.ptr(ral.status.cmdqd), .compare_value(4'h0));
    ctrl_val[30] = 1'b0;
    csr_wr(.ptr(ral.control), .value(ctrl_val));
  endtask : trigger_bus_sw_rst_in_state

  virtual task body();
    int edges_until_sw_rst;
    for (int i = 0; i < num_runs; i++) begin : for_num_runs
      `uvm_info(`gfn, $sformatf("Starting run %0d/%0d now!", i, num_runs), UVM_LOW)
      fork begin : isolation_fork
        fork start_agent_reactive_seqs(); join_none

        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          fork
            begin
              // Read data out of RXFIFO once the DUT becomes active
              read_rx_fifo(); // Returns when status.active == 0 + rxdata is cleared out.
            end

            // Happy-path : Start transaction(s), wait for DUT to become idle again.
            begin
              csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1));
            end

            // Sad-path : Wait for a random-number of SCK-edges into the transaction
            begin
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(edges_until_sw_rst,
                edges_until_sw_rst inside { [40 : 120] };)
              while (edges_until_sw_rst > 0) begin
                cfg.m_spi_agent_cfg.wait_sck_edge(DrivingEdge, spi_host_ctrl_reg.csid[CSB_WIDTH-1:0]);
                edges_until_sw_rst--;
              end
            end
          join_any;
        end

        // Wait for no outstanding accesses before using 'disable fork' to kill the path
        // which did not join.
        csr_utils_pkg::wait_no_outstanding_access();
        disable fork;
      end : isolation_fork join

      csr_utils_pkg::wait_no_outstanding_access();
      spi_host_atomic = new(1);
      `uvm_info(`gfn, "Triggering CONTROL.SW_RST now!", UVM_LOW)
      spi_host_init();
      csr_wr(.ptr(ral.error_status), .value(32'h3F));

      cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      // Confirm that both FIFO's are empty before releasing the IP from reset.
      csr_rd_check(.ptr(ral.status.rxempty), .compare_value(1'b1));
      csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));

    end : for_num_runs

    target_fsm_transitions();
  endtask : body

  virtual task target_fsm_transitions();
    spi_segment_item seg;

    // 1. WaitLead -> Idle (state 1 -> 0) via passive observation + bus CONTROL.SW_RST
    // csnlead=15, clkdiv=20 => WaitLead persists for 16 * 21 = 336 core clocks
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
    // csnidle=15, clkdiv=20 with changed cpol => CSBSwitch persists for 336 core clocks
    `uvm_info(`gfn, "Targeting CSBSwitch -> Idle transition via bus CONTROL.SW_RST", UVM_LOW)
    program_control_reg();
    program_csid_reg();
    wait_ready_for_command();
    ral.configopts.cpol.set(~ral.configopts.cpol.get_mirrored_value());
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
    // 1-byte Quad transfer finishes shifting quickly, then WaitTrail persists for 16 * 21 = 336 clocks
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
    // csnidle=15, clkdiv=20 => WaitIdle persists for 16 * 21 = 336 core clocks
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
    // clkdiv=30 => each InternalClkHigh half-period (including bit_cntr_q == 0) persists 31 core clocks
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
