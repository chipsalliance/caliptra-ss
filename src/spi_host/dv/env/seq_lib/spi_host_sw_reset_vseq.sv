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
    cfg.en_scb = 0;
    super.pre_start();
  endtask

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
                edges_until_sw_rst inside { [40 : 120] };) // TODO(#18886) Examine txn len for range
              while (edges_until_sw_rst > 0) begin
                // TODO(#18886) The below statement assumes CSB[0], future work may break this.
                cfg.m_spi_agent_cfg.wait_sck_edge(DrivingEdge, 2'b00);
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
      `uvm_info(`gfn, "Triggering CONTROL.SW_RST now!", UVM_LOW)
      spi_host_init();

      cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      // Confirm that both FIFO's are empty before releasing the IP from reset.
      csr_rd_check(.ptr(ral.status.rxempty), .compare_value(1'b1));
      csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));

    end : for_num_runs

    target_fsm_transitions();
  endtask : body

  virtual task target_fsm_transitions();
    spi_segment_item seg;

    // 1. WaitLead -> Idle (state 1 -> 0)
    `uvm_info(`gfn, "Targeting WaitLead -> Idle transition", UVM_LOW)
    spi_host_init();
    wait_ready_for_command();
    ral.configopts.csnlead.set(4'd15);
    ral.configopts.clkdiv.set(16'd10);
    csr_update(ral.configopts);
    fork
      cfg.force_spi_fsm_vif.force_sw_rst_in_state(3'h1);
      begin
        seg = spi_segment_item::type_id::create("seg_lead");
        seg.command_reg.direction = TxOnly;
        seg.command_reg.mode = Standard;
        seg.command_reg.csaat = 1'b0;
        seg.command_reg.len = 9'd3;
        for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'hA5);
        access_data_fifo(seg.spi_data, TxFifo);
        program_command_reg(seg.command_reg);
      end
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();

    // 2. CSBSwitch -> Idle (state 6 -> 0)
    `uvm_info(`gfn, "Targeting CSBSwitch -> Idle transition", UVM_LOW)
    wait_ready_for_command();
    ral.configopts.cpol.set(~ral.configopts.cpol.get_mirrored_value());
    ral.configopts.csnidle.set(4'd15);
    ral.configopts.clkdiv.set(16'd10);
    csr_update(ral.configopts);
    fork
      cfg.force_spi_fsm_vif.force_sw_rst_in_state(3'h6);
      begin
        seg = spi_segment_item::type_id::create("seg_switch");
        seg.command_reg.direction = TxOnly;
        seg.command_reg.mode = Standard;
        seg.command_reg.csaat = 1'b0;
        seg.command_reg.len = 9'd3;
        for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'h5A);
        access_data_fifo(seg.spi_data, TxFifo);
        program_command_reg(seg.command_reg);
      end
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();

    // 3. WaitTrail -> Idle (state 4 -> 0)
    `uvm_info(`gfn, "Targeting WaitTrail -> Idle transition", UVM_LOW)
    wait_ready_for_command();
    ral.configopts.csntrail.set(4'd15);
    ral.configopts.clkdiv.set(16'd2);
    csr_update(ral.configopts);
    fork
      cfg.force_spi_fsm_vif.force_sw_rst_in_state(3'h4);
      begin
        seg = spi_segment_item::type_id::create("seg_trail");
        seg.command_reg.direction = TxOnly;
        seg.command_reg.mode = Standard;
        seg.command_reg.csaat = 1'b0;
        seg.command_reg.len = 9'd3;
        for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'h3C);
        access_data_fifo(seg.spi_data, TxFifo);
        program_command_reg(seg.command_reg);
      end
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();

    // 4. WaitIdle -> Idle (state 5 -> 0)
    `uvm_info(`gfn, "Targeting WaitIdle -> Idle transition", UVM_LOW)
    wait_ready_for_command();
    ral.configopts.csnidle.set(4'd15);
    ral.configopts.clkdiv.set(16'd2);
    csr_update(ral.configopts);
    fork
      cfg.force_spi_fsm_vif.force_sw_rst_in_state(3'h5);
      begin
        seg = spi_segment_item::type_id::create("seg_idle");
        seg.command_reg.direction = TxOnly;
        seg.command_reg.mode = Standard;
        seg.command_reg.csaat = 1'b0;
        seg.command_reg.len = 9'd3;
        for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'hF0);
        access_data_fifo(seg.spi_data, TxFifo);
        program_command_reg(seg.command_reg);
      end
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();

    // 5. InternalClkHigh -> Idle (state 3 -> 0)
    `uvm_info(`gfn, "Targeting InternalClkHigh -> Idle transition", UVM_LOW)
    wait_ready_for_command();
    ral.configopts.clkdiv.set(16'd5);
    csr_update(ral.configopts);
    fork
      cfg.force_spi_fsm_vif.force_sw_rst_in_state(3'h3);
      begin
        seg = spi_segment_item::type_id::create("seg_clkhigh");
        seg.command_reg.direction = TxOnly;
        seg.command_reg.mode = Standard;
        seg.command_reg.csaat = 1'b0;
        seg.command_reg.len = 9'd3;
        for (int b = 0; b < 4; b++) seg.spi_data.push_back(8'h55);
        access_data_fifo(seg.spi_data, TxFifo);
        program_command_reg(seg.command_reg);
      end
    join
    csr_utils_pkg::wait_no_outstanding_access();
    cfg.clk_rst_vif.wait_clks(20);
    spi_host_init();

    // 6. InternalClkLow -> WaitTrail (with CPHA=1)
    `uvm_info(`gfn, "Targeting InternalClkLow -> WaitTrail with CPHA=1", UVM_LOW)
    wait_ready_for_command();
    ral.configopts.cpha.set(1'b1);
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
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1));
    end
    spi_host_init();
  endtask : target_fsm_transitions
endclass : spi_host_sw_reset_vseq
