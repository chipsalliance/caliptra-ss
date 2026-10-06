// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test verifies extended spi transaction and covers
// idlecsbactive state and next command triggers fsm state.
class spi_host_idlecsbactive_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_idlecsbactive_vseq)
  `uvm_object_new

 spi_host_command_t cmd_copy;

  constraint spi_config_regs_clkdiv_c {
    spi_config_regs.clkdiv inside {[0 : 1]};
  }

  virtual task pre_start();
    cfg.en_scb = 0;
    cfg.seq_cfg.host_spi_min_len = 4;
    cfg.seq_cfg.host_spi_max_len = 4;
    super.pre_start();
  endtask

  virtual task body();
    fork
      begin : isolation_fork
        fork
          start_agent_reactive_seqs();
        join_none

        begin
          wait_ready_for_command();
          // program spi host regs and send transaction
          // csaat on last segment keeps CS active
          start_spi_host_trans_w_csaat(.num_transactions(1));
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));
          cfg.clk_rst_vif.wait_clks(10);
          // Exercise IdleCSBActive -> Idle transition via SW reset
          ral.control.sw_rst.set(1'b1);
          csr_update(ral.control);
          cfg.clk_rst_vif.wait_clks(10);
          ral.control.sw_rst.set(1'b0);
          csr_update(ral.control);
          cfg.clk_rst_vif.wait_clks(10);
          spi_host_init();
          generate_transaction();
          // send normal spi transaction csaat last segment 0 to release CS
          send_trans_w_csaat(transaction, 1, 0);
          cfg.clk_rst_vif.wait_clks(100);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));

          // Exercise IdleCSBActive -> WaitTrail -> WaitIdle -> CSBSwitch when switching CSID
          if (SPI_HOST_NUM_CS > 1) begin
            uvm_status_e status;
            spi_host_command_t cmd;

            // Segment 1 on CS0 with CSAAT=1 -> parks in IdleCSBActive
            csr_wr(.ptr(ral.csid), .value(32'h0));
            ral.txdata.write(status, 0, 32'hA5A5_5A5A);
            wait_ready_for_command();
            cmd.direction = TxOnly;
            cmd.mode      = Standard;
            cmd.csaat     = 1'b1;
            cmd.len       = 9'd3;
            program_command_reg(cmd);
            csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));

            // Segment 2 on CS1 with CSAAT=0 while parked in IdleCSBActive (command_i.csid != csid_q)
            csr_wr(.ptr(ral.csid), .value(32'h1));
            ral.txdata.write(status, 0, 32'h5A5A_A5A5);
            wait_ready_for_command();
            cmd.direction = TxOnly;
            cmd.mode      = Standard;
            cmd.csaat     = 1'b0;
            cmd.len       = 9'd3;
            program_command_reg(cmd);
            csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0));
            csr_wr(.ptr(ral.csid), .value(32'h0));
          end
        end

        disable fork;
      end
    join
    begin
      read_rx_fifo();
    end
  endtask : body

  // sending tx requests to the agent
  virtual task send_trans_w_csaat(spi_transaction_item trans, bit wait_ready = 1'b1,
                               bit csaathold = 1'b1);
    spi_segment_item segment;
    if (csaathold) begin
      trans.segments[0].command_reg.csaat = 1'b1;
    end else begin
      trans.segments[0].command_reg.csaat = 1'b0;
    end
    while (trans.segments.size() > 0) begin
      // wait on DUT ready
      segment = trans.segments.pop_back();
      if (wait_ready) wait_ready_for_command();
      // lock fifo to this seq
      spi_host_atomic.get(1);
      // write data to fifo
      if (segment.command_reg.direction != RxOnly) begin
        access_data_fifo(segment.spi_data, TxFifo);
      end
      program_command_reg(segment.command_reg);
      spi_host_atomic.put(1);
    end
  endtask : send_trans_w_csaat

  virtual task start_spi_host_trans_w_csaat(int num_transactions, bit wait_ready = 1'b1,
                                         bit csaathold = 1'b1);
    program_spi_host_regs();
    if (wait_ready) wait_ready_for_command();
    for (int n = 0; n < num_transactions; n++) begin
      generate_transaction();
      send_trans_w_csaat(transaction, wait_ready,csaathold);
      if (wait_ready) wait_ready_for_command();
    end
    spi_host_txn_sent = 1;
  endtask

  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction, num_segments == 4; cmd == ReadStd;)
  endtask

endclass : spi_host_idlecsbactive_vseq
