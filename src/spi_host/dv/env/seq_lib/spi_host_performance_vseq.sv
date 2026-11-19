// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies SPI Host peak serial throughput and back-to-back segment streaming at minimum
// CONFIGOPTS latencies (CLKDIV=0, CSNLEAD=0, CSNTRAIL=0, CSNIDLE=0) with zero artificial inter-txn
// or polling sleeps and quantitative bit-rate / inter-segment gap assertions (Comment #23).
class spi_host_performance_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_performance_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans == cfg.seq_cfg.host_spi_max_trans;}
  constraint intr_dly_c {clear_intr_dly == cfg.seq_cfg.host_spi_min_dly;}
  constraint fifo_dly_c {
    rx_fifo_access_dly == cfg.seq_cfg.host_spi_min_dly;
    tx_fifo_access_dly == cfg.seq_cfg.host_spi_min_dly;
  }

  constraint spi_config_regs_c {
    spi_config_regs.cpol     == 1'b0;
    spi_config_regs.cpha     == 1'b0;
    spi_config_regs.fullcyc  == 1'b0;
    spi_config_regs.csnlead  == cfg.seq_cfg.host_spi_min_csn_latency;
    spi_config_regs.csntrail == cfg.seq_cfg.host_spi_min_csn_latency;
    spi_config_regs.csnidle  == cfg.seq_cfg.host_spi_min_csn_latency;
  }

  constraint spi_config_regs_clkdiv_c {
    spi_config_regs.clkdiv == cfg.seq_cfg.host_spi_min_clkdiv;
  }

  virtual task pre_start();
    super.pre_start();
    run_cov_stimulus     = 1'b0;
    inter_trans_delay_ns = 0;
    rx_poll_min_delay_ns = 0;
    rx_poll_max_delay_ns = 0;
  endtask

  // Measures core-clock elapsed frame time and inter-SCK edge gaps across 4 chained back-to-back
  // 64-byte Quad segments (256 bytes = 2,048 serial bits, theoretical ideal = 1,026 core clocks at
  // clkdiv=0 -> 2.0 bits/clk) and a 64-byte Bidir full-duplex transfer, asserting:
  //   - Zero TXSTALL / RXSTALL throughout streaming
  //   - Max inter-SCK edge gap <= 4 core clocks across CSAAT=1 segment boundaries (zero bubbles)
  //   - Achieved Quad serial throughput >= 85% of theoretical 2.0 bits/clk peak (active_clks <= 1200)
  virtual task run_checked_max_bandwidth_streaming_test();
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         rdata;
    int unsigned       prev_tx_cnt, prev_rx_cnt;
    int unsigned       active_clks          = 0;
    int unsigned       cur_sck_gap_clks     = 0;
    int unsigned       max_inter_sck_gap    = 0;
    int unsigned       sck_edges_seen       = 0;
    bit                saw_stall            = 1'b0;
    logic              prev_sck             = 1'b0;

    `uvm_info(`gfn, "Running checked max-bandwidth Quad & Bidir streaming throughput test (clkdiv=0)", UVM_LOW)
    spi_host_init();
    program_spi_host_regs();
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);

    // 1. Pre-load 64 words (256 bytes = 2,048 bits) and 4 chained 64B Quad segments while SPIEN=0
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_0000)); // clkdiv=0, csnlead/trail/idle=0
    csr_wr(.ptr(ral.control),    .value(32'h2000_007F)); // spien=0, output_en=1

    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    for (int unsigned w = 0; w < 64; w++) begin
      ral.txdata.write(status, 0, 32'hF0E1_D2C3 ^ (w * 32'h0101_0101));
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    for (int seg_i = 0; seg_i < 4; seg_i++) begin
      cmd.direction = TxOnly;
      cmd.mode      = Quad;
      cmd.csaat     = (seg_i < 3) ? 1'b1 : 1'b0;
      cmd.len       = 9'd63; // 64 bytes per segment (4 x 64B = 256B)
      program_command_reg(cmd);
    end

    fork
      begin : quad_rate_observer
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        prev_sck = cfg.spi_passthrough_vif.cio_sck_o;
        while (cfg.m_spi_agent_cfg.vif.csb[0] === 1'b0) begin
          @(posedge cfg.clk_rst_vif.clk);
          if (cfg.m_spi_agent_cfg.vif.csb[0] !== 1'b0) break;
          active_clks++;
          if (cfg.spi_passthrough_vif.cio_sck_o !== prev_sck) begin
            if (sck_edges_seen > 0 && cur_sck_gap_clks > max_inter_sck_gap) begin
              max_inter_sck_gap = cur_sck_gap_clks;
            end
            sck_edges_seen++;
            cur_sck_gap_clks = 1;
            prev_sck = cfg.spi_passthrough_vif.cio_sck_o;
          end else begin
            cur_sck_gap_clks++;
          end
        end
      end
      begin : enable_quad_stream
        spi_host_status_t st;
        csr_wr(.ptr(ral.control), .value(32'hA000_007F)); // spien=1 releases 4-segment Quad stream
        do begin
          csr_rd(.ptr(ral.status), .value(st));
          saw_stall |= (st.txstall || st.rxstall);
        end while (st.active);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
      end
    join

    `uvm_info(`gfn, $sformatf(
      "Quad streaming metrics: 2048 bits in %0d active core clocks (sck_edges=%0d, max_sck_gap=%0d clks)",
      active_clks, sck_edges_seen, max_inter_sck_gap), UVM_LOW)

    `DV_CHECK_EQ(saw_stall, 1'b0, "Unexpected TXSTALL/RXSTALL during max-bandwidth Quad stream")
    `DV_CHECK_EQ(sck_edges_seen, 1024, "Expected 1024 SCK edges (512 cycles) for 256-byte Quad stream")
    `DV_CHECK_LE(max_inter_sck_gap, 4,
                 "Avoidable inter-segment pipeline bubble detected across CSAAT=1 Quad segments")
    `DV_CHECK_LE(active_clks, 1200,
                 "Quad serial bit-rate utilization fell below >=85% threshold (2048 bits / <=1200 clks)")
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 4,
                 "Expected scoreboard to verify all 4 chained max-bandwidth Quad segments")

    // 2. Back-to-back 64-byte full-duplex Bidir transfer at clkdiv=0 (512 SCK cycles = 1,024 half-cycles)
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    csr_wr(.ptr(ral.control), .value(32'h2000_007F)); // spien=0 for pre-load
    for (int unsigned w = 0; w < 16; w++) begin
      ral.txdata.write(status, 0, 32'hA55A_0F00 + w);
    end
    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd63; // 64 bytes (16 words)
    program_command_reg(cmd);

    active_clks = 0;
    fork
      begin
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        while (cfg.m_spi_agent_cfg.vif.csb[0] === 1'b0) begin
          @(posedge cfg.clk_rst_vif.clk);
          if (cfg.m_spi_agent_cfg.vif.csb[0] === 1'b0) active_clks++;
        end
      end
      begin
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int b = 0; b < 512; b++) begin
          cfg.m_spi_agent_cfg.vif.sio_out[1] <= bit'(b[0] ^ b[2]);
          @(negedge cfg.m_spi_agent_cfg.vif.sck);
        end
        cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      end
      begin
        csr_wr(.ptr(ral.control), .value(32'hA000_007F)); // spien=1
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
      end
    join

    `DV_CHECK_LE(active_clks, 1150,
                 "Full-duplex Bidir 64B transfer exceeded expected min-latency cycle bound (<=1150 clks)")
    for (int unsigned w = 0; w < 16; w++) begin
      ral.rxdata.read(status, 0, rdata);
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1)
    `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 16)
  endtask

  virtual task body();
    // 1. Quantitative max-bandwidth Quad & Bidir streaming throughput/gap checks
    run_checked_max_bandwidth_streaming_test();

    // 2. Zero-delay multi-mode back-to-back randomized stream
    fork
      begin : isolation_fork
        fork
          start_agent_reactive_seqs();
        join_none

        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          csr_spinwait(.ptr(ral.status.cmdqd),  .exp_data(4'h0), .backdoor(1'b1));
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b1));
          csr_spinwait(.ptr(ral.status.rxqd),   .exp_data(8'h0), .backdoor(1'b1));
          cfg.clk_rst_vif.wait_clks(50);
        end
        disable fork;
      end
      begin
        read_rx_fifo();
      end
    join
  endtask : body

  virtual task start_spi_host_trans(int num_transactions, bit wait_ready = 1'b1);
    cfg.seq_cfg.std_en  = 1;
    cfg.seq_cfg.dual_en = 1;
    cfg.seq_cfg.quad_en = 1;
    super.start_spi_host_trans(num_trans);
  endtask

  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(transaction,
      num_segments inside {[1 : 3]};
      cmd inside {WriteQuad, ReadQuad, WriteDual, ReadDual, ReadStd, WriteStd};
    )
  endtask

endclass : spi_host_performance_vseq
