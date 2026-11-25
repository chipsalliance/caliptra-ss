// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies mid-transaction CONTROL.SPIEN = 0 suspension:
//   1) Deterministically overlaps active mid-byte shifting (CSB == 0, ACTIVE == 1),
//   2) Continuously checks clock-by-clock hold invariants on SCK, CSB, SD, and SD_EN,
//   3) Exercises a deliberate pin-toggle violation negative control, and
//   4) Verifies lossless resume on CONTROL.SPIEN = 1 followed by randomized multi-toggle stress
//      (Comment #10).
class spi_host_spien_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_spien_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.seq_cfg.host_spi_min_len     = 4;
    cfg.seq_cfg.host_spi_max_len     = 4;
    cfg.seq_cfg.host_spi_min_num_seg = 4;
    cfg.seq_cfg.host_spi_max_num_seg = 8;
  endtask

  virtual function void check_spien_pause_hold(logic exp_sck,
                                               logic [CSB_WIDTH-1:0] exp_csb,
                                               logic [3:0] exp_sd,
                                               logic [3:0] exp_sd_en,
                                               int unsigned cyc_idx);
    if (cfg.spi_passthrough_vif.cio_sck_o !== exp_sck ||
        cfg.m_spi_agent_cfg.vif.csb !== exp_csb ||
        cfg.spi_passthrough_vif.cio_sd_o !== exp_sd ||
        cfg.spi_passthrough_vif.cio_sd_en_o !== exp_sd_en) begin
      `uvm_error(`gfn, $sformatf(
        "SPIEN=0 pin-hold invariant violated at pause cycle %0d: sck=%b(exp %b) csb=%b(exp %b) sd=%h(exp %h) sd_en=%h(exp %h)",
        cyc_idx,
        cfg.spi_passthrough_vif.cio_sck_o, exp_sck,
        cfg.m_spi_agent_cfg.vif.csb, exp_csb,
        cfg.spi_passthrough_vif.cio_sd_o, exp_sd,
        cfg.spi_passthrough_vif.cio_sd_en_o, exp_sd_en))
    end
  endfunction

  virtual task run_checked_spien_pause_hold_and_fault_control();
    spi_host_command_t       cmd;
    uvm_status_e             st;
    uvm_reg_data_t           rdata;
    int unsigned             prev_tx_cnt, prev_rx_cnt;
    bit [31:0]               exp_tx_word = 32'hA55A_C33C;
    bit [31:0]               exp_rx_word = 32'h6996_F00F;
    logic                    hold_sck;
    logic [CSB_WIDTH-1:0]    hold_csb;
    logic [3:0]              hold_sd;
    logic [3:0]              hold_sd_en;

    `uvm_info(`gfn, "Running deterministic mid-byte SPIEN=0 pin-hold check, fault control & resume", UVM_LOW)
    spi_host_init();
    program_spi_host_regs();
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0111_000C)); // Mode 0, clkdiv=12 (13 clks / half-SCK)
    csr_wr(.ptr(ral.control),    .value(32'hA000_007F)); // spien=1, output_en=1

    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    write_txdata(exp_tx_word, 4'hf, st);
    `DV_CHECK_EQ(st, UVM_IS_OK)

    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3; // 4 bytes

    fork
      begin : periph_miso_drv
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int byte_i = 0; byte_i < 4; byte_i++) begin
          bit [7:0] bval = exp_rx_word[byte_i * 8 +: 8];
          for (int bit_i = 7; bit_i >= 0; bit_i--) begin
            cfg.m_spi_agent_cfg.vif.sio_out[1] <= bval[bit_i];
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
          end
        end
        cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      end
      begin : host_pause_and_check
        spi_host_scb_neg_catcher hold_catcher = spi_host_scb_neg_catcher::type_id::create("spien_hold_catcher");
        program_command_reg(cmd);

        // Wait until CSB[0] is active low and 3 SCK edges elapse (strictly mid-byte 0!)
        wait (cfg.m_spi_agent_cfg.vif.csb[0] === 1'b0);
        repeat (3) @(cfg.m_spi_agent_cfg.vif.sck);

        // Deassert CONTROL.SPIEN = 0 mid-byte via frontdoor AXI write and snapshot pins immediately
        csr_wr(.ptr(ral.control), .value(32'h2000_007F)); // spien=0, output_en=1
        cfg.clk_rst_vif.wait_clks(1);

        hold_sck   = cfg.spi_passthrough_vif.cio_sck_o;
        hold_csb   = cfg.m_spi_agent_cfg.vif.csb;
        hold_sd    = cfg.spi_passthrough_vif.cio_sd_o;
        hold_sd_en = cfg.spi_passthrough_vif.cio_sd_en_o;
        `DV_CHECK_EQ(hold_csb[0], 1'b0,
                     "SPIEN=0 must overlap active in-flight transfer with CSB[0]==0")
        `DV_CHECK_EQ(hold_sd_en, 4'b0001, "Expected SD_EN[0]=1 held steady during SPIEN=0 pause")

        // Prove STATUS.ACTIVE == 1 and verify pins stayed frozen across the CSR read itself
        csr_rd_check(.ptr(ral.status.active), .compare_value(1'b1));
        check_spien_pause_hold(hold_sck, hold_csb, hold_sd, hold_sd_en, 0);

        // Continuously sample and verify pin hold on every core clock for 60 cycles (>2 full SCK periods)
        for (int unsigned cyc = 0; cyc < 60; cyc++) begin
          @(posedge cfg.clk_rst_vif.clk);
          check_spien_pause_hold(hold_sck, hold_csb, hold_sd, hold_sd_en, cyc);
        end

        // Re-enable CONTROL.SPIEN = 1, verify negative control detects the first resumed SCK toggle,
        // and verify lossless transfer completion
        csr_wr(.ptr(ral.control), .value(32'hA000_007F));

        @(cfg.m_spi_agent_cfg.vif.sck);
        hold_catcher.match_pattern = "*SPIEN=0 pin-hold invariant violated*";
        uvm_report_cb::add(null, hold_catcher);
        check_spien_pause_hold(hold_sck, hold_csb, hold_sd, hold_sd_en, 999);
        uvm_report_cb::delete(null, hold_catcher);
        `DV_CHECK_EQ(hold_catcher.caught_err_cnt, 1,
                     "Expected SPIEN=0 hold-invariant negative control to catch resumed SCK toggle")

        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      end
    join

    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    ral.rxdata.read(st, 0, rdata);
    `DV_CHECK_EQ(st, UVM_IS_OK)
    `DV_CHECK_EQ(rdata, exp_rx_word, "Resumed SPIEN=0->1 Bidir RXDATA payload mismatch")
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                 "Expected scoreboard TX check on resumed SPIEN=0->1 transfer")
    `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                 "Expected scoreboard RX check on resumed SPIEN=0->1 transfer")
  endtask

  virtual task body();
    spi_host_status_t status;

    // 1. Deterministic active-overlap, continuous cycle-by-cycle pin hold, negative control & resume
    run_checked_spien_pause_hold_and_fault_control();

    // 2. Randomized multi-segment SPIEN=0/1 toggle stress
    fork start_agent_reactive_seqs(); join_none
    program_spi_host_regs();
    wait_ready_for_command();

    fork
      begin
        read_rx_fifo();
      end
      begin
        start_spi_host_trans(.num_transactions(3), .wait_ready(1));
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .timeout_ns(500_000_000));
        csr_spinwait(.ptr(ral.status.rxqd), .exp_data(8'h0), .timeout_ns(500_000_000));
        cfg.clk_rst_vif.wait_clks(100);
      end
      begin
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b1), .backdoor(1), .timeout_ns(500_000_000));
        do begin
          cfg.clk_rst_vif.wait_clks($urandom_range(20, 2000));

          csr_wr(.ptr(ral.control.spien), .value(1'b0));
          cfg.clk_rst_vif.wait_clks($urandom_range(20, 2000));
          csr_wr(.ptr(ral.control.spien), .value(1'b1));

          csr_rd(.ptr(ral.status), .value(status), .backdoor(1));
        end while (status.active == 1);
      end
    join
  endtask : body

endclass : spi_host_spien_vseq
