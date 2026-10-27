// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// passthrough_mode test vseq
// SPI_HOST HWIP Technical Specification Block Diagram
class spi_host_passthrough_mode_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_passthrough_mode_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
  endtask

  virtual task body();
    bit en = 1'b1;
    fork
    begin
      forever begin
        if (!en) break;
        @(posedge cfg.clk_rst_vif.clk);
        if (cfg.spi_passthrough_vif.passthrough_en && (SPI_HOST_NUM_CS == 1)) begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, cfg.spi_passthrough_vif.sck)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, cfg.spi_passthrough_vif.sck_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o, cfg.spi_passthrough_vif.csb)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o, cfg.spi_passthrough_vif.csb_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, cfg.spi_passthrough_vif.s_en)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, cfg.spi_passthrough_vif.is)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_i, cfg.spi_passthrough_vif.os)
        end else begin
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sck_en_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_o, 1'b1)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_csb_en_o, 1'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_o, 4'b0)
          `DV_CHECK_EQ(cfg.spi_passthrough_vif.os, 4'hf)
        end
      end
    end
    begin
      while (en) begin
        @(posedge cfg.clk_rst_vif.clk);
        cfg.spi_passthrough_vif.sck_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.csb_en <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.s_en   <= $urandom_range(0, 4'hf);
        cfg.spi_passthrough_vif.csb    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.sck    <= $urandom_range(0, 1);
        cfg.spi_passthrough_vif.is     <= $urandom_range(100, 2000);
        cfg.spi_passthrough_vif.cio_sd_i <= $urandom_range(100, 2000);
      end
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 20));
    end
    begin
      @(posedge cfg.clk_rst_vif.clk);
      for (int i = 0; i < (num_trans * num_runs); i++) begin
        bit pt_en = (i % 2);
        @(posedge cfg.clk_rst_vif.clk);
        cfg.spi_passthrough_vif.passthrough_en <= (SPI_HOST_NUM_CS == 1) ? pt_en : 1'b0;
        cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      end
      en = 1'b0;
    end
    join
    cfg.spi_passthrough_vif.passthrough_en <= 1'b0;
    cfg.clk_rst_vif.wait_clks(5);

    // Verify normal SPI host operation and scoreboard checking on non-passthrough traffic
    spi_host_init();
    program_spi_host_regs();
    begin
      uvm_status_e status;
      uvm_reg_data_t rdata;
      spi_host_command_t cmd;
      int unsigned prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
      int unsigned prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
      write_txdata(32'hDEAD_BEEF, 4'hf, status);
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
                     "Expected scoreboard TX check on baseline transfer in passthrough_mode test")
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     "Expected scoreboard RX check on baseline transfer in passthrough_mode test")
      end
    end
  endtask : body
endclass : spi_host_passthrough_mode_vseq
