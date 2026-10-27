// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// speed test vseq
class spi_host_speed_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_speed_vseq)
  `uvm_object_new

  constraint spi_config_regs_c {
      // configopts regs
      spi_config_regs.cpol dist {
        1'b0 :/ 1,
        1'b1 :/ 1
      };
      spi_config_regs.cpha dist {
        1'b0 :/ 1,
        1'b1 :/ 1
      };
      spi_config_regs.csnlead inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                       cfg.seq_cfg.host_spi_max_csn_latency]};
      spi_config_regs.csntrail inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                        cfg.seq_cfg.host_spi_max_csn_latency]};
      spi_config_regs.csnidle inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                       cfg.seq_cfg.host_spi_max_csn_latency]};
  }

  constraint spi_config_regs_clkdiv_c {
    // CLKDIV randomised not in the whole range since there's a dedicated VSEQ:
    // spi_host_upper_range_clkdiv_vseq.sv which uses the upper range of clock
    // divider values - this way we won't have super long  tests when running this VSEQ
    spi_config_regs.clkdiv inside {[cfg.seq_cfg.host_spi_min_clkdiv :
                                    cfg.seq_cfg.host_spi_lower_middle_clkdiv]};
  }

  virtual task start_spi_host_trans(int num_transactions, bit wait_ready = 1'b1);
    cfg.seq_cfg.std_en  = 1;
    cfg.seq_cfg.dual_en = 1;
    cfg.seq_cfg.quad_en = 1;
    super.start_spi_host_trans(num_transactions);
  endtask

  virtual task sweep_config_opts();
    uvm_status_e status;
    uvm_reg_data_t rdata;
    spi_host_command_t cmd;
    bit [3:0] latency_vals[4] = '{4'd0, 4'd3, 4'd8, 4'd14};
    // Lower and bottom-eight clkdiv bins: {0}, {[1:15]} (4 bins), {[16'h10:16'hfe]} (5 bins)
    // Upper-eight and max (0xFFFF) bins are verified via unforced checked transfers in upper_range_clkdiv_vseq.
    bit [15:0] xfer_clkdiv_vals[10] = '{
      16'd0,
      16'd1, 16'd5, 16'd10, 16'd15,
      16'h0020, 16'h0050, 16'h0080, 16'h00b0, 16'h00e0
    };
    int iter_idx = 0;

    `uvm_info(`gfn, "Executing scoreboard-checked TX/RX transfers across CS0/CS1 timing & clkdiv bins", UVM_LOW)
    csr_wr(.ptr(ral.control), .value(32'hA000_007F)); // spien=1, output_en=1

    for (int lead_i = 0; lead_i < 4; lead_i++) begin
      for (int idle_i = 0; idle_i < 4; idle_i++) begin
        for (int trail_i = 0; trail_i < 4; trail_i++) begin
          bit cpol_val    = bit'(lead_i % 2);
          bit cpha_val    = bit'(idle_i % 2);
          bit fullcyc_val = bit'(trail_i % 2);
          int cs_idx      = ((lead_i / 2) ^ (idle_i / 2) ^ (trail_i % 2)) % SPI_HOST_NUM_CS;
          bit [15:0] cur_clkdiv = xfer_clkdiv_vals[iter_idx % $size(xfer_clkdiv_vals)];
          bit [31:0] cfg_word   = {
            cpol_val, cpha_val, fullcyc_val, 1'b0,
            latency_vals[lead_i], latency_vals[trail_i], latency_vals[idle_i],
            cur_clkdiv
          };

          csr_wr(.ptr(ral.csid), .value(cs_idx));
          if (cs_idx == 1) begin
            csr_wr(.ptr(ral.configopts_1), .value(cfg_word));
          end else begin
            csr_wr(.ptr(ral.configopts), .value(cfg_word));
          end

          // Execute a scoreboard-checked SPI transfer under the programmed CONFIGOPTS setting:
          // Use Bidir (TX + RX) for all compatible sampling modes; per spi_host_fsm.sv:275,
          // full-cycle RX sampling is incompatible with CPHA=1, so use TxOnly for (cpha=1, fullcyc=1).
          write_txdata(32'hA55A_00FF ^ {16'(iter_idx), 8'(lead_i), 8'(trail_i)}, 4'b0001, status);
          wait_ready_for_command();
          cmd.direction = (cpha_val && fullcyc_val) ? TxOnly : Bidir;
          cmd.mode      = Standard;
          cmd.csaat     = 1'b0;
          cmd.len       = 9'd0; // 1-byte checked transfer
          program_command_reg(cmd);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

          if (cmd.direction == Bidir) begin
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
            ral.rxdata.read(status, 0, rdata);
          end

          iter_idx++;
        end
      end
    end

    // Also verify end-to-end Flash page program + Quad readback across both CS0 and CS1
    begin
      int saved_num_words = num_words;
      num_words = 4;
      for (int i = 0; i < 4; i++) begin
        int cs_idx = i % SPI_HOST_NUM_CS;
        bit [31:0] flash_cfg = {
          1'b0, 1'b0, bit'(i % 2 == 1), 1'b0,
          latency_vals[i], latency_vals[3 - i], latency_vals[i],
          xfer_clkdiv_vals[i]
        };
        if (cs_idx == 1) begin
          csr_wr(.ptr(ral.configopts_1), .value(flash_cfg));
        end else begin
          csr_wr(.ptr(ral.configopts), .value(flash_cfg));
        end
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
          flash_addr < 32'h080000;
          flash_addr[7:0] == 8'h00;
        )
        `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
        run_flash_page_program_and_read(cs_idx[1:0]);
      end
      num_words = saved_num_words;
    end

    // Restore clean default operating configopts on both chip selects
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0002));
  endtask

  virtual task body();
    super.body();
    sweep_config_opts();
  endtask

endclass : spi_host_speed_vseq
