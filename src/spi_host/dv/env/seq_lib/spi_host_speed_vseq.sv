// Copyright lowRISC contributors (OpenTitan project).
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
    bit [3:0] latency_vals[4] = '{4'd0, 4'd3, 4'd8, 4'd14};
    bit [15:0] clkdiv_vals[16] = '{
      16'd0,
      16'd1, 16'd5, 16'd10, 16'd15,
      16'h0020, 16'h0050, 16'h0080, 16'h00b0, 16'h00e0,
      16'h0200, 16'h4000, 16'h8000, 16'hb000, 16'he000,
      16'hffff
    };
    int clk_idx = 0;

    `uvm_info(`gfn, "Sweeping configopts register across all covergroup bins", UVM_LOW)
    for (int lead_i = 0; lead_i < 4; lead_i++) begin
      for (int idle_i = 0; idle_i < 4; idle_i++) begin
        for (int trail_i = 0; trail_i < 4; trail_i++) begin
          bit cpol_val = (lead_i % 2);
          bit cpha_val = (idle_i % 2);
          bit fullcyc_val = (trail_i % 2);
          csr_wr(.ptr(ral.configopts), .value({
            cpol_val, cpha_val, fullcyc_val, 1'b0,
            latency_vals[lead_i], latency_vals[trail_i], latency_vals[idle_i],
            clkdiv_vals[clk_idx]
          }));
          clk_idx = (clk_idx + 1) % 16;
        end
      end
    end
    // Restore clean default operating configopts
    csr_wr(.ptr(ral.configopts), .value({
      1'b0, 1'b0, 1'b0, 1'b0,
      4'd1, 4'd1, 4'd1,
      16'd2
    }));
  endtask

  virtual task body();
    sweep_config_opts();
    super.body();
  endtask

endclass : spi_host_speed_vseq
