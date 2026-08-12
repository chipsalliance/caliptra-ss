// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)
  `uvm_object_new

  constraint spi_config_regs_c {
    // configopts regs
    spi_config_regs.cpol == 1'b0;
    spi_config_regs.cpha == 1'b0;
    spi_config_regs.csnlead == cfg.seq_cfg.host_spi_max_csn_latency;
    spi_config_regs.csntrail == cfg.seq_cfg.host_spi_max_csn_latency;
  }

  constraint spi_config_regs_clkdiv_c {
    spi_config_regs.clkdiv <= cfg.seq_cfg.host_spi_middle_clkdiv;
  }


  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_smoke_vseq'", UVM_DEBUG)
    cfg.num_dummy = 0;
    apply_reset("HARD");
    spi_host_init();
    fork
      begin : isolation_fork
        fork
          start_agent_reactive_seqs();
        join_none

        begin
          start_spi_host_trans(num_trans);
          csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0));
          csr_spinwait(.ptr(ral.status.rxqd), .exp_data(8'h0), .backdoor(1'b0));
          cfg.clk_rst_vif.wait_clks(100);
        end

        disable fork;
      end
      begin
        spi_host_status_t status_val;
        // Wait for transaction to start or bytes to arrive, and continuously drain the RX FIFO
        // This avoids deadlock with the Hardware Loopback which floods the RX FIFO in real-time.
        while (!spi_host_txn_sent || status_val.rx_qd > 0 || !status_val.rxempty) begin
          csr_rd(.ptr(ral.status), .value(status_val));
          if (status_val.rx_qd > 0) begin
            read_rx_fifo();
          end
          cfg.clk_rst_vif.wait_clks(10);
        end
        // Final drain just in case anything arrived right at the end
        read_rx_fifo();
      end
    join
  endtask : body

endclass : spi_host_smoke_vseq
