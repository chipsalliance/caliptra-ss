// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Dedicated directed boundary, FIFO-window error, reactive-responder, and functional closure
// sequence separated from short spi_host_smoke_vseq so child/stress sequences do not replay
// heavy directed closure routines (Comments #6, #8, #9, #18, #23).
class spi_host_closure_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_closure_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    run_cov_stimulus = 1'b1;
  endtask : pre_start

  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_closure_vseq'", UVM_LOW)
    super.body();

    // 1. Checked maximum-length 512-byte (LEN = 511, 128-word) TxOnly, RxOnly, and Bidir
    //    streaming data transfers with live TX refill (>73 words) and RX drain (>64 words)
    run_max_len_512b_data_transfers();

    // 2. Explicit FIFO/command-queue/watermark boundary verification (BYTEORDER, CMDQD=0..8,
    //    TXQD=72 vs 73, and TX/RX watermarks at 0, 1, depth-1, depth, depth+1, 0x7F, 255)
    run_fifo_and_watermark_boundary_checks();

    // 3. Bus-level wrong-direction FIFO-window errors (RXDATA write / TXDATA read SLVERR,
    //    ERROR_STATUS==0, TX/RX FIFO preservation, and post-error recovery)
    run_wrong_direction_window_error_checks();

    // 4. Focused validation of opt-in reactive SPI device responder across CS0/CS1 and
    //    Standard/Dual/Quad lane significance (Comment #18)
    run_reactive_device_driver_validation();

    `uvm_info(`gfn, "Finished 'spi_host_closure_vseq' successfully", UVM_LOW)
  endtask : body

  virtual task run_max_len_512b_data_transfers();
    localparam int unsigned MAX_WORDS = 128; // 512 bytes (LEN = 511)
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         tx_words[MAX_WORDS];
    bit [31:0]         exp_rx_words[MAX_WORDS];
    bit [7:0]          exp_rx_bytes[MAX_WORDS * 4];
    int unsigned       prev_tx_cnt, prev_rx_cnt;

    `uvm_info(`gfn, "Running checked 512-byte (LEN=511) TxOnly, RxOnly, and Bidir transfers", UVM_LOW)
    spi_host_init();
    program_spi_host_regs();
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0001)); // Mode 0, clkdiv=1

    for (int unsigned w = 0; w < MAX_WORDS; w++) begin
      tx_words[w] = 32'hA500_0000 ^ (w * 32'h0103_0507) ^ 32'h005A_C33C;
      for (int b = 0; b < 4; b++) begin
        exp_rx_bytes[w * 4 + b] = 8'((w * 4 + b) * 7 + 8'h3D);
        exp_rx_words[w][b * 8 +: 8] = exp_rx_bytes[w * 4 + b];
      end
    end

    // 1a. 512-byte (LEN = 511) Quad TxOnly transfer with live TX refill (>73 words)
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    for (int unsigned w = 0; w < 64; w++) begin
      ral.txdata.write(status, 0, tx_words[w]);
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Quad;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd511;
    program_command_reg(cmd);
    for (int unsigned w = 64; w < MAX_WORDS; w++) begin
      csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
      ral.txdata.write(status, 0, tx_words[w]);
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                 .spinwait_delay_ns(50), .timeout_ns(50_000_000));
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                 "Expected scoreboard to verify 512-byte (LEN=511) Quad TxOnly transfer")

    // 1b. 512-byte (LEN = 511) Quad RxOnly transfer with live RX drain (>64 words)
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0002)); // Mode 0, clkdiv=2
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    wait_ready_for_command();
    cmd.direction = RxOnly;
    cmd.mode      = Quad;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd511;
    fork
      begin
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int unsigned byte_i = 0; byte_i < MAX_WORDS * 4; byte_i++) begin
          cfg.m_spi_agent_cfg.vif.sio_out[3:0] <= exp_rx_bytes[byte_i][7:4];
          @(negedge cfg.m_spi_agent_cfg.vif.sck);
          cfg.m_spi_agent_cfg.vif.sio_out[3:0] <= exp_rx_bytes[byte_i][3:0];
          @(negedge cfg.m_spi_agent_cfg.vif.sck);
        end
        cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      end
      begin
        int unsigned rx_rcvd = 0;
        program_command_reg(cmd);
        while (rx_rcvd < MAX_WORDS) begin
          spi_host_status_t st;
          csr_rd(.ptr(ral.status), .value(st));
          for (int unsigned k = 0; k < st.rx_qd && rx_rcvd < MAX_WORDS; k++) begin
            bit [31:0] rword;
            ral.rxdata.read(status, 0, rword);
            `DV_CHECK_EQ(status, UVM_IS_OK)
            `DV_CHECK_EQ(rword, exp_rx_words[rx_rcvd],
                         $sformatf("512B Quad RxOnly mismatch at word %0d", rx_rcvd))
            rx_rcvd++;
          end
          if (rx_rcvd < MAX_WORDS && st.rx_qd == 0) cfg.clk_rst_vif.wait_clks(4);
        end
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(50), .timeout_ns(50_000_000));
      end
    join
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                 "Expected scoreboard segment check on 512-byte Quad RxOnly transfer")
    `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + MAX_WORDS,
                 "Expected scoreboard to verify all 128 RX words of 512-byte Quad RxOnly transfer")

    // 1c. 512-byte (LEN = 511) Standard Bidir transfer with interleaved TX refill & RX drain
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0001)); // Mode 0, clkdiv=1
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    for (int unsigned w = 0; w < 64; w++) begin
      ral.txdata.write(status, 0, tx_words[w] ^ 32'hFFFF_0000);
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    wait_ready_for_command();
    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd511;
    fork
      begin
        @(negedge cfg.m_spi_agent_cfg.vif.csb[0]);
        for (int unsigned byte_i = 0; byte_i < MAX_WORDS * 4; byte_i++) begin
          bit [7:0] bval = exp_rx_bytes[byte_i] ^ 8'h55;
          for (int bit_i = 7; bit_i >= 0; bit_i--) begin
            cfg.m_spi_agent_cfg.vif.sio_out[1] <= bval[bit_i];
            @(negedge cfg.m_spi_agent_cfg.vif.sck);
          end
        end
        cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      end
      begin
        int unsigned tx_sent = 64;
        int unsigned rx_rcvd = 0;
        program_command_reg(cmd);
        while (tx_sent < MAX_WORDS || rx_rcvd < MAX_WORDS) begin
          spi_host_status_t st;
          csr_rd(.ptr(ral.status), .value(st));
          while (tx_sent < MAX_WORDS && st.tx_qd < 68) begin
            ral.txdata.write(status, 0, tx_words[tx_sent] ^ 32'hFFFF_0000);
            `DV_CHECK_EQ(status, UVM_IS_OK)
            tx_sent++;
            st.tx_qd++;
          end
          while (rx_rcvd < MAX_WORDS && st.rx_qd > 0) begin
            bit [31:0] rword;
            ral.rxdata.read(status, 0, rword);
            `DV_CHECK_EQ(status, UVM_IS_OK)
            `DV_CHECK_EQ(rword, exp_rx_words[rx_rcvd] ^ 32'h5555_5555,
                         $sformatf("512B Standard Bidir RX mismatch at word %0d", rx_rcvd))
            rx_rcvd++;
            st.rx_qd--;
          end
          if (rx_rcvd < MAX_WORDS && st.rx_qd == 0) cfg.clk_rst_vif.wait_clks(8);
        end
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0),
                     .spinwait_delay_ns(50), .timeout_ns(50_000_000));
      end
    join
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                 "Expected scoreboard TX check on 512-byte Standard Bidir transfer")
    `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + MAX_WORDS,
                 "Expected scoreboard RX check on 512-byte Standard Bidir transfer")
  endtask : run_max_len_512b_data_transfers

  virtual task run_fifo_and_watermark_boundary_checks();
    spi_host_command_t cmd;
    spi_host_status_t  st;
    uvm_status_e       status;
    bit [31:0]         rdata;

    `uvm_info(`gfn, "Running CMDQD=8/READY, TXQD=73/TXFULL, BYTEORDER, and watermark 0..255 boundary checks", UVM_LOW)
    spi_host_init();
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_0000));

    // 2a. Explicit STATUS.BYTEORDER & halted CMDQD=0..7 (READY=1) vs CMDQD=8 (READY=0) check
    csr_wr(.ptr(ral.control), .value(32'h2000_007F)); // spien=0, output_en=1, rx_wm=0x7F, tx_wm=0
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.byteorder, SPI_HOST_BYTEORDER, "STATUS.BYTEORDER target constant mismatch")
    `DV_CHECK_EQ(st.cmd_qd, 4'd0)
    `DV_CHECK_EQ(st.ready,  1'b1)

    for (int unsigned k = 1; k <= SPI_HOST_CMD_DEPTH; k++) begin
      cmd.direction = None;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      csr_rd(.ptr(ral.status), .value(st));
      `DV_CHECK_EQ(st.cmd_qd, 4'(k), $sformatf("Expected CMDQD=%0d after command push", k))
      `DV_CHECK_EQ(st.ready, (k < SPI_HOST_CMD_DEPTH),
                   $sformatf("Expected READY=%0b at CMDQD=%0d", (k < SPI_HOST_CMD_DEPTH), k))
    end
    // Enable SPIEN=1 so all 8 queued dummy commands execute and retire cleanly
    csr_wr(.ptr(ral.control), .value(32'hA000_007F));
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.cmd_qd, 4'd0)
    `DV_CHECK_EQ(st.ready,  1'b1)

    // 2b. Packer-inclusive TXQD = 72 (TXFULL = 0) vs TXQD = 73 (TXFULL = 1) + TX_WATERMARK boundaries
    //     (0, 1, 72, 73, 74, 255)
    csr_wr(.ptr(ral.control), .value(32'h2000_007F)); // spien=0, tx_wm=0, rx_wm=0x7F
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_qd,   8'd0)
    `DV_CHECK_EQ(st.txempty, 1'b1)
    `DV_CHECK_EQ(st.txfull,  1'b0)
    `DV_CHECK_EQ(st.tx_wm,   1'b0, "TXWM must be 0 when TX_WATERMARK=0 and TXQD=0")

    csr_wr(.ptr(ral.control), .value(32'h2000_017F)); // tx_wm=1
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_wm, 1'b1, "TXWM must be 1 when TXQD=0 < TX_WATERMARK=1")

    // Push word 1 -> TXQD=1 (u_select packer stage), TXWM drops to 0 for tx_wm=1
    ral.txdata.write(status, 0, 32'h1000_0001);
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_qd,   8'd1)
    `DV_CHECK_EQ(st.txempty, 1'b0)
    `DV_CHECK_EQ(st.txfull,  1'b0)
    `DV_CHECK_EQ(st.tx_wm,   1'b0, "TXWM must be 0 when TXQD=1 == TX_WATERMARK=1")

    // Fill to TXQD = 72 (SPI_HOST_TX_DEPTH): TXFULL must remain 0; check tx_wm=73 (1) vs tx_wm=72 (0)
    for (int unsigned w = 2; w <= SPI_HOST_TX_DEPTH; w++) begin
      ral.txdata.write(status, 0, 32'h1000_0000 + w);
    end
    csr_wr(.ptr(ral.control), .value(32'h2000_487F)); // tx_wm = 72 (0x48)
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_qd,  8'd72)
    `DV_CHECK_EQ(st.txfull, 1'b0, "TXFULL must remain 0 at TXQD=72 (1 word below 73-word packer+FIFO depth)")
    `DV_CHECK_EQ(st.tx_wm,  1'b0, "TXWM must be 0 at TXQD=72 == TX_WATERMARK=72")

    csr_wr(.ptr(ral.control), .value(32'h2000_497F)); // tx_wm = 73 (0x49 = SPI_HOST_TX_DEPTH + 1)
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_wm, 1'b1, "TXWM must be 1 at TXQD=72 < TX_WATERMARK=73")

    // Push 73rd word -> TXQD = 73, TXFULL = 1, TXWM(73) = 0; above-depth TXWM(74) & TXWM(255) = 1
    ral.txdata.write(status, 0, 32'h1000_0049);
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_qd,  8'd73, "Expected packer-inclusive full TXQD=73")
    `DV_CHECK_EQ(st.txfull, 1'b1,  "Expected TXFULL=1 at TXQD=73")
    `DV_CHECK_EQ(st.tx_wm,  1'b0,  "Expected TXWM=0 at TXQD=73 == TX_WATERMARK=73")

    csr_wr(.ptr(ral.control), .value(32'h2000_4A7F)); // tx_wm = 74 (above depth)
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_wm, 1'b1, "Above-depth TX_WATERMARK=74 must keep TXWM=1 even when TXFULL=1")

    csr_wr(.ptr(ral.control), .value(32'h2000_FF7F)); // tx_wm = 255
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.tx_wm, 1'b1, "Max TX_WATERMARK=255 must keep TXWM=1 even when TXFULL=1")

    // Flush TX FIFO via SW_RST
    spi_host_init();

    // 2c. RX_WATERMARK boundaries (0, 1, 63, 64, 65, 0x7F, 255) & RXFULL=1 at RXQD=64
    //     NOTE (Pending Designer Confirmation - Comment #25): RTL implements rx_wm = (rx_qd >= rx_watermark).
    csr_wr(.ptr(ral.csid),       .value(32'h0));
    csr_wr(.ptr(ral.configopts), .value(32'h0000_0000));
    csr_wr(.ptr(ral.control),    .value(32'hA000_0000)); // rx_wm = 0
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_qd, 8'd0)
    `DV_CHECK_EQ(st.rx_wm, 1'b1, "RXWM must be 1 when RXQD=0 >= RX_WATERMARK=0")

    csr_wr(.ptr(ral.control), .value(32'hA000_0001)); // rx_wm = 1
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_wm, 1'b0, "RXWM must be 0 when RXQD=0 < RX_WATERMARK=1")

    // Receive 1 word (4 bytes, Quad RxOnly) -> RXQD=1 -> RXWM(1)=1
    cmd.direction = RxOnly;
    cmd.mode      = Quad;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_qd, 8'd1)
    `DV_CHECK_EQ(st.rx_wm, 1'b1, "RXWM must be 1 when RXQD=1 == RX_WATERMARK=1")

    // Receive 62 more words (248 bytes, LEN=247) -> RXQD=63: check RXFULL=0, RXWM(64)=0, RXWM(63)=1
    csr_wr(.ptr(ral.control), .value(32'hA000_0040)); // rx_wm = 64 (0x40 = SPI_HOST_RX_DEPTH)
    cmd.len = 9'd247;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_qd,  8'd63)
    `DV_CHECK_EQ(st.rxfull, 1'b0)
    `DV_CHECK_EQ(st.rx_wm,  1'b0, "RXWM must be 0 at RXQD=63 < RX_WATERMARK=64")

    // Receive 64th word -> RXQD=64: RXFULL=1, RXWM(64)=1; above-depth RXWM(65), RXWM(0x7F), RXWM(255) = 0
    cmd.len = 9'd3;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(20));
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_qd,  8'd64)
    `DV_CHECK_EQ(st.rxfull, 1'b1)
    `DV_CHECK_EQ(st.rx_wm,  1'b1, "RXWM must be 1 at RXQD=64 == RX_WATERMARK=64")

    csr_wr(.ptr(ral.control), .value(32'hA000_0041)); // rx_wm = 65 (above depth)
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_wm, 1'b0, "Above-depth RX_WATERMARK=65 must keep RXWM=0 even when RXFULL=1")

    csr_wr(.ptr(ral.control), .value(32'hA000_007F)); // rx_wm = 0x7F (reset default)
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_wm, 1'b0, "Reset RX_WATERMARK=0x7F must keep RXWM=0 even when RXFULL=1")

    csr_wr(.ptr(ral.control), .value(32'hA000_00FF)); // rx_wm = 255
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_wm, 1'b0, "Max RX_WATERMARK=255 must keep RXWM=0 even when RXFULL=1")

    // Drain all 64 RX words cleanly
    for (int unsigned w = 0; w < SPI_HOST_RX_DEPTH; w++) begin
      ral.rxdata.read(status, 0, rdata);
      `DV_CHECK_EQ(status, UVM_IS_OK)
    end
    csr_rd(.ptr(ral.status), .value(st));
    `DV_CHECK_EQ(st.rx_qd,   8'd0)
    `DV_CHECK_EQ(st.rxempty, 1'b1)
    program_spi_host_regs();
  endtask : run_fifo_and_watermark_boundary_checks

  virtual task run_wrong_direction_window_error_checks();
    uvm_sequencer_base reg_seqr = ral.default_map.get_sequencer();
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         rdata;
    int unsigned       prev_tx_cnt, prev_rx_cnt;
    bit [31:0]         exp_rx_word = 32'hA55A_6996;
    bit [31:0]         exp_tx_word = 32'hDEAD_BEEF;

    `uvm_info(`gfn, "Running bus-level wrong-direction RXDATA write / TXDATA read SLVERR & preservation checks", UVM_LOW)
    spi_host_init();
    program_spi_host_regs();
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.error_enable), .value(32'h1F));

    // Stage 1 valid RX word in u_rx_fifo (via a 4B Bidir transfer) and 1 valid TX word in u_tx_fifo
    write_txdata(32'hCAFE_1234, 4'hf, status);
    wait_ready_for_command();
    cmd.direction = Bidir;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3;
    fork
      begin
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
      begin
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      end
    join
    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    // Pause SPIEN=0 and stage 1 fresh TX word (exp_tx_word) so both RXQD==1 and TXQD==1 during error probes
    csr_wr(.ptr(ral.control.spien), .value(1'b0));
    write_txdata(exp_tx_word, 4'hf, status);
    `DV_CHECK_EQ(status, UVM_IS_OK)
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd1));
    csr_rd_check(.ptr(ral.status.txqd), .compare_value(8'd1));
    csr_rd_check(.ptr(ral.error_status), .compare_value(32'h0));

    // Probe wrong-direction RXDATA write (0x24) and TXDATA read (0x28) with and without B/R backpressure
    for (int bp = 0; bp < 2; bp++) begin
      uvm_sequence_item rsp_base;
      axi_reg_op_item   win_op, win_rsp;
      axi_response_accept_item::s_force_backpressure = bit'(bp);
      axi_response_accept_item::s_forced_delay       = 4;

      // (a) Wrong-direction write to read-only RXDATA window (0x24) -> must return SLVERR
      win_op = axi_reg_op_item::type_id::create("rxdata_illegal_wr");
      win_op.m_rw.kind    = UVM_WRITE;
      win_op.m_rw.addr    = SPI_HOST_RXDATA_OFFSET;
      win_op.m_rw.data    = 32'hBAD0_BAD0;
      win_op.m_rw.n_bits  = 32;
      win_op.m_rw.byte_en = 4'hf;
      start_item(win_op, .sequencer(reg_seqr));
      finish_item(win_op);
      get_response(rsp_base);
      `downcast(win_rsp, rsp_base)
      `DV_CHECK_EQ(win_rsp.m_rw.status, UVM_NOT_OK,
                   $sformatf("Expected SLVERR on wrong-direction write to RXDATA (bp=%0d)", bp))

      // (b) Wrong-direction read from write-only TXDATA window (0x28) -> must return SLVERR
      win_op = axi_reg_op_item::type_id::create("txdata_illegal_rd");
      win_op.m_rw.kind    = UVM_READ;
      win_op.m_rw.addr    = SPI_HOST_TXDATA_OFFSET;
      win_op.m_rw.data    = 32'h0;
      win_op.m_rw.n_bits  = 32;
      win_op.m_rw.byte_en = 4'hf;
      start_item(win_op, .sequencer(reg_seqr));
      finish_item(win_op);
      get_response(rsp_base);
      `downcast(win_rsp, rsp_base)
      `DV_CHECK_EQ(win_rsp.m_rw.status, UVM_NOT_OK,
                   $sformatf("Expected SLVERR on wrong-direction read from TXDATA (bp=%0d)", bp))
    end
    axi_response_accept_item::s_force_backpressure = 1'b0;

    // Verify ERROR_STATUS remained 0 and both RXQD==1 and TXQD==1 were preserved intact
    csr_rd_check(.ptr(ral.error_status), .compare_value(32'h0));
    csr_rd_check(.ptr(ral.status.rxqd),  .compare_value(8'd1));
    csr_rd_check(.ptr(ral.status.txqd),  .compare_value(8'd1));

    // Verify preserved RXDATA word reads back intact and preserved TXDATA word transmits cleanly
    prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;
    ral.rxdata.read(status, 0, rdata);
    `DV_CHECK_EQ(status, UVM_IS_OK)
    `DV_CHECK_EQ(rdata, exp_rx_word, "Preserved RXDATA word corrupted by wrong-direction window access")
    csr_rd_check(.ptr(ral.status.rxqd), .compare_value(8'd0));

    csr_wr(.ptr(ral.control.spien), .value(1'b1));
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd3; // Transmit the preserved 4-byte exp_tx_word already in TX FIFO
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 1,
                 "Expected preserved TXDATA word to transmit cleanly and pass scoreboard TX check")
    `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                 "Expected preserved RXDATA word to pass scoreboard RX check")
  endtask : run_wrong_direction_window_error_checks

  virtual task run_reactive_device_driver_validation();
    spi_cmd_e          rd_opcs[3]   = '{ReadStd,  ReadDual, ReadQuad};
    spi_mode_e         rd_modes[3]  = '{Standard, Dual,     Quad};
    spi_host_command_t cmd;
    uvm_status_e       status;
    bit [31:0]         rdata;
    int unsigned       prev_tx_cnt, prev_rx_cnt;

    `uvm_info(`gfn, "Validating reactive SPI device responder across CS0/CS1 and Standard/Dual/Quad", UVM_LOW)
    spi_host_init();
    program_spi_host_regs();
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);
    cfg.en_reactive_device_rsp = 1'b1;

    fork
      start_agent_reactive_seqs();
    join_none

    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      csr_wr(.ptr(ral.csid), .value(cs));
      if (cs == 1) csr_wr(.ptr(ral.configopts_1), .value(32'h0222_0008));
      else         csr_wr(.ptr(ral.configopts),   .value(32'h0222_0008));

      foreach (rd_opcs[m_i]) begin
        prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
        prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;

        // Segment 1: 1-byte reactive command opcode (ReadStd=0xCC, ReadDual=0x3B, ReadQuad=0x0F)
        write_txdata({24'h0, rd_opcs[m_i]}, 4'b0001, status);
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b1;
        cmd.len       = 9'd0;
        program_command_reg(cmd);

        // Wait until first segment parks in IdleCSBActive so spi_device_cmd_rsp_seq queues response
        if (cfg.force_spi_fsm_vif != null) begin
          wait (cfg.force_spi_fsm_vif.fsm_state == 3'd7);
        end else begin
          cfg.clk_rst_vif.wait_clks(200);
        end

        // Segment 2: 4-byte RxOnly in target lane mode (Standard, Dual, or Quad)
        cmd.direction = RxOnly;
        cmd.mode      = rd_modes[m_i];
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd3;
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
        ral.rxdata.read(status, 0, rdata);
        `DV_CHECK_EQ(status, UVM_IS_OK)
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt + 2,
                     $sformatf("Reactive responder TX/segment check failed (CS%0d, %s)", cs, rd_modes[m_i].name()))
        `DV_CHECK_EQ(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt + 1,
                     $sformatf("Reactive responder RX lane-order check failed (CS%0d, %s)", cs, rd_modes[m_i].name()))
      end
    end

    cleanup_reactive_seq();
    cfg.en_reactive_device_rsp = 1'b0;
    cfg.m_spi_agent_cfg.spi_mode = Standard;
    cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    csr_wr(.ptr(ral.csid),         .value(32'h0));
    csr_wr(.ptr(ral.configopts),   .value(32'h0111_0002));
    csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0002));
  endtask : run_reactive_device_driver_validation

endclass : spi_host_closure_vseq
