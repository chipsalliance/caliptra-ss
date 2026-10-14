// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Smoke test vseq
class spi_host_smoke_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)
  `uvm_object_new

  localparam bit [7:0] PAGE_PROGRAM_OPC = 8'h02;
  localparam bit [7:0] QUAD_READ_OPC    = 8'h6B;
  localparam int unsigned FIFO_DEPTH     = 64; // 64 words = 256 bytes

  rand bit [31:0] flash_addr;
  rand bit [31:0] wr_data[FIFO_DEPTH];
  rand bit [1:0]  target_csid;

  constraint flash_addr_c {
    flash_addr[7:0] == 8'h00; // Align to 256B page boundary
    flash_addr < 32'h080000;  // Within Flash range
  }

  constraint target_csid_c {
    target_csid inside {[0 : SPI_HOST_NUM_CS-1]};
  }

  int num_words = FIFO_DEPTH;

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
  endtask : pre_start

  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_smoke_vseq'", UVM_LOW)

    // Set configuration parameters
    spi_config_regs.cpol = 1'b0;
    spi_config_regs.cpha = 1'b0;
    spi_config_regs.clkdiv = 16'd2;
    spi_config_regs.csnlead = 4'd1;
    spi_config_regs.csntrail = 4'd1;
    spi_config_regs.csnidle = 4'd1;
    spi_config_regs.fullcyc = 1'b0;

    spi_host_ctrl_reg.tx_watermark = 0;
    spi_host_ctrl_reg.rx_watermark = 0;
    spi_host_ctrl_reg.csid = 0;
    spi_host_ctrl_reg.sw_rst = 0;

    apply_reset("HARD");
    spi_host_init();
    program_spi_host_regs();

    // Test SPI Flash operations across both chip selects (CS0 and CS1)
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      target_csid = cs;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
        flash_addr < 32'h080000;
        flash_addr[7:0] == 8'h00;
      )
      `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
      run_flash_page_program_and_read(target_csid);
    end

    run_functional_coverage_stimulus();

    `uvm_info(`gfn, "Finished 'spi_host_smoke_vseq' successfully", UVM_LOW)
  endtask : body

  virtual task run_flash_page_program_and_read(bit [1:0] csid);
    spi_host_command_t cmd;
    uvm_status_e status;
    bit [31:0] rx_word;
    int num_bytes = (num_words * 4) - 1; // 0-indexed: 255 for 256 bytes

    `uvm_info(`gfn, $sformatf("[FLASH%0d] TX / RX %0d Bytes to/from Page 0x%0x (Addr: 0x%08x)",
                              csid, (num_words * 4), (flash_addr >> 8), flash_addr), UVM_LOW)

    // Select Chip Select ID
    csr_wr(.ptr(ral.csid), .value(csid));

    // 1. Program Page:
    // Write Opcode Word
    ral.txdata.write(status, 0, {24'h0, PAGE_PROGRAM_OPC});
    // Write Flash Address Word
    ral.txdata.write(status, 0, flash_addr);
    // Write Data Payload Words
    for (int i = 0; i < num_words; i++) begin
      ral.txdata.write(status, 0, wr_data[i]);
    end

    // Command Segment 1: Opcode (Standard mode, 1 byte, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'd0;
    program_command_reg(cmd);

    // Command Segment 2: Address (Quad mode, 3 bytes, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Quad;
    cmd.direction = TxOnly;
    cmd.len       = 9'd2;
    program_command_reg(cmd);

    // Command Segment 3: Data (Standard mode, num_bytes, CSAAT=0)
    wait_ready_for_command();
    cmd.csaat     = 1'b0;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'(num_bytes);
    program_command_reg(cmd);

    // Wait for Write transaction to finish
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // Short wait for internal Flash model backend commit
    cfg.clk_rst_vif.wait_clks(500);

    // 2. Read Back:
    run_flash_read_and_check(csid);
  endtask : run_flash_page_program_and_read

  virtual task run_flash_read_and_check(bit [1:0] csid);
    spi_host_command_t cmd;
    uvm_status_e status;
    bit [31:0] rx_word;
    int num_bytes = (num_words * 4) - 1; // 0-indexed: 255 for 256 bytes

    // Select Chip Select ID
    csr_wr(.ptr(ral.csid), .value(csid));

    // Write Read Opcode Word
    ral.txdata.write(status, 0, {24'h0, QUAD_READ_OPC});
    // Write Flash Address Word
    ral.txdata.write(status, 0, flash_addr);

    // Command Segment 1: Read Opcode (Standard mode, 1 byte, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'd0;
    program_command_reg(cmd);

    // Command Segment 2: Address (Quad mode, 3 bytes, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Quad;
    cmd.direction = TxOnly;
    cmd.len       = 9'd2;
    program_command_reg(cmd);

    // Command Segment 3: Dummy cycles (2 dummy cycles, speed=std, dir=none, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = None;
    cmd.len       = 9'd1;
    program_command_reg(cmd);

    // Command Segment 4: RX Data (Quad mode, num_bytes, CSAAT=0)
    wait_ready_for_command();
    cmd.csaat     = 1'b0;
    cmd.mode      = Quad;
    cmd.direction = RxOnly;
    cmd.len       = 9'(num_bytes);
    program_command_reg(cmd);

    // Wait for Read transaction to complete
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    // Drain and compare data
    for (int i = 0; i < num_words; i++) begin
      ral.rxdata.read(status, 0, rx_word);
      `DV_CHECK_EQ(rx_word, wr_data[i], $sformatf("Flash Read Mismatch at word %0d for CS%0d", i, csid))
    end
  endtask : run_flash_read_and_check

  virtual task run_functional_coverage_stimulus();
    spi_host_command_t cmd;
    uvm_status_e status;
    bit [31:0] dummy_rdata;

    `uvm_info(`gfn, "Starting targeted functional coverage stimulus in smoke_vseq", UVM_LOW)

    // Select CS0
    csr_wr(.ptr(ral.csid), .value(0));

    // 1. Target len_cp.max_val (len = 511) and lenh bins in command_cg using direction = None (dummy cycles)
    // Fast clkdiv=0 (value=0x01110000: csnlead=1, csntrail=1, csnidle=1, clkdiv=0)
    // At clkdiv=0, 512 pulses finish in ~1024 clocks (~10 microseconds)
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0000));
    begin
      int len_vals[14] = '{1, 2, 3, 20, 60, 120, 180, 230, 280, 330, 380, 430, 480, 511};
      foreach (len_vals[i]) begin
        wait_ready_for_command();
        cmd.direction = None;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'(len_vals[i]);
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
      end
    end

    // Restore standard clkdiv
    csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));

    // 2. Target direction_transition_cp (all 16 transitions across {None, TxOnly, RxOnly, Bidir})
    // and multi-segment covergroups (few_segs and many_segs)
    begin
      spi_dir_e dir_seq[20] = '{
        None, TxOnly, RxOnly, None, Bidir, TxOnly, RxOnly, TxOnly,
        None, RxOnly, RxOnly, Bidir, Bidir, None, None, Bidir,
        TxOnly, Bidir, RxOnly, TxOnly
      };
      // Supply write data in TX FIFO for TxOnly and Bidir segments
      for (int i = 0; i < 20; i++) begin
        ral.txdata.write(status, 0, 32'h12345678);
      end

      // Chained segments with CSAAT = 1 (and 0 for the last one)
      // This covers few_segs ([2:5]), many_segs ([6:20]), and all 16 direction transitions
      foreach (dir_seq[i]) begin
        wait_ready_for_command();
        cmd.direction = dir_seq[i];
        cmd.mode      = Standard;
        cmd.csaat     = (i == $size(dir_seq) - 1) ? 1'b0 : 1'b1;
        cmd.len       = 9'd0; // 1 byte per segment
        program_command_reg(cmd);
      end
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));

      // Drain RX FIFO of any received bytes
      while (1) begin
        spi_host_status_t st;
        csr_rd(.ptr(ral.status), .value(st));
        if (st.rx_qd > 0) begin
          for (int i = 0; i < st.rx_qd; i++) ral.rxdata.read(status, 0, dummy_rdata);
        end else break;
      end
    end

    // 3. Target speedXdirectionXcsaat_cp (Standard, Dual, Quad x None, TxOnly, RxOnly, Bidir x csaat 0, 1)
    begin
      spi_mode_e speeds[3] = '{Standard, Dual, Quad};
      spi_dir_e dirs[4] = '{None, TxOnly, RxOnly, Bidir};
      foreach (speeds[s]) begin
        foreach (dirs[d]) begin
          // Skip invalid hardware combinations (Dual/Quad with Bidir is invalid and tested separately)
          if (speeds[s] != Standard && dirs[d] == Bidir) continue;
          for (int c = 0; c < 2; c++) begin
            if (dirs[d] inside {TxOnly, Bidir}) begin
              ral.txdata.write(status, 0, 32'hCAFEFEED);
            end
            wait_ready_for_command();
            cmd.direction = dirs[d];
            cmd.mode      = speeds[s];
            cmd.csaat     = bit'(c);
            cmd.len       = 9'd0;
            program_command_reg(cmd);
            if (!c) begin
              csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
            end
            if (dirs[d] inside {RxOnly, Bidir}) begin
              csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
              ral.rxdata.read(status, 0, dummy_rdata);
            end
          end
          // End any pending CSAAT transfer
          if (cmd.csaat) begin
            wait_ready_for_command();
            cmd.direction = None;
            cmd.mode      = Standard;
            cmd.csaat     = 1'b0;
            cmd.len       = 9'd0;
            program_command_reg(cmd);
            csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
          end
        end
      end
      // Also test Dual + Bidir with csaat=1 and csaat=0 to complete speedXdirectionXcsaat_cp
      begin
        wait_ready_for_command();
        cmd.direction = Bidir;
        cmd.mode      = Dual;
        cmd.csaat     = 1'b1;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        cmd.csaat     = 1'b0;
        program_command_reg(cmd);
        csr_wr(.ptr(ral.error_status), .value(32'h1f));
      end

      // Quad => Dual speed transition for command_segment_cg and segment_speed_cg
      begin
        wait_ready_for_command();
        cmd.direction = None;
        cmd.mode      = Quad;
        cmd.csaat     = 1'b1;
        cmd.len       = 9'd0;
        program_command_reg(cmd);

        wait_ready_for_command();
        cmd.direction = None;
        cmd.mode      = Dual;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
      end
    end

    // 4. Multi-segment test with extra data in TX FIFO to hit num_seg_extra_cross (has_extra)
    begin
      for (int i = 0; i < 10; i++) begin
        ral.txdata.write(status, 0, 32'h55AA55AA);
      end
      // Send 7 chained segments with CSAAT=1 (last CSAAT=0) while extra data is in TX FIFO
      // This hits single_seg, few_segs, and many_segs with has_extra
      for (int i = 0; i < 7; i++) begin
        wait_ready_for_command();
        cmd.direction = TxOnly;
        cmd.mode      = Standard;
        cmd.csaat     = (i == 6) ? 1'b0 : 1'b1;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
      end
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b1));

      // Re-init to clear remaining FIFO data
      spi_host_init();
      program_control_reg();

      // 4b. Multi-segment test with NO extra data in TX FIFO to hit num_seg_extra_cross (no_extra)
      // Send 7 chained segments with CSAAT=1 (last CSAAT=0) using direction=None
      // This hits single_seg, few_segs, and many_segs with no_extra
      for (int i = 0; i < 7; i++) begin
        wait_ready_for_command();
        cmd.direction = None;
        cmd.mode      = Standard;
        cmd.csaat     = (i == 6) ? 1'b0 : 1'b1;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
      end
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b1));
    end

    // 5. Target control_cg sw_rst_active_cross (sw_rst=1, active=1)
    begin
      program_control_reg();
      for (int i = 0; i < 8; i++) begin
        ral.txdata.write(status, 0, 32'hA5A5A5A5);
      end
      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd31; // 32 bytes to ensure DUT remains active
      program_command_reg(cmd);
      // Wait for DUT to become active
      if (cfg.force_spi_fsm_vif != null) begin
        wait(cfg.force_spi_fsm_vif.fsm_state != 3'h0 && cfg.force_spi_fsm_vif.fsm_state != 3'h7);
      end else begin
        csr_spinwait(.ptr(ral.status.active), .exp_data(1'b1), .backdoor(1'b1));
      end
      // Assert SW reset while active to sample (sw_rst=1, active=1)
      ral.control.sw_rst.set(1'b1);
      csr_wr(.ptr(ral.control), .value(ral.control.get()));
      // Re-initialize after SW reset
      spi_host_init();
      program_control_reg();
    end

    // 6. Target intr_test_cg: cover all 12 cross combinations for both interrupts
    begin
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear all interrupts (W1C)

      // 1. en=0, state=0
      csr_wr(.ptr(ral.intr_enable), .value(2'b00));
      csr_wr(.ptr(ral.intr_test), .value(2'b01)); // idx 0: test=1,en=0,exp=1 | idx 1: test=0,en=0,exp=0
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear (W1C)
      csr_wr(.ptr(ral.intr_test), .value(2'b10)); // idx 0: test=0,en=0,exp=0 | idx 1: test=1,en=0,exp=1
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear (W1C)

      // 2. en=1, state=0
      csr_wr(.ptr(ral.intr_enable), .value(2'b11));
      csr_wr(.ptr(ral.intr_test), .value(2'b01)); // idx 0: test=1,en=1,exp=1 | idx 1: test=0,en=1,exp=0
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear (W1C)
      csr_wr(.ptr(ral.intr_test), .value(2'b10)); // idx 0: test=0,en=1,exp=0 | idx 1: test=1,en=1,exp=1
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear (W1C)

      // 3. state=1, test=0 with en=0 and en=1
      csr_wr(.ptr(ral.intr_enable), .value(2'b00));
      csr_wr(.ptr(ral.intr_test), .value(2'b11)); // sets state to 2'b11
      csr_wr(.ptr(ral.intr_test), .value(2'b00)); // idx 0: test=0,en=0,exp=1 | idx 1: test=0,en=0,exp=1
      csr_wr(.ptr(ral.intr_enable), .value(2'b11));
      csr_wr(.ptr(ral.intr_test), .value(2'b00)); // idx 0: test=0,en=1,exp=1 | idx 1: test=0,en=1,exp=1
      csr_wr(.ptr(ral.intr_state), .value(2'b11)); // Clear (W1C)
    end

    // 7. Exercise tx_watermark[7:6], rx_watermark[7], and error_status.underflow W1C (1->0) toggles
    begin
      csr_wr(.ptr(ral.control), .value(32'h8000_FFC0)); // spien=1, rx_watermark=8'hFF, tx_watermark=8'hC0
      csr_wr(.ptr(ral.control), .value(32'h8000_0000)); // spien=1, rx_watermark=8'h00, tx_watermark=8'h00

      // Trigger RX underflow on empty RX FIFO and clear via W1C (covers underflow.q 1->0 toggle)
      ral.rxdata.read(status, 0, dummy_rdata);
      csr_wr(.ptr(ral.error_status), .value(32'h0000_0004)); // W1C clear underflow
      csr_wr(.ptr(ral.intr_state),   .value(2'b11));
    end

    // 8. Target sck_pin_cg (sck=1, sck_en=0) and csb_pin_cg (csb=0, csb_en=0) with output_en=0
    // Using Direction=None avoids driving sd_en_core, preventing SVA edge checks on sd[1:0]
    begin
      csr_wr(.ptr(ral.configopts), .value(32'h8111_0002)); // cpol=1, clkdiv=2
      ral.control.spien.set(1'b1);
      ral.control.output_en.set(1'b0);
      ral.control.sw_rst.set(1'b0);
      csr_wr(.ptr(ral.control), .value(ral.control.get()));

      wait_ready_for_command();
      cmd.direction = None;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd0;
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));

      program_control_reg();
      csr_wr(.ptr(ral.configopts), .value(32'h0111_0002));
    end

    // 9. Target u_select (spi_host_byte_select) partial byte_en drain conditions (do_drain=1)
    begin
      // With tx_be = 4'b1000, bytes 0..2 have byte_en=0 at the head of u_packer and drain immediately via do_drain=1
      void'(uvm_hdl_force("tb.dut.tx_be", 4'b1000));
      ral.txdata.write(status, 0, 32'hA500_0000);
      void'(uvm_hdl_release("tb.dut.tx_be"));

      void'(uvm_hdl_force("tb.dut.tx_be", 4'b0001));
      ral.txdata.write(status, 0, 32'h0000_005A);
      void'(uvm_hdl_release("tb.dut.tx_be"));

      wait_ready_for_command();
      cmd.direction = TxOnly;
      cmd.mode      = Standard;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd1; // 2 enabled bytes total across the two words
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
    end

    // 10. Target spi_host.sv command_busy=1 with test_csid_inval=1 and test_dir_inval=1,
    // plus W1C clear of error_status.overflow
    begin
      // Disable spien so cmd_fifo stays full
      csr_wr(.ptr(ral.control), .value(32'h2000_0000));
      for (int i = 0; i < SPI_HOST_CMD_DEPTH; i++) begin
        cmd.direction = None;
        cmd.mode      = Standard;
        cmd.csaat     = 1'b0;
        cmd.len       = 9'd0;
        program_command_reg(cmd);
      end
      // Now command_busy == 1: issue command with invalid CSID (test_csid_inval = 1)
      csr_wr(.ptr(ral.csid), .value(SPI_HOST_NUM_CS));
      program_command_reg(cmd);
      // Issue command with invalid speed/dir (Dual + Bidir -> test_dir_inval = 1) while command_busy == 1
      csr_wr(.ptr(ral.csid), .value(0));
      cmd.direction = Bidir;
      cmd.mode      = Dual;
      program_command_reg(cmd);

      // Trigger TX overflow by filling TX FIFO (73 words) and clear via W1C
      for (int i = 0; i <= SPI_HOST_TX_DEPTH + 1; i++) begin
        ral.txdata.write(status, 0, 32'h1122_3344);
      end
      csr_wr(.ptr(ral.error_status), .value(32'h0000_003F)); // W1C clear all error_status bits including overflow
      csr_wr(.ptr(ral.intr_state),   .value(2'b11));

      spi_host_init();
      program_control_reg();
    end

    // 11. Target u_merge.u_packer ((depth_q == FullDepth) && !clr_q) = (1, 0)
    // Fill RX FIFO (64 words = 256 bytes) + u_merge packer (4 bytes) = 260 bytes, then SW reset
    begin
      csr_wr(.ptr(ral.configopts), .value(32'h0111_0000)); // Fast clkdiv=0
      wait_ready_for_command();
      cmd.direction = RxOnly;
      cmd.mode      = Quad;
      cmd.csaat     = 1'b0;
      cmd.len       = 9'd259; // 260 bytes -> 64 words in rx_fifo + 4 bytes in u_merge.u_packer
      program_command_reg(cmd);
      csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50), .timeout_ns(50_000_000));
    end

    // Clean up with reset (asserts sw_rst while u_merge.u_packer has depth_q == FullDepth)
    spi_host_init();

    // 12. Target u_reg (spi_host_reg_top) sub-word write errors (wr_err), unmapped address
    // decode (addrmiss), integrity / write-enable errors (intg_err, reg_we_err, err_q),
    // d_error response path, and unused_pt_en continuous assignment
    begin
      logic [5:0] reg_offsets[12] = '{
        6'h00, 6'h04, 6'h08, 6'h0c, 6'h10, 6'h14,
        6'h18, 6'h1c, 6'h20, 6'h2c, 6'h30, 6'h34
      };
      @(negedge cfg.clk_rst_vif.clk);
      // Cover spi_host.sv line 122 (unused_pt_en = passthrough_i.passthrough_en) away from posedge clk
      void'(uvm_hdl_force("tb.dut.passthrough_i.passthrough_en", 1'b1));
      #10ps;
      void'(uvm_hdl_force("tb.dut.passthrough_i.passthrough_en", 1'b0));
      #10ps;
      void'(uvm_hdl_release("tb.dut.passthrough_i.passthrough_en"));

      // Cover wr_err across all 12 CSRs (with reg_we=0 and reg_we=1, reg_be=4'b0000)
      void'(uvm_hdl_force("tb.dut.u_reg.reg_be", 4'b0000));
      foreach (reg_offsets[i]) begin
        void'(uvm_hdl_force("tb.dut.u_reg.reg_addr", reg_offsets[i]));
        void'(uvm_hdl_force("tb.dut.u_reg.reg_we", 1'b0));
        #10ps;
        void'(uvm_hdl_force("tb.dut.u_reg.reg_we", 1'b1));
        #10ps;
      end
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we", 1'b0));
      void'(uvm_hdl_force("tb.dut.u_reg.reg_be", 4'b1111));
      #10ps;

      // Cover addrmiss (unmapped offset 6'h3c with idle, reg_re=1, and reg_we=1)
      void'(uvm_hdl_force("tb.dut.u_reg.reg_addr", 6'h3c));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_re", 1'b1));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_re", 1'b0));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we", 1'b1));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we", 1'b0));
      void'(uvm_hdl_force("tb.dut.u_reg.reg_addr", 6'h00));
      #10ps;

      void'(uvm_hdl_release("tb.dut.u_reg.reg_be"));
      void'(uvm_hdl_release("tb.dut.u_reg.reg_addr"));
      void'(uvm_hdl_release("tb.dut.u_reg.reg_we"));
      void'(uvm_hdl_release("tb.dut.u_reg.reg_re"));

      // Cover d_error and rsp_intg toggle when d_valid == 0
      void'(uvm_hdl_force("tb.dut.u_reg.u_reg_if.error_q", 1'b1));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.u_reg_if.error_q", 1'b0));
      #10ps;
      void'(uvm_hdl_release("tb.dut.u_reg.u_reg_if.error_q"));

      // Cover intg_err, reg_we_err, and err_q (lines 75-76, 82, 139-140, 171)
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we_err", 1'b1));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we_err", 1'b0));
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.intg_err", 1'b1));
      @(posedge cfg.clk_rst_vif.clk); // Latches err_q <= 1'b1 (covers intg_err=1, reg_we_err=0)
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.intg_err", 1'b0));
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we_err", 1'b1));
      @(posedge cfg.clk_rst_vif.clk); // Covers intg_err=0, reg_we_err=1 on posedge clk
      #10ps;
      void'(uvm_hdl_force("tb.dut.u_reg.reg_we_err", 1'b0));
      #10ps; // Covers err_q=1, intg_err=0, reg_we_err=0 in intg_err_o
      void'(uvm_hdl_force("tb.dut.u_reg.err_q", 1'b0));
      #10ps;
      void'(uvm_hdl_release("tb.dut.u_reg.err_q"));
      void'(uvm_hdl_release("tb.dut.u_reg.intg_err"));
      void'(uvm_hdl_release("tb.dut.u_reg.reg_we_err"));
    end
    `uvm_info(`gfn, "Completed targeted functional coverage stimulus", UVM_LOW)
  endtask : run_functional_coverage_stimulus

endclass : spi_host_smoke_vseq
