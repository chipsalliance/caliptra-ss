// Copyright lowRISC contributors (OpenTitan project).
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
  endtask : run_flash_page_program_and_read

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

    // Clean up with reset
    spi_host_init();
    `uvm_info(`gfn, "Completed targeted functional coverage stimulus", UVM_LOW)
  endtask : run_functional_coverage_stimulus

endclass : spi_host_smoke_vseq
