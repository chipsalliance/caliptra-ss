// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash verification vseq targeting the integrated spiflash behavioral model
class spi_host_flash_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_flash_vseq)
  `uvm_object_new

  localparam bit [7:0] PAGE_PROGRAM_OPC = 8'h02;
  localparam bit [7:0] QUAD_READ_OPC    = 8'h6B;

  rand bit [31:0] flash_addr;
  rand bit [31:0] wr_data[16];
  rand bit [1:0]  target_csid;

  constraint flash_addr_c {
    flash_addr[7:0] == 8'h00; // Align to 256B page boundary
    flash_addr < 32'h080000;  // Within 512KB Flash range (safely below 1MB)
  }

  constraint target_csid_c {
    target_csid inside {[0 : SPI_HOST_NUM_CS-1]};
  }

  virtual task pre_start();
    cfg.en_scb = 0;
    super.pre_start();
  endtask : pre_start

  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_flash_vseq'", UVM_LOW)

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

    // Test SPI Flash operations
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      target_csid = cs;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
        flash_addr < 32'h080000;
        flash_addr[7:0] == 8'h00;
      )
      `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
      run_flash_page_program_and_read(target_csid);
    end

    `uvm_info(`gfn, "Finished 'spi_host_flash_vseq' successfully", UVM_LOW)
  endtask : body

  virtual task run_flash_page_program_and_read(bit [1:0] csid);
    spi_host_command_t cmd;
    uvm_status_e status;
    bit [31:0] rx_word;
    int num_words = 16;
    int num_bytes = (num_words * 4) - 1; // 0-indexed byte count for length field: 63 for 64 bytes

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

endclass : spi_host_flash_vseq
