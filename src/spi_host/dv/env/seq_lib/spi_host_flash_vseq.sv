// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Flash verification vseq:
//   Part 1: Exercises multi-segment mixed-lane host datapaths against the locally patched spiflash
//           BFM (synthetic Quad-address / 2-dummy-clock framing).
//   Part 2: Executes a strict datasheet-conforming Winbond W25Q01JV / W25Q128JV Rev B flow
//           (Sections 7.4.4, 7.4.6, 7.4.14, 7.4.21: 06h WREN, 05h RDSR1 WEL/BUSY polling,
//           31h/35h QE=1 setup, WEL=0 write-rejection enforcement, 1-lane 24-bit MSB-first
//           address for 02h Page Program & 6Bh Quad Output Fast Read, and 8 dummy clocks for 6Bh)
//           against a protocol-enforcing peripheral model across CS0 and CS1 (Comment #19).
class spi_host_flash_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_flash_vseq)
  `uvm_object_new

  localparam bit [7:0] WREN_OPC         = 8'h06;
  localparam bit [7:0] RDSR1_OPC        = 8'h05;
  localparam bit [7:0] RDSR2_OPC        = 8'h35;
  localparam bit [7:0] WRSR2_OPC        = 8'h31;
  localparam bit [7:0] READ_DATA_OPC    = 8'h03;
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
    super.pre_start();
  endtask : pre_start

  virtual task body();
    `uvm_info(`gfn, "Starting 'spi_host_flash_vseq'", UVM_LOW)

    spi_config_regs.cpol     = 1'b0;
    spi_config_regs.cpha     = 1'b0;
    spi_config_regs.clkdiv   = 16'd2;
    spi_config_regs.csnlead  = 4'd1;
    spi_config_regs.csntrail = 4'd1;
    spi_config_regs.csnidle  = 4'd1;
    spi_config_regs.fullcyc  = 1'b0;

    spi_host_ctrl_reg.tx_watermark = 0;
    spi_host_ctrl_reg.rx_watermark = 0;
    spi_host_ctrl_reg.csid         = 0;
    spi_host_ctrl_reg.sw_rst       = 0;

    apply_reset("HARD");
    spi_host_init();
    program_spi_host_regs();

    // Part 1: Synthetic mixed-lane multi-segment datapath flow against patched tb.sv spiflash BFM
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      target_csid = cs;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_addr,
        flash_addr < 32'h080000;
        flash_addr[7:0] == 8'h00;
      )
      `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
      run_synthetic_spiflash_mixed_lane_flow(target_csid);
    end

    // Part 2: Strict Winbond W25Q01JV Rev B datasheet-conforming flow across CS0 and CS1
    for (int cs = 0; cs < SPI_HOST_NUM_CS; cs++) begin
      run_winbond_w25q01jv_datasheet_flow(cs);
    end

    if (cfg.en_scb) begin
      `DV_CHECK_GT(cfg.scb_checked_tx_seg_cnt, 0, "Expected scoreboard to check TX segments")
      `DV_CHECK_GT(cfg.scb_checked_rx_seq_cnt, 0, "Expected scoreboard to check RX reads")
    end

    `uvm_info(`gfn, "Finished 'spi_host_flash_vseq' successfully", UVM_LOW)
  endtask : body

  // Part 1: Synthetic mixed-lane datapath test (Quad 3B address + 2 dummy clocks) matching patched spiflash
  virtual task run_synthetic_spiflash_mixed_lane_flow(bit [1:0] csid);
    spi_host_command_t cmd;
    uvm_status_e status;
    int num_words = 16;
    int num_bytes = (num_words * 4) - 1;

    `uvm_info(`gfn, $sformatf("[SYNTH-SPIFLASH CS%0d] Mixed-lane TX/RX %0dB @ 0x%08x",
                              csid, (num_words * 4), flash_addr), UVM_LOW)

    csr_wr(.ptr(ral.csid), .value(csid));

    ral.txdata.write(status, 0, {24'h0, PAGE_PROGRAM_OPC});
    ral.txdata.write(status, 0, flash_addr);
    for (int i = 0; i < num_words; i++) begin
      ral.txdata.write(status, 0, wr_data[i]);
    end

    // Segment 1: Opcode (Standard, 1B, CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'd0;
    program_command_reg(cmd);

    // Segment 2: Synthetic Quad-lane 3B Address (CSAAT=1)
    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Quad;
    cmd.direction = TxOnly;
    cmd.len       = 9'd2;
    program_command_reg(cmd);

    // Segment 3: Data (Standard, 64B, CSAAT=0)
    wait_ready_for_command();
    cmd.csaat     = 1'b0;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'(num_bytes);
    program_command_reg(cmd);

    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));
    cfg.clk_rst_vif.wait_clks(500);

    run_synthetic_spiflash_read_and_check(csid);
  endtask : run_synthetic_spiflash_mixed_lane_flow

  virtual task run_synthetic_spiflash_read_and_check(bit [1:0] csid);
    spi_host_command_t cmd;
    uvm_status_e status;
    bit [31:0] rx_word;
    int num_words = 16;
    int num_bytes = (num_words * 4) - 1;

    csr_wr(.ptr(ral.csid), .value(csid));

    ral.txdata.write(status, 0, {24'h0, QUAD_READ_OPC});
    ral.txdata.write(status, 0, flash_addr);

    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = TxOnly;
    cmd.len       = 9'd0;
    program_command_reg(cmd);

    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Quad;
    cmd.direction = TxOnly;
    cmd.len       = 9'd2;
    program_command_reg(cmd);

    wait_ready_for_command();
    cmd.csaat     = 1'b1;
    cmd.mode      = Standard;
    cmd.direction = None;
    cmd.len       = 9'd1;
    program_command_reg(cmd);

    wait_ready_for_command();
    cmd.csaat     = 1'b0;
    cmd.mode      = Quad;
    cmd.direction = RxOnly;
    cmd.len       = 9'(num_bytes);
    program_command_reg(cmd);

    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(100));

    for (int i = 0; i < num_words; i++) begin
      ral.rxdata.read(status, 0, rx_word);
      `DV_CHECK_EQ(rx_word, wr_data[i], $sformatf("Synthetic spiflash read mismatch at word %0d for CS%0d", i, csid))
    end
  endtask : run_synthetic_spiflash_read_and_check

  // Helper for strict W25Q01JV responder: sample 1 byte MSB-first on IO0 while enforcing 1-lane SD_EN
  virtual task w25q_sample_1lane_byte(input int cs_idx, output bit [7:0] rx_b, input string phase_name);
    rx_b = 8'h00;
    for (int b = 7; b >= 0; b--) begin
      @(posedge cfg.m_spi_agent_cfg.vif.sck);
      `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0001,
                   $sformatf("[W25Q01JV CS%0d %s] Expected single-lane Standard output enable (4'b0001)",
                             cs_idx, phase_name))
      rx_b[b] = bit'(cfg.m_spi_agent_cfg.vif.sio[0]);
    end
  endtask

  // Strict Winbond W25Q01JV Rev B peripheral responder enforcing:
  //   - 1-lane Standard opcodes & 24-bit MSB-first addresses for 02h, 03h, and 6Bh
  //   - WEL==1 requirement for 02h Page Program and 31h Write Status Register-2 (rejects if WEL==0)
  //   - BUSY==1 -> 0 transition on 05h RDSR1 after 02h Page Program
  //   - QE==1 requirement and exact 8 dummy clocks (sd_en==4'h0) for 6Bh Quad Output Fast Read
  virtual task run_w25q01jv_strict_responder(int cs_idx, ref bit stop_flag,
                                             ref int unsigned rejected_wel0_cnt);
    bit        wel_bit       = 1'b0;
    bit        busy_bit      = 1'b0;
    bit        qe_bit        = 1'b0;
    bit [7:0]  mem[bit [23:0]];
    rejected_wel0_cnt = 0;

    forever begin
      bit [7:0]  opc;
      bit [23:0] addr24;
      fork begin : wait_cs_or_stop
        fork
          @(negedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
          wait (stop_flag);
        join_any
        disable fork;
      end join
      if (stop_flag) break;

      cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      fork begin : frame_Responder
        fork
          begin
            @(posedge cfg.m_spi_agent_cfg.vif.csb[cs_idx]);
          end
          begin
            w25q_sample_1lane_byte(cs_idx, opc, "opcode");
            case (opc)
              WREN_OPC: begin
                wel_bit = 1'b1;
                wait (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b1);
              end
              RDSR1_OPC: begin
                bit [7:0] sr1 = {6'b0, wel_bit, busy_bit};
                for (int b = 7; b >= 0; b--) begin
                  @(negedge cfg.m_spi_agent_cfg.vif.sck);
                  cfg.m_spi_agent_cfg.vif.sio_out[1] <= sr1[b];
                end
                // Clear simulated program busy after first status poll observes BUSY==1
                if (busy_bit) busy_bit = 1'b0;
                wait (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b1);
              end
              RDSR2_OPC: begin
                bit [7:0] sr2 = {6'b0, qe_bit, 1'b0};
                for (int b = 7; b >= 0; b--) begin
                  @(negedge cfg.m_spi_agent_cfg.vif.sck);
                  cfg.m_spi_agent_cfg.vif.sio_out[1] <= sr2[b];
                end
                wait (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b1);
              end
              WRSR2_OPC: begin
                bit [7:0] sr2_in;
                w25q_sample_1lane_byte(cs_idx, sr2_in, "WRSR2_data");
                if (wel_bit) begin
                  qe_bit  = sr2_in[1];
                  wel_bit = 1'b0;
                end else begin
                  rejected_wel0_cnt++;
                end
                wait (cfg.m_spi_agent_cfg.vif.csb[cs_idx] === 1'b1);
              end
              PAGE_PROGRAM_OPC: begin
                bit [7:0] a2, a1, a0, dbyte;
                int unsigned off = 0;
                // W25Q01JV Sec 7.4.14: 24-bit MSB-first address on single lane IO0
                w25q_sample_1lane_byte(cs_idx, a2, "02h_addr[23:16]");
                w25q_sample_1lane_byte(cs_idx, a1, "02h_addr[15:8]");
                w25q_sample_1lane_byte(cs_idx, a0, "02h_addr[7:0]");
                addr24 = {a2, a1, a0};
                if (!wel_bit) begin
                  rejected_wel0_cnt++;
                end
                forever begin
                  w25q_sample_1lane_byte(cs_idx, dbyte, "02h_data");
                  if (wel_bit) begin
                    mem[{addr24[23:8], 8'(addr24[7:0] + off[7:0])}] = dbyte;
                  end
                  off++;
                end
              end
              READ_DATA_OPC: begin
                bit [7:0] a2, a1, a0;
                int unsigned off = 0;
                w25q_sample_1lane_byte(cs_idx, a2, "03h_addr[23:16]");
                w25q_sample_1lane_byte(cs_idx, a1, "03h_addr[15:8]");
                w25q_sample_1lane_byte(cs_idx, a0, "03h_addr[7:0]");
                addr24 = {a2, a1, a0};
                forever begin
                  bit [23:0] cur_a = addr24 + off;
                  bit [7:0]  rbyte = mem.exists(cur_a) ? mem[cur_a] : 8'hFF;
                  for (int b = 7; b >= 0; b--) begin
                    @(negedge cfg.m_spi_agent_cfg.vif.sck);
                    cfg.m_spi_agent_cfg.vif.sio_out[1] <= rbyte[b];
                  end
                  off++;
                end
              end
              QUAD_READ_OPC: begin
                bit [7:0] a2, a1, a0;
                int unsigned off = 0;
                // W25Q01JV Sec 7.4.21: 1-lane 24b MSB-first address + 8 dummy SCK clocks + 4-lane Quad data
                `DV_CHECK_EQ(qe_bit, 1'b1, "[W25Q01JV] 6Bh Quad Output Fast Read requires QE==1 in SR2")
                w25q_sample_1lane_byte(cs_idx, a2, "6Bh_addr[23:16]");
                w25q_sample_1lane_byte(cs_idx, a1, "6Bh_addr[15:8]");
                w25q_sample_1lane_byte(cs_idx, a0, "6Bh_addr[7:0]");
                addr24 = {a2, a1, a0};
                for (int d = 0; d < 8; d++) begin
                  @(posedge cfg.m_spi_agent_cfg.vif.sck);
                  `DV_CHECK_EQ(cfg.spi_passthrough_vif.cio_sd_en_o, 4'b0000,
                               $sformatf("[W25Q01JV] Expected SD_EN==0 during 6Bh dummy clock %0d", d))
                end
                forever begin
                  bit [23:0] cur_a = addr24 + off;
                  bit [7:0]  rbyte = mem.exists(cur_a) ? mem[cur_a] : 8'hFF;
                  @(negedge cfg.m_spi_agent_cfg.vif.sck);
                  cfg.m_spi_agent_cfg.vif.sio_out[3:0] <= rbyte[7:4];
                  @(negedge cfg.m_spi_agent_cfg.vif.sck);
                  cfg.m_spi_agent_cfg.vif.sio_out[3:0] <= rbyte[3:0];
                  off++;
                end
              end
              default: begin
                `uvm_error(`gfn, $sformatf("[W25Q01JV] Unsupported opcode 0x%02h on CS%0d", opc, cs_idx))
              end
            endcase
          end
        join_any
        disable fork;
      end join
      cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
      // Per W25Q01JV spec, 02h completion clears WEL and raises BUSY until programming finishes
      if (opc == PAGE_PROGRAM_OPC && wel_bit) begin
        wel_bit  = 1'b0;
        busy_bit = 1'b1;
      end
    end
  endtask

  virtual task issue_w25q_rdsr(int cs_idx, bit [7:0] opc, output bit [7:0] sr_val);
    spi_host_command_t cmd;
    uvm_status_e       st;
    bit [31:0]         rdata;
    csr_wr(.ptr(ral.csid), .value(cs_idx));
    write_txdata({24'h0, opc}, 4'b0001, st);
    wait_ready_for_command();
    cmd.direction = TxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b1;
    cmd.len       = 9'd0;
    program_command_reg(cmd);

    cmd.direction = RxOnly;
    cmd.mode      = Standard;
    cmd.csaat     = 1'b0;
    cmd.len       = 9'd0;
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    ral.rxdata.read(st, 0, rdata);
    sr_val = rdata[7:0];
  endtask

  virtual task run_winbond_w25q01jv_datasheet_flow(int cs_idx);
    spi_host_command_t cmd;
    uvm_status_e       st;
    bit [31:0]         rdata;
    bit [7:0]          sr_val;
    bit                stop_model = 1'b0;
    int unsigned       rejected_wel0_cnt = 0;
    bit [23:0]         target_addr = 24'h01_23_00 + (cs_idx << 8);
    // Little-Endian word packing {Addr[7:0], Addr[15:8], Addr[23:16], Opcode} transmits
    // Opcode first, followed by MSB-first 24-bit address Addr[23:16], Addr[15:8], Addr[7:0] on IO0!
    bit [31:0]         pp_hdr_le   = {target_addr[7:0], target_addr[15:8], target_addr[23:16], PAGE_PROGRAM_OPC};
    bit [31:0]         rd_hdr_le   = {target_addr[7:0], target_addr[15:8], target_addr[23:16], READ_DATA_OPC};
    bit [31:0]         qrd_hdr_le  = {target_addr[7:0], target_addr[15:8], target_addr[23:16], QUAD_READ_OPC};
    bit [31:0]         exp_payload[4] = '{
      32'hCAFE_F00D ^ cs_idx,
      32'h1234_5678 ^ cs_idx,
      32'hA55A_6996 ^ cs_idx,
      32'hDEAD_C0DE ^ cs_idx
    };
    int unsigned       prev_tx_cnt = cfg.scb_checked_tx_seg_cnt;
    int unsigned       prev_rx_cnt = cfg.scb_checked_rx_seq_cnt;

    `uvm_info(`gfn, $sformatf("[W25Q01JV-DATASHEET CS%0d] Running strict WREN/RDSR/QE/02h/6Bh flow", cs_idx), UVM_LOW)
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b0);
    csr_wr(.ptr(ral.csid), .value(cs_idx));
    if (cs_idx == 1) csr_wr(.ptr(ral.configopts_1), .value(32'h0111_0003));
    else             csr_wr(.ptr(ral.configopts),   .value(32'h0111_0003));

    fork
      run_w25q01jv_strict_responder(cs_idx, stop_model, rejected_wel0_cnt);
    join_none

    // 1. Negative control: attempt 02h Page Program BEFORE 06h WREN (WEL == 0) -> must be ignored
    ral.txdata.write(st, 0, pp_hdr_le);
    ral.txdata.write(st, 0, 32'hBAD0_BAD0);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b0, len: 9'd7}; // 4B hdr + 4B data, 1-lane
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    `DV_CHECK_EQ(rejected_wel0_cnt, 1, "Expected W25Q01JV responder to reject 02h Page Program when WEL==0")

    // Verify flash remained erased (0xFFFFFFFF) via 03h Read Data (1-lane opcode + 1-lane 24b addr + 1-lane data)
    ral.txdata.write(st, 0, rd_hdr_le);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b1, len: 9'd3};
    program_command_reg(cmd);
    cmd = '{mode: Standard, direction: RxOnly, csaat: 1'b0, len: 9'd3};
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active),  .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
    ral.rxdata.read(st, 0, rdata);
    `DV_CHECK_EQ(rdata, 32'hFFFF_FFFF, "Flash page must remain erased (0xFFFFFFFF) when 02h lacked WREN")

    // 2. Enable QE=1 in Status Register-2: 06h WREN -> 05h RDSR1 (WEL==1) -> 31h WRSR2 (0x02) -> 35h RDSR2 (QE==1)
    write_txdata({24'h0, WREN_OPC}, 4'b0001, st);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b0, len: 9'd0};
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    issue_w25q_rdsr(cs_idx, RDSR1_OPC, sr_val);
    `DV_CHECK_EQ(sr_val, 8'h02, "Expected RDSR1 WEL==1, BUSY==0 after 06h WREN")

    write_txdata({16'h0, 8'h02, WRSR2_OPC}, 4'b0011, st);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b0, len: 9'd1};
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    issue_w25q_rdsr(cs_idx, RDSR2_OPC, sr_val);
    `DV_CHECK_EQ(sr_val, 8'h02, "Expected RDSR2 QE==1 after 31h WRSR2")

    // 3. Datasheet 02h Page Program: 06h WREN -> 02h (1-lane opcode + 1-lane 24b MSB-first addr + 16B 1-lane data)
    write_txdata({24'h0, WREN_OPC}, 4'b0001, st);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b0, len: 9'd0};
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    ral.txdata.write(st, 0, pp_hdr_le);
    foreach (exp_payload[w]) ral.txdata.write(st, 0, exp_payload[w]);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b0, len: 9'd19}; // 4B hdr + 16B payload = 20B
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    // Poll 05h RDSR1: first poll sees BUSY==1 (0x01), second poll sees BUSY==0, WEL==0 (0x00)
    issue_w25q_rdsr(cs_idx, RDSR1_OPC, sr_val);
    `DV_CHECK_EQ(sr_val, 8'h01, "Expected RDSR1 BUSY==1, WEL==0 immediately after 02h Page Program")
    issue_w25q_rdsr(cs_idx, RDSR1_OPC, sr_val);
    `DV_CHECK_EQ(sr_val, 8'h00, "Expected RDSR1 BUSY==0, WEL==0 on completion")

    // 4. Datasheet 6Bh Quad Output Fast Read:
    //    Seg 1: 1-lane 6Bh opcode + 1-lane 24b MSB-first address (4 bytes Standard TxOnly, CSAAT=1)
    //    Seg 2: 8 dummy SCK clocks (Quad Direction=None, LEN=7 -> 8 tri-stated dummy clocks, CSAAT=1)
    //    Seg 3: 16-byte Quad RxOnly payload (Quad RxOnly, LEN=15, CSAAT=0)
    ral.txdata.write(st, 0, qrd_hdr_le);
    wait_ready_for_command();
    cmd = '{mode: Standard, direction: TxOnly, csaat: 1'b1, len: 9'd3};
    program_command_reg(cmd);

    cmd = '{mode: Quad, direction: None, csaat: 1'b1, len: 9'd7}; // Exact 8 tri-stated dummy SCK clocks
    program_command_reg(cmd);

    cmd = '{mode: Quad, direction: RxOnly, csaat: 1'b0, len: 9'd15}; // 16 bytes Quad data
    program_command_reg(cmd);
    csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));

    foreach (exp_payload[w]) begin
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0), .backdoor(1'b0), .spinwait_delay_ns(50));
      ral.rxdata.read(st, 0, rdata);
      `DV_CHECK_EQ(rdata, exp_payload[w],
                   $sformatf("[W25Q01JV CS%0d] 6Bh Quad Output Fast Read mismatch at word %0d", cs_idx, w))
    end

    stop_model = 1'b1;
    cfg.clk_rst_vif.wait_clks(10);
    cfg.m_spi_agent_cfg.vif.sio_out <= 4'bzzzz;
    cfg.m_spi_agent_cfg.vif.set_flash_model_en(1'b1);
    if (cfg.en_scb) begin
      `DV_CHECK_GT(cfg.scb_checked_tx_seg_cnt, prev_tx_cnt)
      `DV_CHECK_GT(cfg.scb_checked_rx_seq_cnt, prev_rx_cnt)
    end
  endtask : run_winbond_w25q01jv_datasheet_flow

endclass : spi_host_flash_vseq
