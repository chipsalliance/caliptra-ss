// Copyright 2026 Google LLC(OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//==================================================
// Caliptra-SS SPI Host VCS Coverage Exclusion File (.el)
// Format Version: 2
// ExclMode: default
//
// Categories explicitly distinguished below (Comments #6, #7, #22, #24):
//   [DESIGN-UNR]  Structurally unreachable RTL expressions/transitions across all parameterizations.
//   [TARGET-CFG]  Parameterized target restrictions of spi_host_axi (NumCS=2, AxiIw=1, AxiDw=32,
//                 ByteOrder=1, TxDepth=72, RxDepth=64).
//
// Additional documented structural UNR notes in spi_host_axi wrapper (unwaived in raw score):
//   - spi_host.sv:122 (`assign unused_pt_en = passthrough_i.passthrough_en;` in gen_passthrough_ignore):
//     [TARGET-CFG] For NumCS=2, PassthroughNumCSCompat_A requires !passthrough_i.passthrough_en on
//     every active clock edge; sub-cycle coverage pulses were removed per Comment #22.
//   - sub2tlul.sv:91,94 (cur_txn direct valid_get_txn <-> valid_put_txn FSM transitions):
//     [DESIGN-UNR] pending_txn gates tl_o.a_valid (`dv & ~pending_txn`), forcing cur_txn back to
//     no_txn upon AccessAck/AccessAckData before a new request can assert tl_o.a_valid.
//   - axi_addr.v:180 (`2'b11` 8-byte beat alignment arm):
//     [TARGET-CFG] spi_host_axi fixes AxiDw=32 (DSZ=2, max legal AXI4 AxSIZE=3'b010 = 4 bytes).
//==================================================

//==================================================
// 1. SPI HOST CORE TOP (tb.dut.u_caliptra_ss_spi_host : caliptra_ss_spi_host)
//==================================================
// [DESIGN-UNR] In spi_host.sv:154-166, test_speed_inval is only set to 1 in the default
// case branch where test_dir_inval is also set to 1, so (test_speed_inval=1, test_dir_inval=0)
// is structurally unreachable.
CHECKSUM: "2960936678 1977424990"
INSTANCE: tb.dut.u_caliptra_ss_spi_host
ANNOTATION: "[DESIGN-UNR] test_speed_inval=1 always implies test_dir_inval=1 in spi_host.sv:164-165"
Condition 5 "2312135264" "(test_speed_inval | test_dir_inval) 1 -1" (3 "10")

// [TARGET-CFG] NumCS = 2 target-configuration exclusion (Comment #22):
// PassthroughNumCSCompat_A requires passthrough_i.passthrough_en == 1'b0 when NumCS > 1.
INSTANCE: tb.dut.u_caliptra_ss_spi_host
ANNOTATION: "[TARGET-CFG] NumCS=2 structurally disables passthrough_en per PassthroughNumCSCompat_A"
Toggle passthrough_i.passthrough_en "logic passthrough_i.passthrough_en"

// [TARGET-CFG / DESIGN-UNR] Structural constants driven by production u_axi2tlul_spi_host (sub2tlul.sv)
// and TL-UL device responses on spi_host_axi (AxiIw=1):
//   - sub2tlul.sv:70,155 ties instr_type to MuBi4False (4'b1001) and upper a_user rsvd bits to 3'b0.
//   - sub2tlul.sv:123 zero-extends 1-bit AXI ID (AxiIw=1) into 8-bit tl_a_source / tl_d_source [7:1].
//   - sub2tlul.sv:116,137 fixes a_param=3'h0 and encodes only PutFullData(0)/PutPartialData(1)/Get(4)
//     so a_opcode[1] is structurally 1'b0 (while a_opcode[0] and a_size[1:0] DO toggle dynamically).
//   - TL-UL device responses use only AccessAck(0)/AccessAckData(1) with d_param=0, d_sink=0.
INSTANCE: tb.dut.u_caliptra_ss_spi_host
ANNOTATION: "[TARGET-CFG] Production sub2tlul / TL-UL protocol constants for spi_host_axi (AxiIw=1)"
Toggle tl_i.a_user.instr_type "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_source [7:1] "logic tl_i.a_source[7:0]"
Toggle tl_i.a_param "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_source [7:1] "logic tl_o.d_source[7:0]"
Toggle tl_o.d_param "logic tl_o.d_param[2:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"

//==================================================
// 2. SHIFT REGISTER (tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_shift_reg)
//==================================================
// [DESIGN-UNR] u_fsm gates rd_en_o with sr_rd_ready_i and wr_en_o with sr_wr_ready_i,
// so (rd_en_i=1, rd_ready_o=0) and (wr_en_i=1, wr_ready_o=0) are structurally unreachable.
// Note: speed_i == RsvdSpd (2'b11) waivers are intentionally NOT claimed unconditionally here
// pending designer confirmation on W1C-only recovery (Comments #2, #3, #7).
CHECKSUM: "3611448077 2976194449"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_shift_reg
ANNOTATION: "[DESIGN-UNR] u_fsm gates rd_en/wr_en with sr_rd_ready_i/sr_wr_ready_i"
Condition 18 "864104756" "(rd_en_i && rd_ready_o) 1 -1" (2 "10")
Condition 21 "1964525666" "(rd_en_i && rd_ready_o) 1 -1" (2 "10")
Condition 28 "1682065670" "(wr_en_i & wr_ready_o) 1 -1" (2 "10")

//==================================================
// 3. SPI HOST FSM (tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_fsm)
//==================================================
// [DESIGN-UNR] Unreachable condition rows due to FSM invariant relationships:
// - Condition 74: shift_en_internal requires bit_cntr_q != 0 while stall requires bit_cntr_q == 0.
// - Conditions 100, 106, 112, 115: sw_rst_i == 1 forces state_d == Idle, so ~sw_rst_i == 0
//   cannot co-occur with state_d == WaitLead / InternalClkLow / InternalClkHigh.
// - Conditions 149, 151: rd_en_o / wr_en_o are already gated by ~stall (sr_rd_ready_i / sr_wr_ready_i).
CHECKSUM: "1990714023 2778135185"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_fsm
ANNOTATION: "[DESIGN-UNR] Mutually exclusive FSM state/stall/handshake condition terms"
Condition 74 "1393146906" "(shift_en_internal & ((~stall))) 1 -1" (2 "10")
Condition 100 "2255307332" "(((~sw_rst_i)) & state_changing & ((state_d == WaitLead) | ((state_d == InternalClkLow) & (bit_cntr_q == 3'b0)))) 1 -1" (1 "011")
Condition 106 "1889227624" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkLow) & (bit_cntr_q != 3'b0)) 1 -1" (1 "0111")
Condition 112 "23619835" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkHigh) & (bit_cntr_q == 3'b0)) 1 -1" (1 "0111")
Condition 115 "3337879098" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkHigh) & (bit_cntr_q != 3'b0)) 1 -1" (1 "0111")
Condition 149 "4099565162" "((byte_cntr_late == 9'b0) & rd_en_o & sr_rd_ready_i) 1 -1" (3 "110")
Condition 151 "836227580" "((byte_cntr_early == 9'b0) & wr_en_o & sr_wr_ready_i) 1 -1" (3 "110")

// [DESIGN-UNR] Unreachable default case arm in u_fsm where all 8 3-bit state_q enum values are listed.
CHECKSUM: "1990714023 1201296722"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_fsm
ANNOTATION: "[DESIGN-UNR] Defensive default case arm for full 3-bit caliptra_ss_spi_host_st_e enum"
Branch 28 "337219961" "sw_rst_i" (17) "sw_rst_i 0,1,default,-,-,-,-,-,-,-,-"

//==================================================
// 4. PACKER FIFOs (u_merge.u_packer & u_select.u_packer)
//==================================================
// [DESIGN-UNR] ClearOnRead defaults to 1'b1 in caliptra_prim_packer_fifo.sv:47 (neither SPI packer
// overrides it), and clear_status = clr_q | (ClearOnRead & clear_data) = clr_q | clear_data.
// Therefore when clr_q == 1'b1, clear_status is unconditionally 1'b1, making
// ((ClearOnRead && clear_status)=0, clr_q=1) structurally impossible (Comment #7).
// In u_select.u_packer, Condition 7 is inside (depth_q == FullDepth) where
// rvalid_o = (depth_q != 0) is always 1'b1.
CHECKSUM: "618627179 2680453721"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_merge.u_packer
ANNOTATION: "[DESIGN-UNR] ClearOnRead=1 and clear_status=(clr_q | clear_data), so clr_q=1 implies (ClearOnRead && clear_status)=1"
Condition 3 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")

CHECKSUM: "618627179 3549702725"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_select.u_packer
ANNOTATION: "[DESIGN-UNR] clr_q=1 implies (ClearOnRead && clear_status)=1; rvalid_o=1 invariant when depth_q==FullDepth"
Condition 4 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")
Condition 7 "3660748963" "(rvalid_o && rready_i) 1 -1" (1 "01")

//==================================================
// 5. SYNC FIFOs (cmd_fifo, u_tx_fifo, u_rx_fifo)
//==================================================
// [DESIGN-UNR] In caliptra_prim_fifo_sync.sv:69-85, under_rst is a synchronous post-reset flop and
// wready_o / rvalid_o already include ~gen_normal_fifo.under_rst as a factor, so (wvalid_i & wready_o)==1
// or (rvalid_o & rready_i)==1 structurally implies ~under_rst == 1 (row "110" is impossible, Comment #7).
// In u_tx_fifo, tx_valid_checked = tx_valid & ~error_overflow = tx_valid & tx_ready, gating wvalid_i
// with wready_o so row "101" (wvalid_i=1, wready_o=0) is also structurally impossible.
CHECKSUM: "4004715651 3111044606"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_cmd_queue.cmd_fifo
ANNOTATION: "[DESIGN-UNR] wready_o and rvalid_o already include ~under_rst in caliptra_prim_fifo_sync.sv"
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 3686475193"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_data_fifos.u_tx_fifo
ANNOTATION: "[DESIGN-UNR] wready_o/rvalid_o include ~under_rst; tx_valid_checked gated by tx_ready in spi_host.sv:358"
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "101")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 2903083481"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_data_fifos.u_rx_fifo
ANNOTATION: "[DESIGN-UNR] wready_o and rvalid_o already include ~under_rst in caliptra_prim_fifo_sync.sv"
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

//==================================================
// 6. DATA FIFOS (tb.dut.u_caliptra_ss_spi_host.u_data_fifos)
//==================================================
// [TARGET-CFG] TxDepth=72 (packer-inclusive max 73 < 128) and RxDepth=64 (< 128), so MSB bit [7]
// of 8-bit queue depth outputs tx_qd_o[7] and rx_qd_o[7] is structurally 1'b0.
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_data_fifos
ANNOTATION: "[TARGET-CFG] MSB [7] of queue depth outputs (TxDepth+1=73, RxDepth=64 < 128)"
Toggle tx_qd_o [7] "logic tx_qd_o[7:0]"
Toggle rx_qd_o [7] "logic rx_qd_o[7:0]"

//==================================================
// 7. REGISTER TOP & SUBREG ARBITERS (tb.dut.u_caliptra_ss_spi_host.u_reg)
//==================================================
// (a) [DESIGN-UNR / TARGET-CFG] Constant hw2reg.status.*.de=1'b1 wire-through enables and ByteOrder=1.
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_reg
ANNOTATION: "[TARGET-CFG] Constant status write-enables (.de=1'b1), ByteOrder=1 parameter, and MSB depth bits < 128"
Toggle hw2reg.status.txqd.de "logic hw2reg.status.txqd.de"
Toggle hw2reg.status.txqd.d [7] "logic hw2reg.status.txqd.d[7:0]"
Toggle hw2reg.status.rxqd.de "logic hw2reg.status.rxqd.de"
Toggle hw2reg.status.rxqd.d [7] "logic hw2reg.status.rxqd.d[7:0]"
Toggle hw2reg.status.cmdqd.de "logic hw2reg.status.cmdqd.de"
Toggle hw2reg.status.rxwm.de "logic hw2reg.status.rxwm.de"
Toggle hw2reg.status.byteorder.de "logic hw2reg.status.byteorder.de"
Toggle hw2reg.status.byteorder.d "logic hw2reg.status.byteorder.d"
Toggle hw2reg.status.rxstall.de "logic hw2reg.status.rxstall.de"
Toggle hw2reg.status.rxempty.de "logic hw2reg.status.rxempty.de"
Toggle hw2reg.status.rxfull.de "logic hw2reg.status.rxfull.de"
Toggle hw2reg.status.txwm.de "logic hw2reg.status.txwm.de"
Toggle hw2reg.status.txstall.de "logic hw2reg.status.txstall.de"
Toggle hw2reg.status.txempty.de "logic hw2reg.status.txempty.de"
Toggle hw2reg.status.txfull.de "logic hw2reg.status.txfull.de"
Toggle hw2reg.status.active.de "logic hw2reg.status.active.de"
Toggle hw2reg.status.ready.de "logic hw2reg.status.ready.de"
Toggle hw2reg.intr_state.spi_event.de "logic hw2reg.intr_state.spi_event.de"

// (b) [DESIGN-UNR] Structurally unreachable reg_we_err terms in spi_host_reg_top.sv:75,82:
// u_prim_reg_we_check checks one-hotness of mutually exclusive CSR address
// decode comparators (addr_hit), which cannot assert in fault-free RTL bus traffic.
CHECKSUM: "3127576770 3876883752"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_reg
ANNOTATION: "[DESIGN-UNR] reg_we_err checks one-hotness of mutually exclusive CSR address decode comparators"
Condition 1 "258898769" "(intg_err || reg_we_err) 1 -1" (2 "01")
Condition 31 "8186339" "(err_q | intg_err | reg_we_err) 1 -1" (2 "001")
