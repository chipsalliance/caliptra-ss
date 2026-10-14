// Copyright 2026 Google LLC(OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//==================================================
// Caliptra-SS SPI Host VCS Coverage Exclusion File (.el)
// Format Version: 2
// ExclMode: default
//==================================================

//==================================================
// 1. TOP-LEVEL MODULE (tb.dut : caliptra_ss_spi_host)
//==================================================
// Unreachable condition row: in spi_host.sv:154-166, test_speed_inval is only
// set to 1 in the default case branch where test_dir_inval is also set to 1,
// so (test_speed_inval=1, test_dir_inval=0) is structurally unreachable.
CHECKSUM: "2960936678 1977424990"
INSTANCE: tb.dut
ANNOTATION: "UNR: test_speed_inval=1 always implies test_dir_inval=1 in spi_host.sv:164-165"
Condition 5 "2312135264" "(test_speed_inval | test_dir_inval) 1 -1" (3 "10")

// Tied-off TL-UL / AXI-subordinate bridge port bits on tb.dut
INSTANCE: tb.dut
ANNOTATION: "Tied-off TL-UL / AXI adapter signals on spi_host top-level"
Toggle tl_i.a_user.instr_type [2:1] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_address [31:6] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_source "logic tl_i.a_source[7:0]"
Toggle tl_i.a_size [0] "logic tl_i.a_size[1:0]"
Toggle tl_i.a_param "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1:0] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [3] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_source "logic tl_o.d_source[7:0]"
Toggle tl_o.d_size [0] "logic tl_o.d_size[1:0]"
Toggle tl_o.d_param "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"

//==================================================
// 2. SHIFT REGISTER (tb.dut.u_spi_core.u_shift_reg)
//==================================================
// (a) speed_i == 2'b11 (Rsvd) is rejected at CSR write time by error_cmd_inval
//     and never forwarded to u_shift_reg, so the false arm of (speed_i == Quad)
//     when speed_i != Standard && speed_i != Dual is unreachable.
// (b) u_fsm gates rd_en_o with sr_rd_ready_i and wr_en_o with sr_wr_ready_i,
//     so (rd_en_i=1, rd_ready_o=0) and (wr_en_i=1, wr_ready_o=0) are unreachable.
CHECKSUM: "3611448077 2976194449"
INSTANCE: tb.dut.u_spi_core.u_shift_reg
ANNOTATION: "UNR: speed_i == Rsvd (2'b11) blocked by command validation; rd_en/wr_en stalled when !ready"
Condition 6 "245765369" "((speed_i == Quad) ? ({sr_q[3:0], next_bits[3:0]}) : 8'b0) 1 -1" (1 "0")
Condition 7 "4291680509" "(speed_i == Quad) 1 -1" (1 "0")
Condition 12 "2806144589" "((speed_i == Quad) ? ({sr_q[7:4]}) : 4'b0) 1 -1" (1 "0")
Condition 13 "3728998908" "(speed_i == Quad) 1 -1" (1 "0")
Condition 18 "864104756" "(rd_en_i && rd_ready_o) 1 -1" (2 "10")
Condition 21 "1964525666" "(rd_en_i && rd_ready_o) 1 -1" (2 "10")
Condition 28 "1682065670" "(wr_en_i & wr_ready_o) 1 -1" (2 "10")

CHECKSUM: "3611448077 2617011516"
INSTANCE: tb.dut.u_spi_core.u_shift_reg
ANNOTATION: "UNR: speed_i == Rsvd (2'b11) ternary default branch arm"
Branch 1 "840386731" "(speed_i == Standard)" (3) "(speed_i == Standard) 0,0,0"
Branch 2 "840386731" "(speed_i == Standard)" (3) "(speed_i == Standard) 0,0,0"

//==================================================
// 3. SPI HOST FSM (tb.dut.u_spi_core.u_fsm)
//==================================================
// Unreachable condition rows due to FSM invariant relationships:
// - Condition 74: shift_en_internal is gated by ~stall in FSM state equations.
// - Conditions 100, 106, 112, 115: state_changing is 0 whenever sw_rst_i is 1
//   and state_q is already Idle, or mutually exclusive with WaitLead/InternalClk*.
// - Conditions 149, 151: rd_en_o / wr_en_o stall the FSM when !sr_rd_ready_i / !sr_wr_ready_i.
CHECKSUM: "1990714023 2778135185"
INSTANCE: tb.dut.u_spi_core.u_fsm
ANNOTATION: "UNR: Mutually exclusive FSM state/stall/handshake condition terms"
Condition 74 "1393146906" "(shift_en_internal & ((~stall))) 1 -1" (2 "10")
Condition 100 "2255307332" "(((~sw_rst_i)) & state_changing & ((state_d == WaitLead) | ((state_d == InternalClkLow) & (bit_cntr_q == 3'b0)))) 1 -1" (1 "011")
Condition 106 "1889227624" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkLow) & (bit_cntr_q != 3'b0)) 1 -1" (1 "0111")
Condition 112 "23619835" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkHigh) & (bit_cntr_q == 3'b0)) 1 -1" (1 "0111")
Condition 115 "3337879098" "(((~sw_rst_i)) & state_changing & (state_d == InternalClkHigh) & (bit_cntr_q != 3'b0)) 1 -1" (1 "0111")
Condition 149 "4099565162" "((byte_cntr_late == 9'b0) & rd_en_o & sr_rd_ready_i) 1 -1" (3 "110")
Condition 151 "836227580" "((byte_cntr_early == 9'b0) & wr_en_o & sr_wr_ready_i) 1 -1" (3 "110")

// Unreachable default case arms in u_fsm (all 8 3-bit state_q enum values are
// explicitly listed, and speed==2'b11 is blocked by command validation).
CHECKSUM: "1990714023 1201296722"
INSTANCE: tb.dut.u_spi_core.u_fsm
ANNOTATION: "UNR: Defensive default case arms for full 3-bit state_e and validated 2-bit speed"
Branch 28 "337219961" "sw_rst_i" (17) "sw_rst_i 0,1,default,-,-,-,-,-,-,-,-"
Branch 31 "634942291" "((!cmd_rd_en_d) && (!cmd_wr_en_d))" (4) "((!cmd_rd_en_d) && (!cmd_wr_en_d)) 0,default"
Branch 39 "566322999" "(&csb_o)" (4) "(&csb_o) 0,default"

//==================================================
// 4. PACKER FIFOs (u_merge.u_packer & u_select.u_packer)
//==================================================
// ClearOnRead is parameterized to 1'b0, and clear_status is (clr_q | ...),
// so ((ClearOnRead && clear_status)=0, clr_q=1) cannot occur when ClearOnRead
// is evaluated, and in u_select.u_packer line 140 is inside (depth_q == FullDepth)
// where rvalid_o = (depth_q != 0) is always 1.
CHECKSUM: "618627179 2680453721"
INSTANCE: tb.dut.u_spi_core.u_merge.u_packer
ANNOTATION: "UNR: Parameter ClearOnRead=0 tied-off condition term"
Condition 3 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")

CHECKSUM: "618627179 3549702725"
INSTANCE: tb.dut.u_spi_core.u_select.u_packer
ANNOTATION: "UNR: Parameter ClearOnRead=0 and rvalid_o=1 invariant when depth_q==FullDepth"
Condition 4 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")
Condition 7 "3660748963" "(rvalid_o && rready_i) 1 -1" (1 "01")

//==================================================
// 5. SYNC FIFOs (cmd_fifo, u_tx_fifo, u_rx_fifo)
//==================================================
// Parameter Secure=0 ties gen_normal_fifo.under_rst to constant 1'b0
// (~under_rst is always 1'b1). In u_tx_fifo, wvalid_i is externally gated by
// wready_o via prim_tlul_adapter_sram.
CHECKSUM: "4004715651 3111044606"
INSTANCE: tb.dut.u_cmd_queue.cmd_fifo
ANNOTATION: "UNR: Secure=0 ties gen_normal_fifo.under_rst to 1'b0"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 3686475193"
INSTANCE: tb.dut.u_data_fifos.u_tx_fifo
ANNOTATION: "UNR: Secure=0 ties gen_normal_fifo.under_rst to 1'b0; wvalid_i gated by wready_o"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "101")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 2903083481"
INSTANCE: tb.dut.u_data_fifos.u_rx_fifo
ANNOTATION: "UNR: Secure=0 ties gen_normal_fifo.under_rst to 1'b0"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

//==================================================
// 6. DATA FIFOS (tb.dut.u_data_fifos)
//==================================================
// TxDepth=72 (<128) and RxDepth=64 (<128), so MSB bit [7] of 8-bit queue
// depth outputs tx_qd_o[7] and rx_qd_o[7] is structurally tied to 1'b0.
INSTANCE: tb.dut.u_data_fifos
ANNOTATION: "Tied-off MSB [7] of queue depth outputs (TxDepth=72, RxDepth=64 < 128)"
Toggle tx_qd_o [7] "logic tx_qd_o[7:0]"
Toggle rx_qd_o [7] "logic rx_qd_o[7:0]"

//==================================================
// 7. REGISTER TOP & SUBREG ARBITERS (tb.dut.u_reg)
//==================================================
// (a) Tied-off TL-UL / window / constant hw2reg.status.*.de signals in u_reg.
INSTANCE: tb.dut.u_reg
ANNOTATION: "Tied-off TL-UL bus fields, window response fields, and constant status write-enables"
Toggle tl_i.a_user.instr_type [2:1] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_address [31:6] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_source "logic tl_i.a_source[7:0]"
Toggle tl_i.a_size [0] "logic tl_i.a_size[1:0]"
Toggle tl_i.a_param "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1:0] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [3] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_source "logic tl_o.d_source[7:0]"
Toggle tl_o.d_size [0] "logic tl_o.d_size[1:0]"
Toggle tl_o.d_param "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"
Toggle tl_win_o[0].a_user.instr_type [2:1] "logic tl_win_o[0:1].a_user.instr_type[3:0]"
Toggle tl_win_o[0].a_user.rsvd "logic tl_win_o[0:1].a_user.rsvd[2:0]"
Toggle tl_win_o[0].a_address [1:0] "logic tl_win_o[0:1].a_address[31:0]"
Toggle tl_win_o[0].a_address [31:6] "logic tl_win_o[0:1].a_address[31:0]"
Toggle tl_win_o[0].a_source "logic tl_win_o[0:1].a_source[7:0]"
Toggle tl_win_o[0].a_size [0] "logic tl_win_o[0:1].a_size[1:0]"
Toggle tl_win_o[0].a_param "logic tl_win_o[0:1].a_param[2:0]"
Toggle tl_win_o[0].a_opcode [1:0] "logic tl_win_o[0:1].a_opcode[2:0]"
Toggle tl_win_o[1].a_user.instr_type [2:1] "logic tl_win_o[0:1].a_user.instr_type[3:0]"
Toggle tl_win_o[1].a_user.rsvd "logic tl_win_o[0:1].a_user.rsvd[2:0]"
Toggle tl_win_o[1].a_address [1:0] "logic tl_win_o[0:1].a_address[31:0]"
Toggle tl_win_o[1].a_address [31:6] "logic tl_win_o[0:1].a_address[31:0]"
Toggle tl_win_o[1].a_source "logic tl_win_o[0:1].a_source[7:0]"
Toggle tl_win_o[1].a_size [0] "logic tl_win_o[0:1].a_size[1:0]"
Toggle tl_win_o[1].a_param "logic tl_win_o[0:1].a_param[2:0]"
Toggle tl_win_o[1].a_opcode [1:0] "logic tl_win_o[0:1].a_opcode[2:0]"
Toggle tl_win_i[0].d_error "logic tl_win_i[0:1].d_error"
Toggle tl_win_i[0].d_user.data_intg "logic tl_win_i[0:1].d_user.data_intg[6:0]"
Toggle tl_win_i[0].d_user.rsp_intg "logic tl_win_i[0:1].d_user.rsp_intg[6:0]"
Toggle tl_win_i[0].d_sink "logic tl_win_i[0:1].d_sink[0:0]"
Toggle tl_win_i[0].d_source "logic tl_win_i[0:1].d_source[7:0]"
Toggle tl_win_i[0].d_size [0] "logic tl_win_i[0:1].d_size[1:0]"
Toggle tl_win_i[0].d_param "logic tl_win_i[0:1].d_param[2:0]"
Toggle tl_win_i[0].d_opcode [2:1] "logic tl_win_i[0:1].d_opcode[2:0]"
Toggle tl_win_i[1].d_error "logic tl_win_i[0:1].d_error"
Toggle tl_win_i[1].d_user.data_intg "logic tl_win_i[0:1].d_user.data_intg[6:0]"
Toggle tl_win_i[1].d_user.rsp_intg "logic tl_win_i[0:1].d_user.rsp_intg[6:0]"
Toggle tl_win_i[1].d_data "logic tl_win_i[0:1].d_data[31:0]"
Toggle tl_win_i[1].d_sink "logic tl_win_i[0:1].d_sink[0:0]"
Toggle tl_win_i[1].d_source "logic tl_win_i[0:1].d_source[7:0]"
Toggle tl_win_i[1].d_size [0] "logic tl_win_i[0:1].d_size[1:0]"
Toggle tl_win_i[1].d_param "logic tl_win_i[0:1].d_param[2:0]"
Toggle tl_win_i[1].d_opcode [2:1] "logic tl_win_i[0:1].d_opcode[2:0]"
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
