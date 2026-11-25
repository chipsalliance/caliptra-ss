// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//==================================================
// Caliptra-SS SPI Host VCS Coverage Exclusion File (.el)
// Format Version: 2
// ExclMode: default
//
// Categories explicitly distinguished below (Comments #6, #7, #22, #24):
//   [DESIGN-UNR]       Structurally unreachable RTL expressions/transitions across all parameterizations.
//   [TARGET-CFG]       Parameterized target restrictions of spi_host_axi (NumCS=2, AxiIw=1, AxiDw=32,
//                      ByteOrder=1, TxDepth=72, RxDepth=64).
//   [SW-CONTRACT-UNR]  Defensive RTL arms guarded by firmware contracts & assertions (documented below,
//                      intentionally kept UNWAIVED in raw code coverage per Comment #7).
//
// Summary of structural UNR categories in spi_host_axi wrapper:
//   - Waived [TARGET-CFG] / [DESIGN-UNR] entries below:
//     * spi_host.sv:122 (`passthrough_i.passthrough_en` in gen_passthrough_ignore):
//       [TARGET-CFG] For NumCS=2, PassthroughNumCSCompat_Bound_A (bound in spi_host_bind.sv with
//       active !rst_ni reset disable) requires !passthrough_i.passthrough_en on every active clock
//       edge; sub-cycle coverage pulses were removed per Comment #22.
//     * sub2tlul.sv:91,94 (cur_txn direct valid_get_txn <-> valid_put_txn FSM transitions):
//       [TARGET-CFG] pending_txn gates tl_o.a_valid (`dv & ~pending_txn`), and u_caliptra_ss_spi_host's
//       tlul_adapter_reg / tlul_adapter_sram have >=1-cycle response latency (Pass=0), so tl_i.d_valid
//       cannot assert in the same cycle as a new tl_o.a_valid; cur_txn therefore always returns to
//       no_txn upon AccessAck/AccessAckData before the next request asserts tl_o.a_valid.
//     * axi_addr.v:180 (`2'b11` 8-byte beat alignment arm):
//       [TARGET-CFG] spi_host_axi fixes AxiDw=32 (DSZ=2, max legal AXI4 AxSIZE=3'b010 = 4 bytes).
//   - Intentionally UNWAIVED entries:
//     * spi_host_fsm.sv:423,629 & spi_host_shift_register.sv:59,64 (`speed_i == RsvdSpd (2'b11)`):
//       [SW-CONTRACT-UNR] Unreachable under confirmed Option A firmware contract requiring
//       CONTROL.SW_RST queue flush before clearing ERROR_STATUS.CMDINVAL (guarded by
//       ValidSpeed_Bound_A); kept unwaived.
//     * All SVA assertions (including the 5 unhit AXI_SUB_*_HSHAKE_ERR valid-drop assertions).
//==================================================

//==================================================
// 0. SUBSYSTEM WRAPPER TOP (tb.dut : spi_host_axi)
//==================================================
// [TARGET-CFG] NumCS = 2 elaborates gen_passthrough_ignore and PassthroughNumCSCompat_Bound_A
// requires passthrough_i.passthrough_en == 1'b0 on every active clock edge.
INSTANCE: tb.dut
ANNOTATION: "[TARGET-CFG] NumCS=2 structurally disables passthrough_en per PassthroughNumCSCompat_Bound_A"
Toggle passthrough_i.passthrough_en "logic passthrough_i.passthrough_en"

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
// PassthroughNumCSCompat_Bound_A requires passthrough_i.passthrough_en == 1'b0 when NumCS > 1.
INSTANCE: tb.dut.u_caliptra_ss_spi_host
ANNOTATION: "[TARGET-CFG] NumCS=2 structurally disables passthrough_en per PassthroughNumCSCompat_Bound_A"
Toggle passthrough_i.passthrough_en "logic passthrough_i.passthrough_en"

// [TARGET-CFG / DESIGN-UNR] Structural constants driven by production u_axi2tlul_spi_host (sub2tlul.sv)
// and TL-UL device responses on spi_host_axi (AxiIw=1, AxiDw=32):
//   - sub2tlul.sv:70,155 ties instr_type to MuBi4False (4'b1001) and upper a_user rsvd bits to 3'b0.
//   - axi_sub_{wr,rd}.sv:252,208 hardwires word-aligned addr[1:0] = BW'(0) = 2'b00 (while upper
//     a_address[31:2] bits toggle dynamically on AXI4 bus traffic).
//   - sub2tlul.sv:123 zero-extends 1-bit AXI ID (AxiIw=1) into 8-bit tl_a_source / tl_d_source [7:1].
//   - sub2tlul.sv:116,137 fixes a_param=3'h0 and encodes only PutFullData(0)/PutPartialData(1)/Get(4)
//     so a_opcode[1] is structurally 1'b0 (while a_opcode[0] and a_size[1:0] DO toggle dynamically).
//   - TL-UL device responses use only AccessAck(0)/AccessAckData(1) with d_param=0, d_sink=0;
//     in caliptra_prim_secded_inv_64_57_enc.sv:22, data_o[63] (rsp_intg[6]) XORs 64'h01FBDDA769A46910
//     masked onto 6-bit d2h_rsp_intg payload (bit [4] = d_opcode[1] == 0) with 0 inversion -> constant 1'b0.
INSTANCE: tb.dut.u_caliptra_ss_spi_host
ANNOTATION: "[TARGET-CFG] Production axi_sub / sub2tlul / TL-UL SECDED constants for spi_host_axi (AxiIw=1)"
Toggle tl_i.a_user.instr_type "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_source [7:1] "logic tl_i.a_source[7:0]"
Toggle tl_i.a_param "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_source [7:1] "logic tl_o.d_source[7:0]"
Toggle tl_o.d_param "logic tl_o.d_param[2:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"

//==================================================
// 2. SHIFT REGISTER (tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_shift_reg)
//==================================================
// [DESIGN-UNR] u_fsm gates rd_en_o with sr_rd_ready_i and wr_en_o with sr_wr_ready_i,
// so (rd_en_i=1, rd_ready_o=0) and (wr_en_i=1, wr_ready_o=0) are structurally unreachable.
// Note: speed_i == RsvdSpd (2'b11) defensive arms are [SW-CONTRACT-UNR] under the confirmed
// Option A firmware contract (CONTROL.SW_RST before W1C on CMDINVAL) and are intentionally
// kept UNWAIVED here per Comment #7.
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
// [DESIGN-UNR] In caliptra_prim_packer_fifo.sv:47,102-103,137-138, ClearOnRead defaults to 1'b1
// (neither SPI packer overrides it), clear_status includes `|| clr_q` in both gen_pack_mode
// (u_merge.u_packer: `(rready_i && rvalid_o) || clr_q`) and gen_unpack_mode (u_select.u_packer:
// `(rready_i && (depth_q == lsb_is_one)) || clr_q`), and `clear_data = (ClearOnRead && clear_status) || clr_q`.
// Therefore clr_q == 1'b1 structurally forces clear_status == 1'b1 and (ClearOnRead && clear_status) == 1'b1,
// making row "01" (((ClearOnRead && clear_status)=0, clr_q=1)) impossible (Comment #7).
// In u_select.u_packer (gen_unpack_mode, InW=36 > OutW=9), Condition 7 is `pull_data = rvalid_o && rready_i`
// (line 140), where rvalid_o connects to byte_valid and rready_i connects to `byte_ready = byte_ready_i | do_drain`
// in spi_host_byte_select.sv:29-31. When byte_valid == 1'b0: do_drain == 1'b0 and byte_valid_o == 1'b0,
// which forces u_shift_reg.wr_ready_o == 1'b0 and u_fsm.wr_en_o (byte_ready_i) == 1'b0, making
// row "01" (rvalid_o=0, rready_i=1) structurally unreachable.
CHECKSUM: "618627179 2680453721"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_merge.u_packer
ANNOTATION: "[DESIGN-UNR] ClearOnRead=1 and clear_status=((rready_i && rvalid_o) || clr_q), so clr_q=1 implies (ClearOnRead && clear_status)=1"
Condition 3 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")

CHECKSUM: "618627179 3549702725"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_spi_core.u_select.u_packer
ANNOTATION: "[DESIGN-UNR] clr_q=1 implies (ClearOnRead && clear_status)=1; byte_valid=0 gates both do_drain and u_shift_reg/u_fsm byte_ready_i to 0"
Condition 4 "1116830244" "((ClearOnRead && clear_status) || clr_q) 1 -1" (2 "01")
Condition 7 "3660748963" "(rvalid_o && rready_i) 1 -1" (1 "01")

//==================================================
// 5. SYNC FIFOs (cmd_fifo, u_tx_fifo, u_rx_fifo)
//==================================================
// [DESIGN-UNR / TARGET-CFG] In caliptra_prim_fifo_sync.sv:69-85, under_rst is a synchronous
// post-reset flop and wready_o / rvalid_o already include ~gen_normal_fifo.under_rst as a factor:
//   - On line 84 (rvalid_o = ~empty & ~under_rst): with Pass=1, empty = fifo_empty & ~wvalid_i.
//     rst_ni==0 resets fifo_empty=1 (and wready_o=0 while under_rst==1 prevents any FIFO push);
//     upstream TL-UL/SPI writers hold wvalid_i==0 while rst_ni==0 / during the single post-reset
//     under_rst cycle, so empty remains 1 throughout under_rst==1 and (~empty=1, ~under_rst=0) is
//     unreachable.
//   - On lines 105-106: (wvalid_i & wready_o)==1 or (rvalid_o & rready_i)==1 structurally implies
//     ~under_rst == 1 (row "110" is impossible, Comment #7).
// In u_tx_fifo, tx_valid_checked = tx_valid & ~error_overflow = tx_valid & tx_ready, gating wvalid_i
// with wready_o so row "101" (wvalid_i=1, wready_o=0) is also structurally impossible.
CHECKSUM: "4004715651 3111044606"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_cmd_queue.cmd_fifo
ANNOTATION: "[DESIGN-UNR] Pass=1 empty=fifo_empty&~wvalid_i stays 1 while under_rst=1 (upstream wvalid_i=0 under reset); wready_o/rvalid_o include ~under_rst"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 3686475193"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_data_fifos.u_tx_fifo
ANNOTATION: "[DESIGN-UNR] Pass=1 empty=fifo_empty&~wvalid_i stays 1 while under_rst=1 (upstream wvalid_i=0 under reset); wready_o/rvalid_o include ~under_rst; tx_valid_checked gated by tx_ready"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "101")
Condition 3 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (3 "110")

CHECKSUM: "4004715651 2903083481"
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_data_fifos.u_rx_fifo
ANNOTATION: "[DESIGN-UNR] Pass=1 empty=fifo_empty&~wvalid_i stays 1 while under_rst=1 (upstream wvalid_i=0 under reset); wready_o/rvalid_o include ~under_rst"
Condition 2 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")
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

// (c) [TARGET-CFG / DESIGN-UNR] Propagation of structural TL-UL bus constants on u_reg & u_window ports:
//   - Upstream tl_i / tl_win_o[0..1] constants identical to Section 1 (instr_type=MuBi4False, rsvd=0,
//     a_address[1:0]=2'b00, a_source[7:1]=0, a_param=0, a_opcode[1]=0; upper a_address[31:2] bits
//     are NOT waived and toggle dynamically).
//   - Window D-channel constants: u_window.u_adapter_rx (tlul_adapter_reg with EnableDataIntgGen=0,
//     EnableRspIntgGen=0) ties rx_win_o.d_user = '0, and u_window.u_adapter_tx (tlul_adapter_sram with
//     ErrOnRead=1, EnableDataIntgGen=0, EnableRspIntgGen=0, rdata_i='0) ties tx_win_o.d_data = 32'h0
//     and tx_win_o.d_user = '0.
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_reg
ANNOTATION: "[TARGET-CFG] Propagated TL-UL bus & window adapter structural port constants (AxiIw=1)"
Toggle tl_i.a_user.instr_type "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_source [7:1] "logic tl_i.a_source[7:0]"
Toggle tl_i.a_param "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_source [7:1] "logic tl_o.d_source[7:0]"
Toggle tl_o.d_param "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"
Toggle tl_win_o[0].a_user.instr_type "logic tl_win_o[0].a_user.instr_type[3:0]"
Toggle tl_win_o[0].a_user.rsvd "logic tl_win_o[0].a_user.rsvd[2:0]"
Toggle tl_win_o[0].a_address [1:0] "logic tl_win_o[0].a_address[31:0]"
Toggle tl_win_o[0].a_source [7:1] "logic tl_win_o[0].a_source[7:0]"
Toggle tl_win_o[0].a_param "logic tl_win_o[0].a_param[2:0]"
Toggle tl_win_o[0].a_opcode [1] "logic tl_win_o[0].a_opcode[2:0]"
Toggle tl_win_o[1].a_user.instr_type "logic tl_win_o[1].a_user.instr_type[3:0]"
Toggle tl_win_o[1].a_user.rsvd "logic tl_win_o[1].a_user.rsvd[2:0]"
Toggle tl_win_o[1].a_address [1:0] "logic tl_win_o[1].a_address[31:0]"
Toggle tl_win_o[1].a_source [7:1] "logic tl_win_o[1].a_source[7:0]"
Toggle tl_win_o[1].a_param "logic tl_win_o[1].a_param[2:0]"
Toggle tl_win_o[1].a_opcode [1] "logic tl_win_o[1].a_opcode[2:0]"
Toggle tl_win_i[0].d_user.data_intg "logic tl_win_i[0].d_user.data_intg[6:0]"
Toggle tl_win_i[0].d_user.rsp_intg "logic tl_win_i[0].d_user.rsp_intg[6:0]"
Toggle tl_win_i[0].d_sink "logic tl_win_i[0].d_sink[0:0]"
Toggle tl_win_i[0].d_source [7:1] "logic tl_win_i[0].d_source[7:0]"
Toggle tl_win_i[0].d_param "logic tl_win_i[0].d_param[2:0]"
Toggle tl_win_i[0].d_opcode [2:1] "logic tl_win_i[0].d_opcode[2:0]"
Toggle tl_win_i[1].d_user.data_intg "logic tl_win_i[1].d_user.data_intg[6:0]"
Toggle tl_win_i[1].d_user.rsp_intg "logic tl_win_i[1].d_user.rsp_intg[6:0]"
Toggle tl_win_i[1].d_data "logic tl_win_i[1].d_data[31:0]"
Toggle tl_win_i[1].d_sink "logic tl_win_i[1].d_sink[0:0]"
Toggle tl_win_i[1].d_source [7:1] "logic tl_win_i[1].d_source[7:0]"
Toggle tl_win_i[1].d_param "logic tl_win_i[1].d_param[2:0]"
Toggle tl_win_i[1].d_opcode [2:1] "logic tl_win_i[1].d_opcode[2:0]"

//==================================================
// 8. FIFO WINDOW WRAPPER (tb.dut.u_caliptra_ss_spi_host.u_window)
//==================================================
INSTANCE: tb.dut.u_caliptra_ss_spi_host.u_window
ANNOTATION: "[TARGET-CFG] Propagated TL-UL bus & window adapter structural port constants (AxiIw=1)"
Toggle rx_win_i.a_user.instr_type "logic rx_win_i.a_user.instr_type[3:0]"
Toggle rx_win_i.a_user.rsvd "logic rx_win_i.a_user.rsvd[2:0]"
Toggle rx_win_i.a_address [1:0] "logic rx_win_i.a_address[31:0]"
Toggle rx_win_i.a_source [7:1] "logic rx_win_i.a_source[7:0]"
Toggle rx_win_i.a_param "logic rx_win_i.a_param[2:0]"
Toggle rx_win_i.a_opcode [1] "logic rx_win_i.a_opcode[2:0]"
Toggle rx_win_o.d_user.data_intg "logic rx_win_o.d_user.data_intg[6:0]"
Toggle rx_win_o.d_user.rsp_intg "logic rx_win_o.d_user.rsp_intg[6:0]"
Toggle rx_win_o.d_sink "logic rx_win_o.d_sink[0:0]"
Toggle rx_win_o.d_source [7:1] "logic rx_win_o.d_source[7:0]"
Toggle rx_win_o.d_param "logic rx_win_o.d_param[2:0]"
Toggle rx_win_o.d_opcode [2:1] "logic rx_win_o.d_opcode[2:0]"
Toggle tx_win_i.a_user.instr_type "logic tx_win_i.a_user.instr_type[3:0]"
Toggle tx_win_i.a_user.rsvd "logic tx_win_i.a_user.rsvd[2:0]"
Toggle tx_win_i.a_address [1:0] "logic tx_win_i.a_address[31:0]"
Toggle tx_win_i.a_source [7:1] "logic tx_win_i.a_source[7:0]"
Toggle tx_win_i.a_param "logic tx_win_i.a_param[2:0]"
Toggle tx_win_i.a_opcode [1] "logic tx_win_i.a_opcode[2:0]"
Toggle tx_win_o.d_user.data_intg "logic tx_win_o.d_user.data_intg[6:0]"
Toggle tx_win_o.d_user.rsp_intg "logic tx_win_o.d_user.rsp_intg[6:0]"
Toggle tx_win_o.d_data "logic tx_win_o.d_data[31:0]"
Toggle tx_win_o.d_sink "logic tx_win_o.d_sink[0:0]"
Toggle tx_win_o.d_source [7:1] "logic tx_win_o.d_source[7:0]"
Toggle tx_win_o.d_param "logic tx_win_o.d_param[2:0]"
Toggle tx_win_o.d_opcode [2:1] "logic tx_win_o.d_opcode[2:0]"

//==================================================
// 9. AXI-TO-TL-UL GASKET STRUCTURAL INVARIANTS (tb.dut.u_axi2tlul_spi_host)
//==================================================
// Note: Complex sub2tlul combinational condition tables and all AXI_SUB_*_HSHAKE_ERR SVA assertions
// remain intentionally UNWAIVED. Only strictly RTL-proven structural constants for spi_host_axi
// (AxiIw=1, AxiDw=32 / DSZ=2, CALIPTRA_AXI_SUB_EX_EN undefined) and provable [DESIGN-UNR] /
// [TARGET-CFG] FSM/skidbuffer invariants follow.

// (a) [TARGET-CFG] sub2tlul.sv:91,94: pending_txn gates tl_o.a_valid (`dv & ~pending_txn`), and
// u_caliptra_ss_spi_host's tlul_adapter_reg / tlul_adapter_sram have >=1-cycle response latency
// (Pass=0), so cur_txn always returns to no_txn on AccessAck/AccessAckData before a new request
// can assert a_valid.
CHECKSUM: "2553605572 984500570"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_sub2tlul
ANNOTATION: "[TARGET-CFG] pending_txn gates tl_o.a_valid and spi_host adapters have >=1-cycle response latency (Pass=0), forcing cur_txn through no_txn"
Fsm cur_txn "984500570"
Transition valid_get_txn->valid_put_txn "1->2"
Fsm cur_txn "984500570"
Transition valid_put_txn->valid_get_txn "2->1"

// (b) [TARGET-CFG] axi_sub_wr.sv:157 hardwires s_axi_if_ctx.lock = 1'b0 because the compile-time
// macro CALIPTRA_AXI_SUB_EX_EN is undefined in this build, so AXI_RESP_EXOKAY at lines 341-342 is
// unreachable.
CHECKSUM: "1738911288 1896776429"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr
ANNOTATION: "[TARGET-CFG] CALIPTRA_AXI_SUB_EX_EN undefined hardwires s_axi_if_ctx.lock=1'b0 in axi_sub_wr.sv:157"
Condition 17 "1180556428" "(txn_allow && txn_ctx.lock) 1 -1" (3 "11")
Condition 18 "4215928670" "((txn_allow && txn_ctx.lock) ? AXI_RESP_EXOKAY : AXI_RESP_OKAY) 1 -1" (2 "1")

CHECKSUM: "1738911288 936540671"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr
ANNOTATION: "[TARGET-CFG] CALIPTRA_AXI_SUB_EX_EN undefined hardwires s_axi_if_ctx.lock=1'b0 in axi_sub_wr.sv:157"
Branch 0 "166815847" "(txn_allow && (txn_err || err))" (1) "(txn_allow && (txn_err || err)) 0,1"

// (c) [TARGET-CFG] axi_addr.v:180 (2'b11 8-byte alignment arm): spi_host_axi fixes AxiDw=32 (DSZ=2),
// capping legal AXI4 AxSIZE to 3'b010 (4 bytes); 2'b11 (8 bytes) and MISSING_DEFAULT are unreachable.
CHECKSUM: "2805675034 3365616828"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 (DSZ=2) caps legal AXI4 AxSIZE at 3'b010 (4B); 8B case arm unreachable"
Block 30 "203408636" "aligned_addr[(((AW - 1) > 2) ? 2 : (AW - 1)):0] = 0;"

CHECKSUM: "2805675034 3365616828"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 (DSZ=2) caps legal AXI4 AxSIZE at 3'b010 (4B); 8B case arm unreachable"
Block 30 "203408636" "aligned_addr[(((AW - 1) > 2) ? 2 : (AW - 1)):0] = 0;"

CHECKSUM: "2805675034 2099123372"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 (DSZ=2): DSZ!=3, 8B i_size=2'b11, and case MISSING_DEFAULT unreachable"
Branch 0 "500883511" "(DSZ == 0)" (10) "(DSZ == 0) 0,0,-,0,-,-,1,MISSING_DEFAULT"
Branch 2 "3983581749" "(i_burst != FIXED)" (5) "(i_burst != FIXED) 1,0,-,1,2'b11 ,-"
Branch 2 "3983581749" "(i_burst != FIXED)" (6) "(i_burst != FIXED) 1,0,-,1,MISSING_DEFAULT,-"

CHECKSUM: "2805675034 2099123372"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 (DSZ=2): DSZ!=3, 8B i_size=2'b11, and case MISSING_DEFAULT unreachable"
Branch 0 "500883511" "(DSZ == 0)" (10) "(DSZ == 0) 0,0,-,0,-,-,1,MISSING_DEFAULT"
Branch 2 "3983581749" "(i_burst != FIXED)" (5) "(i_burst != FIXED) 1,0,-,1,2'b11 ,-"
Branch 2 "3983581749" "(i_burst != FIXED)" (6) "(i_burst != FIXED) 1,0,-,1,MISSING_DEFAULT,-"

// (d) [DESIGN-UNR] skidbuffer.v:143:
//   - OPT_OUTREG=0: o_valid = i_valid || r_valid and o_ready = !r_valid, so (i_valid=0, o_ready=1,
//     o_valid=1) and (i_valid=1, o_ready=1, o_valid=0) are boolean contradictions.
//   - OPT_OUTREG=1 (i_rsp_skd): axi_sub_wr.sv:180 gates req_ready on rp_ready (o_ready), guaranteeing
//     a free response slot so (i_valid=1, o_ready=0) cannot occur.
CHECKSUM: "2730301546 2739831295"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_req_skd
ANNOTATION: "[DESIGN-UNR] OPT_OUTREG=0 skidbuffer: o_valid=(i_valid||r_valid) and o_ready=!r_valid"
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (1 "0111")
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (3 "1101")

CHECKSUM: "2730301546 2739831295"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_dp_skd
ANNOTATION: "[DESIGN-UNR] OPT_OUTREG=0 skidbuffer: o_valid=(i_valid||r_valid) and o_ready=!r_valid"
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (1 "0111")
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (3 "1101")

CHECKSUM: "2730301546 2739831295"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd.DATA_PIPELINE[0].i_dp_skd
ANNOTATION: "[DESIGN-UNR] OPT_OUTREG=0 skidbuffer: o_valid=(i_valid||r_valid) and o_ready=!r_valid"
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (1 "0111")
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (3 "1101")

CHECKSUM: "2730301546 2418819841"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_rsp_skd
ANNOTATION: "[DESIGN-UNR] axi_sub_wr.sv:180 gates req_ready on rp_ready (o_ready), preventing i_valid&&!o_ready"
Condition 1 "2827200384" "(i_valid && o_ready && o_valid && ((!i_ready))) 1 -1" (2 "1011")

// (e) [TARGET-CFG] Structural port constants on u_axi2tlul_spi_host hierarchy (AxiIw=1, AxiDw=32, CALIPTRA_AXI_SUB_EX_EN undefined):
//   - Same 11 TL-UL bus constants as Section 1 on axi2tlul / sub2tlul ports.
//   - Word-aligned addr[1:0]=2'b00 on sub2tlul / axi_sub_arb; size[2]=1'b0 (AxiDw=32 -> max AxSIZE=2).
//   - Undefined CALIPTRA_AXI_SUB_EX_EN hardwires lock=0 (i_req_skd data[0]) and resp[0]=0 (i_rsp_skd & rd i_dp_skd data[1]);
//     AxiDw=32 hardwires awsize[2]=0 (i_req_skd data[44]).
INSTANCE: tb.dut.u_axi2tlul_spi_host
ANNOTATION: "[TARGET-CFG] Structural TL-UL port constants for spi_host_axi (AxiIw=1, AxiDw=32)"
Toggle tl_o.a_user.instr_type "logic tl_o.a_user.instr_type[3:0]"
Toggle tl_o.a_user.rsvd "logic tl_o.a_user.rsvd[2:0]"
Toggle tl_o.a_address [1:0] "logic tl_o.a_address[31:0]"
Toggle tl_o.a_source [7:1] "logic tl_o.a_source[7:0]"
Toggle tl_o.a_param "logic tl_o.a_param[2:0]"
Toggle tl_o.a_opcode [1] "logic tl_o.a_opcode[2:0]"
Toggle tl_i.d_user.rsp_intg [6] "logic tl_i.d_user.rsp_intg[6:0]"
Toggle tl_i.d_sink "logic tl_i.d_sink[0:0]"
Toggle tl_i.d_source [7:1] "logic tl_i.d_source[7:0]"
Toggle tl_i.d_param "logic tl_i.d_param[2:0]"
Toggle tl_i.d_opcode [2:1] "logic tl_i.d_opcode[2:0]"

INSTANCE: tb.dut.u_axi2tlul_spi_host.i_sub2tlul
ANNOTATION: "[TARGET-CFG] Structural TL-UL & word-aligned AxiDw=32/AxiIw=1 port constants"
Toggle addr [1:0] "logic addr[31:0]"
Toggle size [2] "logic size[2:0]"
Toggle tl_o.a_user.instr_type "logic tl_o.a_user.instr_type[3:0]"
Toggle tl_o.a_user.rsvd "logic tl_o.a_user.rsvd[2:0]"
Toggle tl_o.a_address [1:0] "logic tl_o.a_address[31:0]"
Toggle tl_o.a_source [7:1] "logic tl_o.a_source[7:0]"
Toggle tl_o.a_param "logic tl_o.a_param[2:0]"
Toggle tl_o.a_opcode [1] "logic tl_o.a_opcode[2:0]"
Toggle tl_i.d_user.rsp_intg [6] "logic tl_i.d_user.rsp_intg[6:0]"
Toggle tl_i.d_sink "logic tl_i.d_sink[0:0]"
Toggle tl_i.d_source [7:1] "logic tl_i.d_source[7:0]"
Toggle tl_i.d_param "logic tl_i.d_param[2:0]"
Toggle tl_i.d_opcode [2:1] "logic tl_i.d_opcode[2:0]"

INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_arb
ANNOTATION: "[TARGET-CFG] AxiDw=32 caps AxSIZE[2]=0; axi_sub_{rd,wr} word-align addr[1:0]=2'b00"
Toggle r_size [2] "logic r_size[2:0]"
Toggle w_size [2] "logic w_size[2:0]"
Toggle addr [1:0] "logic addr[31:0]"
Toggle size [2] "logic size[2:0]"

INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd
ANNOTATION: "[TARGET-CFG] AxiDw=32 caps AxSIZE[2]=0"
Toggle size [2] "logic size[2:0]"

INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr
ANNOTATION: "[TARGET-CFG] AxiDw=32 caps AxSIZE[2]=0"
Toggle wsize [2] "logic wsize[2:0]"

CHECKSUM: "2805675034 3375835418"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 caps AxSIZE[2]=0"
Toggle i_size [2] "logic i_size[2:0]"

CHECKSUM: "2805675034 3375835418"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_axi_addr
ANNOTATION: "[TARGET-CFG] AxiDw=32 caps AxSIZE[2]=0"
Toggle i_size [2] "logic i_size[2:0]"

CHECKSUM: "2730301546 619868591"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_req_skd
ANNOTATION: "[TARGET-CFG] CALIPTRA_AXI_SUB_EX_EN undefined ties awlock (bit 0)=0; AxiDw=32 ties awsize[2] (bit 44)=0"
Toggle i_data [0] "logic i_data[78:0]"
Toggle i_data [44] "logic i_data[78:0]"
Toggle o_data [0] "logic o_data[78:0]"
Toggle o_data [44] "logic o_data[78:0]"

CHECKSUM: "2730301546 1462248156"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_wr.i_rsp_skd
ANNOTATION: "[TARGET-CFG] CALIPTRA_AXI_SUB_EX_EN undefined ties rp_resp[0] (bit 1, EXOKAY LSB)=0"
Toggle i_data [1] "logic i_data[2:0]"
Toggle o_data [1] "logic o_data[2:0]"

CHECKSUM: "2730301546 1129095229"
INSTANCE: tb.dut.u_axi2tlul_spi_host.i_axi_sub.i_axi_sub_rd.DATA_PIPELINE[0].i_dp_skd
ANNOTATION: "[TARGET-CFG] CALIPTRA_AXI_SUB_EX_EN undefined ties dp_xfer_ctx[0].resp[0] (bit 1, EXOKAY LSB)=0"
Toggle i_data [1] "logic i_data[67:0]"
Toggle o_data [1] "logic o_data[67:0]"
