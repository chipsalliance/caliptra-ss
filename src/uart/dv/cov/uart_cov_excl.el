// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Coverage exclusion file for Caliptra SS UART DV
// Format Version: 2
// ExclMode: default

ANNOTATION: "[SUB2TLUL_INTG] Pre-verified TL-UL command integrity generator with constant fields"
INSTANCE: tb.dut.u_axi2tlul_uart.i_sub2tlul.u_axi2tlul_cmd_intg_gen

ANNOTATION: "[SUB2TLUL_INTG] Pre-verified SECDED 64_57 command encoder with constant upper zero-padding"
INSTANCE: tb.dut.u_axi2tlul_uart.i_sub2tlul.u_axi2tlul_cmd_intg_gen.u_cmd_gen

ANNOTATION: "[TLUL_CMD_INTG_CHK] Internal TL-UL command integrity checker fed by hardware axi2tlul_cmd_intg_gen"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_chk

ANNOTATION: "[SECDED_64_57_DEC] Pre-verified SECDED decoder fed by valid ECC from hardware axi2tlul_cmd_intg_gen"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_chk.u_chk

ANNOTATION: "[TLUL_RSP_INTG_GEN] Pre-verified TL-UL response integrity generator wrapper"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_rsp_intg_gen

ANNOTATION: "[SECDED_39_32_ENC] Pre-verified response SECDED encoder with upper 51 input bits tied to 0"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_rsp_intg_gen.gen_rsp_intg.u_rsp_gen

ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1b0) and .wd(0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark

ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1b0) and .wd(0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty

ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1b0) and .wd(0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark

//==================================================

CHECKSUM: "3532547490 2073313596"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.wr_en_data_arb
Block 1 "494386457" "assign wr_en = de;"
Block 3 "1586513996" "assign gen_ro.unused_we = we;"
Block 4 "2453773718" "assign gen_ro.unused_wd = wd;"
Block 5 "3424138525" "assign gen_ro.unused_q = q;"

CHECKSUM: "3532547490 2073313596"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.wr_en_data_arb
Block 1 "494386457" "assign wr_en = de;"
Block 3 "1586513996" "assign gen_ro.unused_we = we;"
Block 4 "2453773718" "assign gen_ro.unused_wd = wd;"
Block 5 "3424138525" "assign gen_ro.unused_q = q;"

CHECKSUM: "3532547490 2073313596"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.wr_en_data_arb
Block 1 "494386457" "assign wr_en = de;"
Block 3 "1586513996" "assign gen_ro.unused_we = we;"
Block 4 "2453773718" "assign gen_ro.unused_wd = wd;"
Block 5 "3424138525" "assign gen_ro.unused_q = q;"

CHECKSUM: "3749827114 132761700"
ANNOTATION: "ModuleName: tlul_rsp_intg_gen"
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_rsp_intg_gen
Block 1 "461445014" "assign rsp_intg = tl_i.d_user.rsp_intg;"
Block 2 "2643129081" "assign data_intg = tl_i.d_user.data_intg;"

CHECKSUM: "1728783588 2573987063"
ANNOTATION: "ModuleName: tlul_adapter_reg"
ANNOTATION: "[TLUL_ADAPTER_REG] Word-aligned addr[1:0]=0 from axi_sub and matched wstrb mask from sub2tlul"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if
Block 30 "2014892424" "assign instr_error = (caliptra_prim_mubi_pkg::mubi4_test_invalid(tl_i.a_user.instr_type) | (caliptra_prim_mubi_pkg::mubi4_test_true_strict(tl_i.a_user.instr_type) & caliptra_prim_mubi_pkg::mubi4_test_false_loose(en_ifetch_i)));"

CHECKSUM: "130489891 3608551021"
ANNOTATION: "ModuleName: tlul_err"
ANNOTATION: "[TLUL_ERR] Word-aligned addr[1:0]=0 and sub2tlul PutFullData/wstrb encoding"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_err
Block 5 "2491734155" "assign instr_type_err = caliptra_prim_mubi_pkg::mubi4_test_invalid(tl_i.a_user.instr_type);"

//==================================================

CHECKSUM: "3532547490 3592535142"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=3,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_rxilvl.wr_en_data_arb
Condition 1 "505266581" "(we | de) 1 -1" (2 "01")

CHECKSUM: "3532547490 3592535142"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=3,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_txilvl.wr_en_data_arb
Condition 1 "505266581" "(we | de) 1 -1" (2 "01")

CHECKSUM: "1728783588 3785313510"
ANNOTATION: "ModuleName: tlul_adapter_reg"
ANNOTATION: "[TLUL_ADAPTER_REG] Word-aligned addr[1:0]=0 from axi_sub and matched wstrb mask from sub2tlul"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if
Condition 18 "3340270436" "(addr_align_err | malformed_meta_err | tl_err | instr_error | intg_error) 1 -1" (3 "00010")
Condition 18 "3340270436" "(addr_align_err | malformed_meta_err | tl_err | instr_error | intg_error) 1 -1" (5 "01000")
Condition 18 "3340270436" "(addr_align_err | malformed_meta_err | tl_err | instr_error | intg_error) 1 -1" (6 "10000")

CHECKSUM: "2937160916 1896776429"
ANNOTATION: "ModuleName: axi_sub_wr"
ANNOTATION: "[AXI_SUB_WR] Exclusive access disabled (EX_EN=0, lock=0, EXOKAY=2'b01 unreachable) and word-aligned addr[1:0]=0"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr
Condition 18 "4215928670" "((txn_allow && txn_ctx.lock) ? AXI_RESP_EXOKAY : AXI_RESP_OKAY) 1 -1" (2 "1")
Condition 19 "1180556428" "(txn_allow && txn_ctx.lock) 1 -1" (3 "11")

CHECKSUM: "130489891 378857456"
ANNOTATION: "ModuleName: tlul_err"
ANNOTATION: "[TLUL_ERR] Word-aligned addr[1:0]=0 and sub2tlul PutFullData/wstrb encoding"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_err
Condition 1 "4001409645" "(tl_i.a_address[1] ? ((~|(tl_i.a_mask & 4'b0011))) : ((~|(tl_i.a_mask & 4'b1100)))) 1 -1" (2 "1")
Condition 2 "1185432721" "(tl_i.a_address[1] ? ((&tl_i.a_mask[3:2])) : ((&tl_i.a_mask[1:0]))) 1 -1" (2 "1")
Condition 6 "3976953572" "(( ~ (opcode_allowed & a_config_allowed) ) | instr_wr_err | instr_type_err) 1 -1" (2 "001")
Condition 6 "3976953572" "(( ~ (opcode_allowed & a_config_allowed) ) | instr_wr_err | instr_type_err) 1 -1" (3 "010")
Condition 9 "3958044303" "((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData) | (tl_i.a_opcode == Get)) 1 -1" (1 "000")

//==================================================

CHECKSUM: "2398989739 1716024512"
ANNOTATION: "ModuleName: caliptra_prim_subreg_ext"
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_status_txlvl
Toggle d [7:6] "net d[7:0]"
Toggle ds [7:6] "logic ds[7:0]"
Toggle qs [7:6] "logic qs[7:0]"

CHECKSUM: "2398989739 1716024512"
ANNOTATION: "ModuleName: caliptra_prim_subreg_ext"
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_status_rxlvl
Toggle d [7] "net d[7:0]"
Toggle ds [7] "logic ds[7:0]"
Toggle qs [7] "logic qs[7:0]"

CHECKSUM: "2730301546 2550070695"
ANNOTATION: "ModuleName: skidbuffer"
ANNOTATION: "[SKIDBUFFER_WR_REQ] OPT_OUTREG=0 Boolean mutual exclusion and constant lock=0 (i_data[0]/o_data[0])"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.i_req_skd
Toggle i_data [0] "net i_data[85:0]"
Toggle o_data [0] "reg o_data[85:0]"

CHECKSUM: "2730301546 1030818833"
ANNOTATION: "ModuleName: skidbuffer ( parameter OPT_LOWPOWER=0,OPT_OUTREG=1,OPT_PASSTHROUGH=0,DW=10 ) "
ANNOTATION: "[SKIDBUFFER_WR_RSP] OPT_OUTREG=0 Boolean mutual exclusion and constant bresp[0]=0 (i_data[8]/o_data[8])"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_wr.i_rsp_skd
Toggle i_data [8] "net i_data[9:0]"
Toggle o_data [8] "reg o_data[9:0]"

CHECKSUM: "2730301546 3522678952"
ANNOTATION: "ModuleName: skidbuffer ( parameter OPT_LOWPOWER=0,OPT_OUTREG=0,OPT_PASSTHROUGH=0,DW=75 ) "
ANNOTATION: "[SKIDBUFFER_RD_DP] OPT_OUTREG=0 Boolean mutual exclusion and constant rresp[0]=0"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_rd.DATA_PIPELINE[0].i_dp_skd
Toggle i_data [1] "net i_data[74:0]"
Toggle o_data [1] "reg o_data[74:0]"

CHECKSUM: "3532547490 94569319"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 + DW=1,SwAccess=3,Mubi=0 + DW=1,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark.wr_en_data_arb
Toggle we "net we"
Toggle wd "net wd[0:0]"
Toggle de "net de"
Toggle wr_en "logic wr_en"

CHECKSUM: "3532547490 94569319"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 + DW=1,SwAccess=3,Mubi=0 + DW=1,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark.wr_en_data_arb
Toggle we "net we"
Toggle wd "net wd[0:0]"
Toggle de "net de"
Toggle wr_en "logic wr_en"

CHECKSUM: "3532547490 94569319"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=1,SwAccess=1,Mubi=0 + DW=1,SwAccess=3,Mubi=0 + DW=1,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty.wr_en_data_arb
Toggle we "net we"
Toggle wd "net wd[0:0]"
Toggle de "net de"
Toggle wr_en "logic wr_en"

CHECKSUM: "3532547490 2414609593"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=3,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_rxilvl.wr_en_data_arb
Toggle de "net de"
Toggle d [2:0] "net d[2:0]"

CHECKSUM: "3532547490 2414609593"
ANNOTATION: "ModuleName: caliptra_prim_subreg_arb ( parameter DW=3,SwAccess=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_txilvl.wr_en_data_arb
Toggle de "net de"
Toggle d [2:0] "net d[2:0]"

CHECKSUM: "3749827114 574992369"
ANNOTATION: "ModuleName: tlul_rsp_intg_gen"
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_rsp_intg_gen
Toggle tl_i.d_user.data_intg [6:0] "logic tl_i.d_user.data_intg[6:0]"
Toggle tl_i.d_user.rsp_intg [6:0] "logic tl_i.d_user.rsp_intg[6:0]"
Toggle tl_i.d_sink "logic tl_i.d_sink[0:0]"
Toggle tl_i.d_param [2:0] "logic tl_i.d_param[2:0]"
Toggle tl_i.d_opcode [2:1] "logic tl_i.d_opcode[2:0]"
Toggle tl_o.d_user.data_intg [6:0] "logic tl_o.d_user.data_intg[6:0]"
Toggle tl_o.d_user.rsp_intg [6:0] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_param [2:0] "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"

CHECKSUM: "3677688747 2915030263"
ANNOTATION: "ModuleName: axi2tlul"
ANNOTATION: "[AXI2TLUL] AXI-to-TLUL wrapper constant TL-UL tie-offs (a_param, d_param, d_sink, d_user, addr[1:0])"
INSTANCE: tb.dut.u_axi2tlul_uart
Toggle tl_o.a_user.instr_type [3:0] "logic tl_o.a_user.instr_type[3:0]"
Toggle tl_o.a_user.rsvd [2:0] "logic tl_o.a_user.rsvd[2:0]"
Toggle tl_o.a_address [1:0] "logic tl_o.a_address[31:0]"
Toggle tl_o.a_param [2:0] "logic tl_o.a_param[2:0]"
Toggle tl_o.a_opcode [1] "logic tl_o.a_opcode[2:0]"
Toggle tl_i.d_user.rsp_intg [6] "logic tl_i.d_user.rsp_intg[6:0]"
Toggle tl_i.d_sink "logic tl_i.d_sink[0:0]"
Toggle tl_i.d_param [2:0] "logic tl_i.d_param[2:0]"
Toggle tl_i.d_opcode [2:1] "logic tl_i.d_opcode[2:0]"

CHECKSUM: "4197951020 3713924239"
ANNOTATION: "ModuleName: caliptra_ss_uart_reg_top"
ANNOTATION: "[UART_REG_TOP] Register block constant TL-UL tie-offs, RO interrupt subregs, and internal integrity/one-hot checkers behind axi2tlul"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg
Toggle tl_i.a_user.instr_type [3:0] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd [2:0] "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_param [2:0] "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_param [2:0] "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"
Toggle reg2hw.rdata.q [7:0] "logic reg2hw.rdata.q[7:0]"
Toggle reg2hw.status.txfull.q "logic reg2hw.status.txfull.q"
Toggle reg2hw.status.rxfull.q "logic reg2hw.status.rxfull.q"
Toggle reg2hw.status.txempty.q "logic reg2hw.status.txempty.q"
Toggle reg2hw.status.txidle.q "logic reg2hw.status.txidle.q"
Toggle reg2hw.status.rxidle.q "logic reg2hw.status.rxidle.q"
Toggle reg2hw.status.rxempty.q "logic reg2hw.status.rxempty.q"
Toggle hw2reg.fifo_status.txlvl.d [7:6] "logic hw2reg.fifo_status.txlvl.d[7:0]"
Toggle hw2reg.fifo_status.rxlvl.d [7] "logic hw2reg.fifo_status.rxlvl.d[7:0]"
Toggle hw2reg.fifo_ctrl.rxilvl.de "logic hw2reg.fifo_ctrl.rxilvl.de"
Toggle hw2reg.fifo_ctrl.rxilvl.d [2:0] "logic hw2reg.fifo_ctrl.rxilvl.d[2:0]"
Toggle hw2reg.fifo_ctrl.txilvl.de "logic hw2reg.fifo_ctrl.txilvl.de"
Toggle hw2reg.fifo_ctrl.txilvl.d [2:0] "logic hw2reg.fifo_ctrl.txilvl.d[2:0]"
Toggle hw2reg.intr_state.tx_watermark.de "logic hw2reg.intr_state.tx_watermark.de"
Toggle hw2reg.intr_state.rx_watermark.de "logic hw2reg.intr_state.rx_watermark.de"
Toggle hw2reg.intr_state.tx_empty.de "logic hw2reg.intr_state.tx_empty.de"

CHECKSUM: "2082390543 3816842152"
ANNOTATION: "ModuleName: tlul_assert"
ANNOTATION: "[TLUL_ASSERT] Compliant single-beat 32-bit TL-UL bridge never triggers multi-beat or unrequested response antecedents"
INSTANCE: tb.dut.u_caliptra_ss_uart.tlul_assert_device
Toggle h2d.a_user.instr_type [3:0] "logic h2d.a_user.instr_type[3:0]"
Toggle h2d.a_user.rsvd [2:0] "logic h2d.a_user.rsvd[2:0]"
Toggle h2d.a_address [1:0] "logic h2d.a_address[31:0]"
Toggle h2d.a_param [2:0] "logic h2d.a_param[2:0]"
Toggle h2d.a_opcode [1] "logic h2d.a_opcode[2:0]"
Toggle d2h.d_user.rsp_intg [6] "logic d2h.d_user.rsp_intg[6:0]"
Toggle d2h.d_sink "logic d2h.d_sink[0:0]"
Toggle d2h.d_param [2:0] "logic d2h.d_param[2:0]"
Toggle d2h.d_opcode [2:1] "logic d2h.d_opcode[2:0]"

CHECKSUM: "2553605572 3311484983"
ANNOTATION: "ModuleName: sub2tlul"
ANNOTATION: "[SUB2TLUL] Single-outstanding TL-UL bridge: pending_txn blocks direct valid_get<->valid_put transitions; a_ready=1 and word-aligned addr[1:0]=0"
INSTANCE: tb.dut.u_axi2tlul_uart.i_sub2tlul
Toggle addr [1:0] "logic addr[31:0]"
Toggle tl_o.a_user.instr_type [3:0] "logic tl_o.a_user.instr_type[3:0]"
Toggle tl_o.a_user.rsvd [2:0] "logic tl_o.a_user.rsvd[2:0]"
Toggle tl_o.a_address [1:0] "logic tl_o.a_address[31:0]"
Toggle tl_o.a_param [2:0] "logic tl_o.a_param[2:0]"
Toggle tl_o.a_opcode [1] "logic tl_o.a_opcode[2:0]"
Toggle tl_i.d_user.rsp_intg [6] "logic tl_i.d_user.rsp_intg[6:0]"
Toggle tl_i.d_sink "logic tl_i.d_sink[0:0]"
Toggle tl_i.d_param [2:0] "logic tl_i.d_param[2:0]"
Toggle tl_i.d_opcode [2:1] "logic tl_i.d_opcode[2:0]"

CHECKSUM: "1728783588 886757705"
ANNOTATION: "ModuleName: tlul_adapter_reg"
ANNOTATION: "[TLUL_ADAPTER_REG] Word-aligned addr[1:0]=0 from axi_sub and matched wstrb mask from sub2tlul"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if
Toggle tl_i.a_user.instr_type [3:0] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd [2:0] "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_param [2:0] "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.data_intg [6:0] "logic tl_o.d_user.data_intg[6:0]"
Toggle tl_o.d_user.rsp_intg [6:0] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_param [2:0] "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"
Toggle en_ifetch_i "logic en_ifetch_i[3:0]"
Toggle intg_error_o "logic intg_error_o"
Toggle busy_i "net busy_i"

CHECKSUM: "784628221 4293694681"
ANNOTATION: "ModuleName: axi_sub_arb"
ANNOTATION: "[AXI_SUB_ARB] Preceding else-if (w_dv && !r_win) makes (r_dv=1, r_win=0) unreachable in else-if (r_dv && r_win); addr[1:0]=0"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_arb
Toggle addr [1:0] "logic addr[31:0]"

CHECKSUM: "2506603348 796268975"
ANNOTATION: "ModuleName: caliptra_ss_uart"
ANNOTATION: "[UART_TOP] Constant TL-UL bus fields from axi2tlul bridge"
INSTANCE: tb.dut.u_caliptra_ss_uart
Toggle tl_i.a_user.instr_type [3:0] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd [2:0] "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_param [2:0] "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"
Toggle tl_o.d_user.rsp_intg [6] "logic tl_o.d_user.rsp_intg[6:0]"
Toggle tl_o.d_sink "logic tl_o.d_sink[0:0]"
Toggle tl_o.d_param [2:0] "logic tl_o.d_param[2:0]"
Toggle tl_o.d_opcode [2:1] "logic tl_o.d_opcode[2:0]"
Toggle cio_tx_en_o "logic cio_tx_en_o"

CHECKSUM: "882443499 640784934"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=3,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_rxilvl
Toggle de "net de"
Toggle d [2:0] "net d[2:0]"

CHECKSUM: "882443499 640784934"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=3,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[REG_SUBREG] Register subreg with unconnected .qe() output port or constant tie-off in reg_top"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_ctrl_txilvl
Toggle de "net de"
Toggle d [2:0] "net d[2:0]"

CHECKSUM: "130489891 861170334"
ANNOTATION: "ModuleName: tlul_err"
ANNOTATION: "[TLUL_ERR] Word-aligned addr[1:0]=0 and sub2tlul PutFullData/wstrb encoding"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_err
Toggle tl_i.a_user.instr_type [3:0] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd [2:0] "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_param [2:0] "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"

CHECKSUM: "4211627521 2008937063"
ANNOTATION: "ModuleName: axi_sub"
ANNOTATION: "[AXI_SUB] AXI subordinate bridge constant bresp[0]/rresp[0] and word-aligned addr[1:0]=0"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub
Toggle addr [1:0] "logic addr[31:0]"

CHECKSUM: "2849835275 2310862966"
ANNOTATION: "ModuleName: caliptra_ss_uart_core"
ANNOTATION: "[UART_CORE] Structurally unreachable break_err&(break_st_q==BRK_CHK) (1,0), 1-bit enum default, 64-entry FIFO bit[7]=0, and unused reg2hw/hw2reg fields"
INSTANCE: tb.dut.u_caliptra_ss_uart.caliptra_ss_uart_core
Toggle reg2hw.rdata.q [7:0] "logic reg2hw.rdata.q[7:0]"
Toggle reg2hw.status.txfull.q "logic reg2hw.status.txfull.q"
Toggle reg2hw.status.rxfull.q "logic reg2hw.status.rxfull.q"
Toggle reg2hw.status.txempty.q "logic reg2hw.status.txempty.q"
Toggle reg2hw.status.txidle.q "logic reg2hw.status.txidle.q"
Toggle reg2hw.status.rxidle.q "logic reg2hw.status.rxidle.q"
Toggle reg2hw.status.rxempty.q "logic reg2hw.status.rxempty.q"
Toggle hw2reg.fifo_status.txlvl.d [7:6] "logic hw2reg.fifo_status.txlvl.d[7:0]"
Toggle hw2reg.fifo_status.rxlvl.d [7] "logic hw2reg.fifo_status.rxlvl.d[7:0]"
Toggle hw2reg.fifo_ctrl.rxilvl.de "logic hw2reg.fifo_ctrl.rxilvl.de"
Toggle hw2reg.fifo_ctrl.rxilvl.d [2:0] "logic hw2reg.fifo_ctrl.rxilvl.d[2:0]"
Toggle hw2reg.fifo_ctrl.txilvl.de "logic hw2reg.fifo_ctrl.txilvl.de"
Toggle hw2reg.fifo_ctrl.txilvl.d [2:0] "logic hw2reg.fifo_ctrl.txilvl.d[2:0]"
Toggle hw2reg.intr_state.tx_watermark.de "logic hw2reg.intr_state.tx_watermark.de"
Toggle hw2reg.intr_state.rx_watermark.de "logic hw2reg.intr_state.rx_watermark.de"
Toggle hw2reg.intr_state.tx_empty.de "logic hw2reg.intr_state.tx_empty.de"

//==================================================
// FSM Transition Exclusions (sub2tlul.sv:86-121)
//==================================================
// Reason:
// 1. Entering valid_get_txn or valid_put_txn requires tl_o.a_valid == 1'b1, which simultaneously
//    registers pending_txn <= 1'b1 on the same clock edge (sub2tlul.sv:108-109).
// 2. While in valid_get_txn or valid_put_txn, pending_txn == 1'b1 forces tl_o.a_valid = (dv & ~pending_txn) == 1'b0
//    (sub2tlul.sv:121), blocking the transition conditions (opcode == Get && tl_o.a_valid) and
//    ((opcode == PutFullData || opcode == PutPartialData) && tl_o.a_valid) at sub2tlul.sv:90-95.
// 3. In addition, hld == 1'b1 stalls axi_sub_arb (preventing write/opcode from flipping mid-transaction),
//    and u_reg_if asserts tl_i.d_valid == 1'b1 on the next cycle, returning cur_txn to no_txn (sub2tlul.sv:96-101).
CHECKSUM: "2553605572 984500570"
ANNOTATION: "ModuleName: sub2tlul"
ANNOTATION: "[UNR_FSM_TRANS] In sub2tlul.sv:86-121, entering valid_get_txn or valid_put_txn latches pending_txn=1, which forces tl_o.a_valid=(dv & ~pending_txn)=0 and hld=1 until tl_i.d_valid returns cur_txn to no_txn; direct transitions between valid_get_txn and valid_put_txn without passing through no_txn are structurally impossible."
INSTANCE: tb.dut.u_axi2tlul_uart.i_sub2tlul
Fsm cur_txn "984500570"
ANNOTATION: "Unreachable: while cur_txn==valid_get_txn, pending_txn==1 forces tl_o.a_valid==0 and hld==1 locks axi_sub_arb until AccessAckData returns cur_txn to no_txn"
Transition valid_get_txn->valid_put_txn "1->2"
ANNOTATION: "Unreachable: while cur_txn==valid_put_txn, pending_txn==1 forces tl_o.a_valid==0 and hld==1 locks axi_sub_arb until AccessAck returns cur_txn to no_txn"
Transition valid_put_txn->valid_get_txn "2->1"


