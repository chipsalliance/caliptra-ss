// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Coverage exclusion file for Caliptra SS UART DV
// Format Version: 2
// ExclMode: default

CHECKSUM: "882443499 223073768"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark
Block 7 "1375076151" "assign qe = wr_en;"

CHECKSUM: "882443499 223073768"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark
Block 7 "1375076151" "assign qe = wr_en;"

CHECKSUM: "882443499 223073768"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty
Block 7 "1375076151" "assign qe = wr_en;"
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
ANNOTATION: "[TLUL_RSP_INTG_GEN] Passthrough response integrity assignment when EnableRspIntgGen=0 in u_reg_if"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_rsp_intg_gen
Block 1 "461445014" "assign rsp_intg = tl_i.d_user.rsp_intg;"
Block 2 "2643129081" "assign data_intg = tl_i.d_user.data_intg;"

//==================================================

CHECKSUM: "882443499 3274445021"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark
Condition 1 "2397158838" "(wr_en ? wr_data : qs) 1 -1" (1 "0")

CHECKSUM: "882443499 3274445021"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark
Condition 1 "2397158838" "(wr_en ? wr_data : qs) 1 -1" (1 "0")

CHECKSUM: "882443499 3274445021"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty
Condition 1 "2397158838" "(wr_en ? wr_data : qs) 1 -1" (1 "0")
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
ANNOTATION: "[TLUL_ADAPTER_REG] Word-aligned addr[1:0]=0 from axi_sub, matched wstrb mask from sub2tlul, and instr_type!=MuBi4True (sub2tlul ties MuBi4False so instr_error never asserts independently of malformed_meta_err)"
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
ANNOTATION: "[TLUL_ERR] Word-aligned addr[1:0]=0, sub2tlul PutFullData/wstrb encoding, and instr_type!=MuBi4True (sub2tlul ties MuBi4False so instr_wr_err is constant 0)"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_err
Condition 1 "4001409645" "(tl_i.a_address[1] ? ((~|(tl_i.a_mask & 4'b0011))) : ((~|(tl_i.a_mask & 4'b1100)))) 1 -1" (2 "1")
Condition 2 "1185432721" "(tl_i.a_address[1] ? ((&tl_i.a_mask[3:2])) : ((&tl_i.a_mask[1:0]))) 1 -1" (2 "1")
Condition 6 "3976953572" "(( ~ (opcode_allowed & a_config_allowed) ) | instr_wr_err | instr_type_err) 1 -1" (3 "010")
Condition 9 "3958044303" "((tl_i.a_opcode == PutFullData) | (tl_i.a_opcode == PutPartialData) | (tl_i.a_opcode == Get)) 1 -1" (1 "000")

CHECKSUM: "91523474 2773930708"
ANNOTATION: "ModuleName: caliptra_prim_secded_inv_64_57_dec"
ANNOTATION: "[TLUL_CMD_SECDED_CONST_BITS] In tlul_cmd_intg_chk.sv:25, H2DCmdMaxWidth'(cmd) zero-extends 43-bit tl_h2d_cmd_intg_t to 57 bits (data_i[56:43]=14'b0); third_party/caliptra-rtl/src/axi/rtl/axi_sub_wr.sv:252 and axi_sub_rd.sv:208 enforce word-aligned addr[1:0]=2'b00 (passed through sub2tlul.sv:120 to data_i[8:7]); and sub2tlul.sv:70,116,156 hard-tie a_opcode[1]=data_i[5]=0 and instr_type=MuBi4False=4'b1001 (data_i[42]=1, data_i[41:40]=2'b00, data_i[39]=1 except single-bit fault syndrome 7'h57). All active payload bits and err_o[1] double-bit detection (line 85) remain un-excluded."
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_chk.u_chk
Condition 11 "3514747152" "((syndrome_o == 7'h0d) ^ data_i[5]) 1 -1" (2 "01")
Condition 11 "3514747152" "((syndrome_o == 7'h0d) ^ data_i[5]) 1 -1" (4 "11")
Condition 15 "2990830276" "((syndrome_o == 7'h25) ^ data_i[7]) 1 -1" (2 "01")
Condition 15 "2990830276" "((syndrome_o == 7'h25) ^ data_i[7]) 1 -1" (4 "11")
Condition 17 "1646732908" "((syndrome_o == 7'h45) ^ data_i[8]) 1 -1" (2 "01")
Condition 17 "1646732908" "((syndrome_o == 7'h45) ^ data_i[8]) 1 -1" (4 "11")
Condition 79 "880200189" "((syndrome_o == 7'h57) ^ data_i[39]) 1 -1" (1 "00")
Condition 81 "104466046" "((syndrome_o == 7'h67) ^ data_i[40]) 1 -1" (2 "01")
Condition 81 "104466046" "((syndrome_o == 7'h67) ^ data_i[40]) 1 -1" (4 "11")
Condition 83 "2094438798" "((syndrome_o == 7'h3b) ^ data_i[41]) 1 -1" (2 "01")
Condition 83 "2094438798" "((syndrome_o == 7'h3b) ^ data_i[41]) 1 -1" (4 "11")
Condition 85 "1378466364" "((syndrome_o == 7'h5b) ^ data_i[42]) 1 -1" (1 "00")
Condition 85 "1378466364" "((syndrome_o == 7'h5b) ^ data_i[42]) 1 -1" (3 "10")
Condition 87 "3676067614" "((syndrome_o == 7'h6b) ^ data_i[43]) 1 -1" (2 "01")
Condition 87 "3676067614" "((syndrome_o == 7'h6b) ^ data_i[43]) 1 -1" (4 "11")
Condition 89 "1626632997" "((syndrome_o == 7'h73) ^ data_i[44]) 1 -1" (2 "01")
Condition 89 "1626632997" "((syndrome_o == 7'h73) ^ data_i[44]) 1 -1" (4 "11")
Condition 91 "3339657325" "((syndrome_o == 7'h3d) ^ data_i[45]) 1 -1" (2 "01")
Condition 91 "3339657325" "((syndrome_o == 7'h3d) ^ data_i[45]) 1 -1" (4 "11")
Condition 93 "3924820959" "((syndrome_o == 7'h5d) ^ data_i[46]) 1 -1" (2 "01")
Condition 93 "3924820959" "((syndrome_o == 7'h5d) ^ data_i[46]) 1 -1" (4 "11")
Condition 95 "1623584509" "((syndrome_o == 7'h6d) ^ data_i[47]) 1 -1" (2 "01")
Condition 95 "1623584509" "((syndrome_o == 7'h6d) ^ data_i[47]) 1 -1" (4 "11")
Condition 97 "733446940" "((syndrome_o == 7'h75) ^ data_i[48]) 1 -1" (2 "01")
Condition 97 "733446940" "((syndrome_o == 7'h75) ^ data_i[48]) 1 -1" (4 "11")
Condition 99 "1337360872" "((syndrome_o == 7'h79) ^ data_i[49]) 1 -1" (2 "01")
Condition 99 "1337360872" "((syndrome_o == 7'h79) ^ data_i[49]) 1 -1" (4 "11")
Condition 101 "794112705" "((syndrome_o == 7'h3e) ^ data_i[50]) 1 -1" (2 "01")
Condition 101 "794112705" "((syndrome_o == 7'h3e) ^ data_i[50]) 1 -1" (4 "11")
Condition 103 "4015714319" "((syndrome_o == 7'h5e) ^ data_i[51]) 1 -1" (2 "01")
Condition 103 "4015714319" "((syndrome_o == 7'h5e) ^ data_i[51]) 1 -1" (4 "11")
Condition 105 "2292186193" "((syndrome_o == 7'h6e) ^ data_i[52]) 1 -1" (2 "01")
Condition 105 "2292186193" "((syndrome_o == 7'h6e) ^ data_i[52]) 1 -1" (4 "11")
Condition 107 "2321080821" "((syndrome_o == 7'h76) ^ data_i[53]) 1 -1" (2 "01")
Condition 107 "2321080821" "((syndrome_o == 7'h76) ^ data_i[53]) 1 -1" (4 "11")
Condition 109 "10578038" "((syndrome_o == 7'h7a) ^ data_i[54]) 1 -1" (2 "01")
Condition 109 "10578038" "((syndrome_o == 7'h7a) ^ data_i[54]) 1 -1" (4 "11")
Condition 111 "57810203" "((syndrome_o == 7'h7c) ^ data_i[55]) 1 -1" (2 "01")
Condition 111 "57810203" "((syndrome_o == 7'h7c) ^ data_i[55]) 1 -1" (4 "11")
Condition 113 "3364043580" "((syndrome_o == 7'h7f) ^ data_i[56]) 1 -1" (2 "01")
Condition 113 "3364043580" "((syndrome_o == 7'h7f) ^ data_i[56]) 1 -1" (4 "11")

//==================================================

CHECKSUM: "2398989739 1716024512"
ANNOTATION: "ModuleName: caliptra_prim_subreg_ext"
ANNOTATION: "[FIFO_STATUS_SUBREG] Upper txlvl[7:6] bits are structurally 0 because TxFifoDepth = 32 (max occupancy 8'h20)"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_fifo_status_txlvl
Toggle d [7:6] "net d[7:0]"
Toggle ds [7:6] "logic ds[7:0]"
Toggle qs [7:6] "logic qs[7:0]"

CHECKSUM: "2398989739 1716024512"
ANNOTATION: "ModuleName: caliptra_prim_subreg_ext"
ANNOTATION: "[FIFO_STATUS_SUBREG] Upper rxlvl[7] bit is structurally 0 because RxFifoDepth = 64 (max occupancy 8'h40)"
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
ANNOTATION: "[SKIDBUFFER_WR_RSP] OPT_OUTREG=1 registered output mode and constant bresp[0]=0 (i_data[8]/o_data[8])"
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
ANNOTATION: "[TLUL_RSP_INTG_GEN] Tied-off response integrity and unused D-channel fields in u_reg_if.u_rsp_intg_gen"
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
ANNOTATION: "[UART_REG_TOP] Structurally constant TL-UL tie-offs from axi2tlul (instr_type[3:1]=3'b100 with bit [0] toggled by sec_cm fault test, rsvd=0, addr[1:0]=0, param=0, sink=0, rsp_intg[6] over 51'b0-padded header), unused RO reg2hw.*.q nets, FIFO-depth-bounded txlvl[7:6]/rxlvl[7] MSBs, and constant de=1'b1 on SwAccessRO status subregs"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg
Toggle tl_i.a_user.instr_type [3:1] "logic tl_i.a_user.instr_type[3:0]"
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
ANNOTATION: "[TLUL_ASSERT] Structurally constant TL-UL tie-offs from axi2tlul (instr_type[3:1]=3'b100 with bit [0] toggled by sec_cm fault test, rsvd=0, addr[1:0]=0, a_param=0, a_opcode[1]=0, rsp_intg[6] over 51'b0-padded header, d_sink=0, d_param=0, d_opcode[2:1]=0)"
INSTANCE: tb.dut.u_caliptra_ss_uart.tlul_assert_device
Toggle h2d.a_user.instr_type [3:1] "logic h2d.a_user.instr_type[3:0]"
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
ANNOTATION: "[TLUL_ADAPTER_REG] Structurally constant TL-UL tie-offs (instr_type[3:1]=3'b100 with bit [0] toggled by sec_cm fault test, rsvd=0, addr[1:0]=0, param=0, sink=0, d_user.*_intg=0 with EnableRspIntgGen=0), .en_ifetch_i(MuBi4False), .busy_i(1'b0), and intg_error_o hard-tied 1'b0 because CmdIntgCheck=0 (tlul_adapter_reg.sv:23,193-196)"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if
Toggle tl_i.a_user.instr_type [3:1] "logic tl_i.a_user.instr_type[3:0]"
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
ANNOTATION: "[AXI_SUB_ARB] Word-aligned 32-bit CSR transfers tie addr[1:0]=2'b00 inside axi_sub_arb"
INSTANCE: tb.dut.u_axi2tlul_uart.i_axi_sub.i_axi_sub_arb
Toggle addr [1:0] "logic addr[31:0]"

CHECKSUM: "2506603348 796268975"
ANNOTATION: "ModuleName: caliptra_ss_uart"
ANNOTATION: "[UART_TOP] Constant TL-UL bus fields from axi2tlul bridge (instr_type[3:1]=3'b100; bit [0] toggled by sec_cm fault test)"
INSTANCE: tb.dut.u_caliptra_ss_uart
Toggle tl_i.a_user.instr_type [3:1] "logic tl_i.a_user.instr_type[3:0]"
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
ANNOTATION: "[TLUL_ERR] Word-aligned addr[1:0]=0, instr_type[3:1]=3'b100 (bit [0] toggled by sec_cm fault test), and sub2tlul PutFullData/wstrb encoding"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_reg_if.u_err
Toggle tl_i.a_user.instr_type [3:1] "logic tl_i.a_user.instr_type[3:0]"
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
ANNOTATION: "[UART_CORE] Unused RO reg2hw.rdata/status .q nets, FIFO-depth-bounded txlvl[7:6] (max 32) and rxlvl[7] (max 64) MSBs, and constant hw2reg fifo_ctrl/status-intr .de/.d tie-offs"
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

CHECKSUM: "882443499 2704308791"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark
Toggle de "net de"
Toggle qe "logic qe"

CHECKSUM: "882443499 2704308791"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark
Toggle de "net de"
Toggle qe "logic qe"

CHECKSUM: "882443499 2704308791"
ANNOTATION: "ModuleName: caliptra_prim_subreg ( parameter DW=1,SwAccess=1,RESVAL,Mubi=0 + DW=1,SwAccess=3,RESVAL=0,Mubi=0 + DW=1,SwAccess=0,RESVAL=0,Mubi=0 ) "
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty
Toggle de "net de"
Toggle qe "logic qe"

CHECKSUM: "3799604519 2942690021"
ANNOTATION: "ModuleName: tlul_cmd_intg_chk"
ANNOTATION: "[TLUL_CMD_INTG_CHK] Constant TL-UL A-channel tie-offs from axi2tlul bridge (instr_type[3:1]=3'b100; bit [0] toggled by sec_cm fault test)"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_chk
Toggle tl_i.a_user.instr_type [3:1] "logic tl_i.a_user.instr_type[3:0]"
Toggle tl_i.a_user.rsvd [2:0] "logic tl_i.a_user.rsvd[2:0]"
Toggle tl_i.a_address [1:0] "logic tl_i.a_address[31:0]"
Toggle tl_i.a_param [2:0] "logic tl_i.a_param[2:0]"
Toggle tl_i.a_opcode [1] "logic tl_i.a_opcode[2:0]"

//==================================================

CHECKSUM: "882443499 3554514034"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_watermark
Branch 0 "3759852512" "wr_en" (1) "wr_en 0"
Branch 1 "1017474648" "(!rst_ni)" (2) "(!rst_ni) 0,0"

CHECKSUM: "882443499 3554514034"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_rx_watermark
Branch 0 "3759852512" "wr_en" (1) "wr_en 0"
Branch 1 "1017474648" "(!rst_ni)" (2) "(!rst_ni) 0,0"

CHECKSUM: "882443499 3554514034"
ANNOTATION: "ModuleName: caliptra_prim_subreg"
ANNOTATION: "[RO_INTR_SUBREG] Status-type RO interrupt subreg with .we(1'b0) and .wd('0) tied off in reg_top and constant de=1'b1"
INSTANCE: tb.dut.u_caliptra_ss_uart.u_reg.u_intr_state_tx_empty
Branch 0 "3759852512" "wr_en" (1) "wr_en 0"
Branch 1 "1017474648" "(!rst_ni)" (2) "(!rst_ni) 0,0"
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


