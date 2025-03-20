
initial begin
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.i3c.i3c.xhci.i3c_csr.ERR_HWIF_IN); // FIXME - remove https://github.com/chipsalliance/i3c-core/issues/22 

    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[0].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[0].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[10].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[11].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[12].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[13].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[13].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[14].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[15].gen_lifecycle.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[15].gen_lifecycle.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[1].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[1].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[2].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[2].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[3].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[3].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[4].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[4].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[5].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[5].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[6].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[7].gen_buffered.u_part_buf.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[7].gen_buffered.u_part_buf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[8].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.gen_partitions[9].gen_unbuffered.u_part_unbuf.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp.u_reg_top.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_dai.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_dai.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lci.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lci.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lfsr_timer.u_prim_count_cnsty.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lfsr_timer.u_prim_count_integ.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lfsr_timer.u_prim_double_lfsr.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_lfsr_timer.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_scrmbl.u_prim_count.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_otp_ctrl_scrmbl.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_reg_core.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_tlul_lc_gate.u_state_regs.AssertConnected_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/148


    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_edn_arb.ValidKnown_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/156 
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_edn_arb.IdxKnown_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/156
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.u_otp_ctrl.u_edn_arb.GrantKnown_A); // FIXME - remove https://github.com/chipsalliance/caliptra-ss/issues/156

    $assertoff(0, caliptra_ss_top_tb.CPTRA_AXI_RD_32BITcptra_ss_mcu_rom_s_axi_if); // FIXME - https://github.com/chipsalliance/caliptra-ss/issues/157

end
