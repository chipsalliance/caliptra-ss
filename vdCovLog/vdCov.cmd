verdiWindowResize -win $_vdCoverage_1 "380" "129" "2689" "838"
gui_set_pref_value -category {coveragesetting} -key {geninfodumping} -value 1
gui_exclusion -set_force true
gui_assert_mode -mode flat
gui_class_mode -mode hier
gui_excl_mgr_flat_list -on  0
gui_covdetail_select -id  CovDetail.1   -name   Line
verdiWindowWorkMode -win $_vdCoverage_1 -coverageAnalysis
gui_open_cov  -hier ../../scratch/v-pnasahl/simland/caliptra_ss_top_tb/caliptra_ss_lcc_st_trans/20250426.112250/coverage.vdb -testdir {} -test {../../scratch/v-pnasahl/simland/caliptra_ss_top_tb/caliptra_ss_lcc_st_trans/20250426.112250/coverage/test} -merge MergedTest -db_max_tests 10 -fsm transition
gui_covtable_show -show  { Function Groups } -id  CoverageTable.1  -test  MergedTest
gui_list_expand -id  CoverageTable.1   -list {covtblFGroupsList} /ahb_slv_sif::ahb_slv_sif_cov_grp
gui_list_expand -id  CoverageTable.1   -list {covtblFGroupsList} /ahb_slv_sif::ahb_slv_sif_cov_grp
gui_list_expand -id  CoverageTable.1   -list {covtblFGroupsList} /ahb_lite_2to1_mux::ahb_lite_2to1_mux_cov_grp
gui_list_expand -id  CoverageTable.1   -list {covtblFGroupsList} /ahb_lite_2to1_mux::ahb_lite_2to1_mux_cov_grp
gui_list_set_filter -id CoverageTable.1 -list {covtblFGroupsList} -text {*lc_ctrl_cov_if*}
gui_list_expand -id  CoverageTable.1   -list {covtblFGroupsList} /caliptra_ss_top_tb.caliptra_ss_dut.u_lc_ctrl.i_lc_ctrl_cov_if::lc_ctrl_state_transition_cg
gui_list_select -id CoverageTable.1 -list covtblFGroupsList { caliptra_ss_top_tb.caliptra_ss_dut.u_lc_ctrl.i_lc_ctrl_cov_if::lc_ctrl_state_transition_cg.lc_state_transition_cp   }
gui_list_action -id  CoverageTable.1 -list {covtblFGroupsList} caliptra_ss_top_tb.caliptra_ss_dut.u_lc_ctrl.i_lc_ctrl_cov_if::lc_ctrl_state_transition_cg.lc_state_transition_cp  -column {Group} 
vdCovExit -noprompt
