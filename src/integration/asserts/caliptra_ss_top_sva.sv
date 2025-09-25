// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

`include "caliptra_ss_top_tb_path_defines.svh"
`include "caliptra_ss_includes.svh"
`include "caliptra_prim_assert.sv"

module caliptra_ss_top_sva
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  ();

`ifdef CALIPTRA_ASSERT_DEFAULT_CLK
`undef CALIPTRA_ASSERT_DEFAULT_CLK
`define CALIPTRA_ASSERT_DEFAULT_CLK `CPTRA_SS_TOP_PATH.u_otp_ctrl.clk_i
`endif

`ifdef CALIPTRA_ASSERT_DEFAULT_RST
`undef CALIPTRA_ASSERT_DEFAULT_RST
`define CALIPTRA_ASSERT_DEFAULT_RST !`CPTRA_SS_TOP_PATH.u_otp_ctrl.rst_ni
`endif

  ////////////////////////////////////////////////////
  // fuse_ctrl_filter
  ////////////////////////////////////////////////////

  // The fuse_ctrl access control filter must discard an AXI write request when
  // the access control policy is violated.
  `CALIPTRA_ASSERT(FcAxiFilterDiscard_A,
    ((`FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awvalid) &&
     (`FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awaddr == 32'h7000_0060) &&
     (`FC_PATH.dai_addr > 12'h040 && `FC_PATH.dai_addr < 12'h0D0) &&
     (`FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser == `CPTRA_SS_TB_TOP_NAME.cptra_ss_strap_mcu_lsu_axi_user_i))
     |-> ##2
     `FC_PATH.discard_fuse_write)

  // When the fuse_ctrl access control filter discards an AXI write request, the DAI
  // must signal a recoverable AccessError.
  `CALIPTRA_ASSERT(FcAxiFilterDaiAccessError_A,
    ($fell(`FC_PATH.discard_fuse_write)) |-> otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError)

  //WDT checks:
  cascade_wdt_t1_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.timer1_restart && `MCI_WDT_PATH.timer1_en && !`MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t1_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart on pet");

  cascade_wdt_t2_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.timer2_restart && !`MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t2_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart on pet");

  cascade_wdt_t1_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.i_wdt.wdt_timer1_timeout_serviced_qual && `MCI_WDT_PATH.timer1_en && !`MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t2_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart after interrupt service");

  cascade_wdt_t2_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.i_wdt.wdt_timer2_timeout_serviced_qual && !`MCI_WDT_PATH.timer2_en) |=> (`MCI_WDT_PATH.i_wdt.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart after interrupt service");

  independent_wdt_t1_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.timer1_restart && `MCI_WDT_PATH.timer1_en && `MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t1_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart on pet");

  independent_wdt_t2_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.timer2_restart && `MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t2_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart on pet");

  independent_wdt_t1_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.i_wdt.wdt_timer1_timeout_serviced_qual && `MCI_WDT_PATH.timer1_en && `MCI_WDT_PATH.timer2_en && !`MCI_WDT_PATH.t2_timeout) |=> (`MCI_WDT_PATH.i_wdt.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart after interrupt service");

  independent_wdt_t2_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`MCI_WDT_PATH.i_wdt.wdt_timer2_timeout_serviced_qual && `MCI_WDT_PATH.timer2_en) |=> (`MCI_WDT_PATH.i_wdt.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart after interrupt service");

  wdt_status_t1_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TB_TOP_NAME.cptra_ss_rst_b_i)
    $rose(`MCI_WDT_PATH.t1_timeout) |=> $rose(`MCI_PATH.mci_reg_hwif_out.WDT_STATUS.t1_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t1 expiry!");

  wdt_status_t2_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TB_TOP_NAME.cptra_ss_rst_b_i)
    $rose(`MCI_WDT_PATH.t2_timeout) |=> $rose(`MCI_PATH.mci_reg_hwif_out.WDT_STATUS.t2_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t2 expiry!");



  // Check that a rollback (i.e. transition to a lower numbered state) never occurs.
  property lcc_state_no_rollback_transition;
    @(posedge `LCC_PATH.u_lc_ctrl_fsm.clk_i)
      disable iff (`LCC_PATH.u_lc_ctrl_fsm.rst_ni || !`LCC_PATH.u_lc_ctrl_fsm.init_done_o)
      // Cast the states to unsigned so that the ordering can be compared.
      (`LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_cmd_i && (`LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_target_i <=
       `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.dec_lc_state_i));
  endproperty

  assert property (lcc_state_no_rollback_transition)
    else $display("SVA ERROR: Rollback transition detected in LCC: current state = %0d, next state = %0d",
      `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_target_i,
      `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.dec_lc_state_i);

  // Check that a transition from PROD_END to RMA is prohibited.
  property no_prod_end_to_rma_transition;
    @(posedge `LCC_PATH.u_lc_ctrl_fsm.clk_i)
      disable iff (`LCC_PATH.u_lc_ctrl_fsm.rst_ni)
      ( `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_cmd_i
          && (`LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.dec_lc_state_i == {DecLcStateNumRep{DecLcStProdEnd}} )
          |->   ( `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_target_i != {DecLcStateNumRep{DecLcStRma}} ));
  endproperty

  assert property (no_prod_end_to_rma_transition)
    else $display("SVA ERROR: Invalid transition from PROD_END to RMA detected.");

  property Allow_PPD_check_in_LCC;
    @(posedge `LCC_PATH.clk_i)
      disable iff (!`LCC_PATH.rst_ni || `FC_LCC_TB_SERV_PATH.disable_lcc_sva)
      ($rose(`LCC_PATH.u_lc_ctrl_fsm.trans_cmd_i)
        && (`LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.dec_lc_state_i != {DecLcStateNumRep{DecLcStScrap}})
        && (`LCC_PATH.u_lc_ctrl_fsm.trans_target_i == {DecLcStateNumRep{DecLcStRma}}
            || `LCC_PATH.u_lc_ctrl_fsm.trans_target_i == {DecLcStateNumRep{DecLcStScrap}})
        && (`LCC_PATH.trans_success_q)
        |-> `LCC_PATH.Allow_RMA_or_SCRAP_on_PPD);
  endproperty

  assert property (Allow_PPD_check_in_LCC)
    else $display("SVA ERROR: Allow_RMA_or_SCRAP_on_PPD was not asserted for SCRAP and RMA.");


  //Error handling
  mci_error_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    (`MCI_REG_TOP_PATH.nmi_intr |=> `MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_FATAL.nmi_pin) and (`MCI_REG_TOP_PATH.mcu_sram_double_ecc_error |=> `MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_ecc_unc) and (`MCI_REG_TOP_PATH.mcu_sram_dmi_axi_collision_error |=> `MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision)
  ) else $display("SVA ERROR: MCI HW ERROR FATAL reg is not set correctly");

  mci_error_fatal_cold_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i |-> (`MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_FATAL=='h0))
  ) else $display("SVA ERROR: MCI HW ERROR FATAL is expected to reset on cold reset");

  mci_error_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (!`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i)
    ((~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i & `CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i) |-> ($stable(`MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_FATAL)[*5]))
  ) else $display("SVA ERROR: MCI HW ERROR FATAL is expected to remain unchanged on warm reset");

  all_error_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_nmi_pin & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_dmi_axi_collision) & (`MCI_REG_TOP_PATH.nmi_intr | `MCI_REG_TOP_PATH.mcu_sram_dmi_axi_collision_error) & `MCI_REG_TOP_PATH.mci_intr |=> ~`MCI_REG_TOP_PATH.all_error_fatal[*5])
    and ((&`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_fw_error_fatal_mask.mask & |`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_FATAL.error_code) |=> ~`MCI_REG_TOP_PATH.all_error_fatal[*5])
  ) else $display("SVA ERROR: all_error_fatal is asserted unexpectedly");

  all_error_fatal_sram_doublebit_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_ecc_unc) & `MCI_REG_TOP_PATH.mcu_sram_double_ecc_error & `MCI_REG_TOP_PATH.cif_resp_if.error |=> ~`MCI_REG_TOP_PATH.all_error_fatal[*5])
  ) else $display("SVA ERROR: all_error_fatal for mcu_sram_ecc_unc is asserted unexpectedly");

  //----------------------------------------------
  mci_error_non_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    (`MCI_REG_TOP_PATH.mbox0_sram_double_ecc_error |=> `MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox0_ecc_unc) and (`MCI_REG_TOP_PATH.mbox1_sram_double_ecc_error |=> `MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox1_ecc_unc)
  ) else $display("SVA ERROR: MCI HW ERROR NON FATAL reg is not set correctly");

  mci_error_non_fatal_cold_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i |-> (`MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_NON_FATAL=='h0))
  ) else $display("SVA ERROR: MCI HW ERROR NON FATAL is expected to reset on cold reset");

  mci_error_non_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (!`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i)
    ((~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i & `CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i) |-> ($stable(`MCI_REG_TOP_PATH.mci_reg_hwif_out.HW_ERROR_NON_FATAL)[*5]))
  ) else $display("SVA ERROR: MCI HW ERROR NON FATAL is expected to remain unchanged on warm reset");

  all_error_non_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox0_ecc_unc & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox1_ecc_unc) & (`MCI_REG_TOP_PATH.mbox0_sram_double_ecc_error | `MCI_REG_TOP_PATH.mbox1_sram_double_ecc_error) & `MCI_REG_TOP_PATH.mci_intr |=> ~`MCI_REG_TOP_PATH.all_error_non_fatal[*5]) and
    ((&`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_fw_error_non_fatal_mask.mask & |`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code) |=> ~`MCI_REG_TOP_PATH.all_error_non_fatal[*5])
  ) else $display("SVA ERROR: all_error_non_fatal is asserted unexpectedly");

  //----------------------------------------------
  all_error_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`MCI_REG_TOP_PATH.mci_rst_b |-> ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o)
  ) else $display("SVA ERROR: all_error_fatal is not reset correctly after a warm reset");

  all_error_non_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`MCI_REG_TOP_PATH.mci_rst_b |-> ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o)
  ) else $display("SVA ERROR: all_error_non_fatal is not reset correctly after a warm reset");

  //----------------------------------------------
  agg_all_error_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    (((`CPTRA_SS_TOP_PATH.cptra_error_fatal & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal0) |
     (`CPTRA_SS_TOP_PATH.mcu_dccm_ecc_double_error & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal6) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[0] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal12) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[1] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal13) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[2] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal14) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[0]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal18) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[1]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal19) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[2]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal20) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[3]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal21) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[4]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal22) |
     (`CPTRA_SS_TOP_PATH.fc_intr_otp_error   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal23) |
     (`CPTRA_SS_TOP_PATH.i3c_escalated_reset & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal24) |
     (`CPTRA_SS_TOP_PATH.i3c_peripheral_reset & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal25)

    ) |=> ##2 `CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o)
  ) else $display("SVA ERROR: AGG all_error_fatal is not set correctly");

  agg_all_error_non_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i)
    (((`CPTRA_SS_TOP_PATH.cptra_error_non_fatal & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal0) |
     (`CPTRA_SS_TOP_PATH.mcu_dccm_ecc_single_error & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal6) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[0] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal12) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[1] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal13) |
     (`CPTRA_SS_TOP_PATH.lc_alerts_o[2] & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal14) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[0]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal18) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[1]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal19) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[2]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal20) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[3]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal21) |
     (`CPTRA_SS_TOP_PATH.fc_alerts[4]   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal22) |
     (`CPTRA_SS_TOP_PATH.fc_intr_otp_error   & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal23) |
     (`CPTRA_SS_TOP_PATH.i3c_escalated_reset & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal24) |
     (`CPTRA_SS_TOP_PATH.i3c_peripheral_reset & ~`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal25)

    ) |=> ##2 `CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o)
  ) else $display("SVA ERROR: AGG all_error_non_fatal is not set correctly");

  //----------------------------------------------
  mci_fw_error_fatal_cold_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i |-> (`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_FATAL=='h0))
  ) else $display("SVA ERROR: MCI FW ERROR FATAL is expected to reset on cold reset");

  mci_fw_error_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (!`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i)
    ((~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i & `CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i) |-> ($stable(`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_FATAL)[*5]))
  ) else $display("SVA ERROR: MCI FW ERROR FATAL is expected to remain unchanged on warm reset");

  mci_fw_error_non_fatal_cold_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (~`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i |-> (`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_NON_FATAL=='h0))
  ) else $display("SVA ERROR: MCI FW ERROR NON FATAL is expected to reset on cold reset");

  mci_fw_error_non_fatal_warm_rst_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (!`CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i)
    ((~`CPTRA_SS_TOP_PATH.cptra_ss_rst_b_i & `CPTRA_SS_TOP_PATH.cptra_ss_pwrgood_i) |-> ($stable(`MCI_REG_TOP_PATH.mci_reg_hwif_out.FW_ERROR_NON_FATAL)[*5]))
  ) else $display("SVA ERROR: MCI FW ERROR NON FATAL is expected to remain unchanged on warm reset");

  ////////////////////////////////////////////////////
  // fuse_ctrl provisioning
  ////////////////////////////////////////////////////

  // XXX: Maybe put this in a life-cycle package.
  function dec_lc_state_e decode_lc_state(lc_state_e lc_state);
    unique case (lc_state)
      LcStRaw:           return DecLcStRaw;
      LcStTestUnlocked0: return DecLcStTestUnlocked0;
      LcStTestLocked0:   return DecLcStTestLocked0;
      LcStTestUnlocked1: return DecLcStTestUnlocked1;
      LcStTestLocked1:   return DecLcStTestLocked1;
      LcStTestUnlocked2: return DecLcStTestUnlocked2;
      LcStTestLocked2:   return DecLcStTestLocked2;
      LcStTestUnlocked3: return DecLcStTestUnlocked3;
      LcStTestLocked3:   return DecLcStTestLocked3;
      LcStTestUnlocked4: return DecLcStTestUnlocked4;
      LcStTestLocked4:   return DecLcStTestLocked4;
      LcStTestUnlocked5: return DecLcStTestUnlocked5;
      LcStTestLocked5:   return DecLcStTestLocked5;
      LcStTestUnlocked6: return DecLcStTestUnlocked6;
      LcStTestLocked6:   return DecLcStTestLocked6;
      LcStTestUnlocked7: return DecLcStTestUnlocked7;
      LcStDev:           return DecLcStDev;
      LcStProd:          return DecLcStProd;
      LcStProdEnd:       return DecLcStProdEnd;
      LcStRma:           return DecLcStRma;
      default:           return DecLcStScrap;
    endcase
  endfunction

  // Assert that a partition is write-locked once its corresponding life-cycle phase has expired.
  generate
  dec_lc_state_e dec_lc_state;
  assign dec_lc_state = decode_lc_state(lc_state_e'(`FC_PATH.otp_lc_data_o.state));
  for (genvar i = 0; i < NumPart-1; i++) begin
    `CALIPTRA_ASSERT(FcPartitionLcPhaseWriteLock_A,
      dec_lc_state > PartInfo[i].lc_phase |-> mubi8_t'(`FC_PATH.part_access[i].write_lock) == MuBi8True
    )
  end
  endgenerate

  // Assert that an DAI write to a partition whose life-cycle phase has expired will result in an error.
  `CALIPTRA_ASSERT(FcPartitionLcPhaseWriteLock_A,
    `FC_PATH.dai_req &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiWrite) &&
    dec_lc_state > PartInfo[part_idx].lc_phase
    |-> ##10
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
  )

  ////////////////////////////////////////////////////
  // fuse_ctrl partition access control
  ////////////////////////////////////////////////////
  logic [NumPartWidth-1:0] part_idx;
  assign part_idx = `FC_PATH.u_otp_ctrl_dai.part_idx;

  // Assert that secret partitions are read-locked after the digest has been computed.
  `CALIPTRA_ASSERT(FcSecretPartitionReadLock_A,
    ((PartInfo[part_idx].secret) &&
     (`CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[otp_ctrl_part_pkg::digest_addrs[part_idx]/2] != 0) &&
     (`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiRead) &&
     (`FC_PATH.dai_addr >= PartInfo[part_idx].offset) &&
     (`FC_PATH.dai_addr < otp_ctrl_part_pkg::digest_addrs[part_idx]))
     |-> ##2
     otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
    )

  // Assert that partitions are write-locked after the digest has been computed.
  //
  // Once a partition has a digest (either sw or hw), it should be write-locked. This means that if
  // we start a DaiWrite operation with an address that points inside that partition, it should
  // respond with an error.
  //
  // Normally, this response will appear in two cycles (with otp_ctrl_dai going to the WriteSt, then
  // noticing the partition is locked, so setting error_d, which gets flopped to error_o). However,
  // the partition might be scrambled (visible because PartInfo[part_idx].secret is true). In that
  // case, there are two extra cycles because the FSM goes through ScrSt, ScrWaitSt first.

  logic        part_may_have_digest, part_has_digest;
  int unsigned part_digest_word_addr;
  logic [21:0] raw_part_digest_value;
  logic        dai_write_req;
  logic        dai_addr_below_digest;
  logic        dai_access_error;

  assign part_may_have_digest  = PartInfo[part_idx].hw_digest || PartInfo[part_idx].sw_digest;
  assign part_digest_word_addr = otp_ctrl_part_pkg::digest_addrs[part_idx] / 2;
  assign raw_part_digest_value =
    `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[part_digest_word_addr];
  assign part_has_digest       = part_may_have_digest && (raw_part_digest_value != 0);
  assign dai_write_req         = `FC_PATH.dai_req && dai_cmd_e'(`FC_PATH.dai_cmd) == DaiWrite;
  assign dai_addr_below_digest = (`FC_PATH.dai_addr >= PartInfo[part_idx].offset) &&
                                 (`FC_PATH.dai_addr < otp_ctrl_part_pkg::digest_addrs[part_idx]);
  assign dai_access_error = otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError;

  `CALIPTRA_ASSERT(FcLockedPartitionWriteLock_A,
		   part_has_digest && dai_write_req && dai_addr_below_digest |-> ##[2:4]
		   dai_access_error)

  ////////////////////////////////////////////////////
  // fuse_ctrl zeroization
  ////////////////////////////////////////////////////

  // Return whether is a partition is zeroized
  function bit is_zeroized(int part_idx);
    logic [ScrmblBlockWidth-1:0] zero_marker;
    if (part_idx < 0 || part_idx >= NumPart) begin
      return 0; // Invalid partition index
    end else if (!PartInfo[part_idx].zeroizable) begin
      return 0; // Not zeroizable
    end else begin
      zero_marker = {`CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[otp_ctrl_part_pkg::zero_addrs[part_idx]/2][15:0],
                     `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[otp_ctrl_part_pkg::zero_addrs[part_idx]/2+1][15:0],
                     `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[otp_ctrl_part_pkg::zero_addrs[part_idx]/2+2][15:0],
                     `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[otp_ctrl_part_pkg::zero_addrs[part_idx]/2+3][15:0]};
      return (otp_ctrl_pkg::check_zeroized_valid(zero_marker));
    end
  endfunction : is_zeroized

  // Zeroization marker status
  logic [NumPart-1:0] pre_marker_zeroized_part = 0;
  logic [NumPart-1:0] marker_zeroized_part     = 0;
  always_ff @(posedge `CPTRA_SS_TOP_PATH.u_otp_ctrl.clk_i) begin : p_marker_zeroized_part
    if ((`FC_PATH.dai_req) && (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiZeroize) &&
        (PartInfo[part_idx].zeroizable) && (`FC_PATH.dai_addr/2 == otp_ctrl_part_pkg::zero_addrs[part_idx]/2)) begin
      pre_marker_zeroized_part[part_idx]  <= 1'b1;
    end
    if (pre_marker_zeroized_part[part_idx] && !marker_zeroized_part[part_idx] && `FC_PATH.otp_operation_done) begin
      if (is_zeroized(part_idx)) begin
        marker_zeroized_part[part_idx]      <= 1'b1;
      end else begin
        pre_marker_zeroized_part[part_idx]  <= 1'b0;
      end 
    end
  end

  // Store the latest direct_access_rdata release by the otp_ctrl_dai block after a successful access.
  logic [NumDaiWords-1:0][31:0] past_direct_access_rdata = 0;
  initial begin
    forever begin
      @(posedge `FC_PATH.clk_i);
      if ((`FC_PATH.dai_req)) begin
        past_direct_access_rdata = `FC_PATH.hw2reg.direct_access_rdata;
      end
    end
  end

  // A zeroized partition must still have the same access privileges: writes fail for a locked partition
  `CALIPTRA_ASSERT(FcZeroizePartWriteLock_A,
    ((PartInfo[part_idx].hw_digest || PartInfo[part_idx].sw_digest) &&
     (PartInfo[part_idx].zeroizable) &&
     (is_zeroized(part_idx)) &&
     (mubi8_t'(`FC_PATH.part_access[part_idx].write_lock) == MuBi8True) &&
     (`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiWrite) &&
     (`FC_PATH.dai_addr >= PartInfo[part_idx].offset) &&
     (`FC_PATH.dai_addr < otp_ctrl_part_pkg::digest_addrs[part_idx]))
    |-> ##2
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
  )

  // A zeroized partition must still have the same access privileges: reads fails for a locked secret partition
  `CALIPTRA_ASSERT(FcZeroizePartReadLock_A,
    ((PartInfo[part_idx].secret) &&
     (PartInfo[part_idx].zeroizable) &&
     (is_zeroized(part_idx)) &&
     (mubi8_t'(`FC_PATH.part_access_dai[part_idx].read_lock) == MuBi8True) &&
     (`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiRead) &&
     (`FC_PATH.dai_addr >= PartInfo[part_idx].offset) &&
     (`FC_PATH.dai_addr < otp_ctrl_part_pkg::digest_addrs[part_idx]))
    |-> ##2
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
  )

  // Make sure that the zeroization command will never return descrambled data for the secret partitions
  `CALIPTRA_ASSERT(FcZeroizeNoDescrambled_A,
    ((PartInfo[part_idx].secret) &&
     (`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiZeroize))
    |->
    not(!`FC_PATH.otp_operation_done[*1:$] ##1
        (otp_scrmbl_cmd_e'(`FC_PATH.u_otp_ctrl_dai.scrmbl_cmd_o) == Decrypt))
  )

  // Zeroization must only be possible for zeroizable partitions
  `CALIPTRA_ASSERT(FcZeroizeOnlyZeroizableAllowed_A,
    (mubi8_t'(`FC_PATH.part_zer_trigs[part_idx]) == MuBi8True)
    |->
    PartInfo[part_idx].zeroizable == 1'b1
  )

  // Attempt to zeroize a non zeroizable partition must be rejected and an error flag should be raised
  `CALIPTRA_ASSERT(FcZeroizeNonZeroizableDenied_A,
    ((`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiZeroize) &&
     (!PartInfo[part_idx].zeroizable))
    |-> ##2
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
  )

  // Zeroization marker field is always readable
  `CALIPTRA_ASSERT(FcZeroizeMarkerAlwaysReadable_A,
    ((`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiRead) &&
     (PartInfo[part_idx].zeroizable) &&
     (`FC_PATH.dai_addr == otp_ctrl_part_pkg::zero_addrs[part_idx]))
    |-> ##2
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == NoError
  )

  // Zeroization marker field is never writable
  `CALIPTRA_ASSERT(FcZeroizeMarkerNeverWritable_A,
    ((`FC_PATH.dai_req) &&
     (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiWrite) &&
     (PartInfo[part_idx].zeroizable) &&
     (`FC_PATH.dai_addr == otp_ctrl_part_pkg::zero_addrs[part_idx]))
    |-> ##2
    otp_err_e'(`FC_PATH.part_error[DaiIdx]) == AccessError
  )

  // When doing a zeroization, the zeroized_valid flag should be kept as invalid if the number of
  // set bits in the 64-bit word is lower than ZeroizationValidBound
  `CALIPTRA_ASSERT(FcZeroizeInvalidWhenBelowThresh_A,
    first_match((`FC_PATH.dai_req) &&
      (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiZeroize)
      ##[1:$]
      (pre_marker_zeroized_part[part_idx]) &&
      (`FC_PATH.otp_operation_done) &&
      (!is_zeroized(part_idx)))
    |=>
    (mubi16_t'(`FC_PATH.u_otp_ctrl_dai.zeroized_valid) == MuBi16False)
  )

  // For scrambled partitions, the zeroized fuse should only be returned if and only if the
  // number of set bits in the 64-bit word is greater or equal ZeroizationValidBound
  `CALIPTRA_ASSERT(FcZeroizeMarkerOnlyWhenAboveThresh_A,
    first_match((PartInfo[part_idx].secret) &&
      (`FC_PATH.dai_req) &&
      (dai_cmd_e'(`FC_PATH.dai_cmd) == DaiZeroize)
      ##[1:$]
      (pre_marker_zeroized_part[part_idx]) &&
      (`FC_PATH.otp_operation_done) &&
      (!is_zeroized(part_idx)))
    |=>
    // In this case, this register will only get updated for a successful and complete zeroization (above the threshold),
    // otherswise, it will take back the previous value.
    (`FC_PATH.hw2reg.direct_access_rdata == past_direct_access_rdata)
  )

  ////////////////////////////////////////////////////
  // fuse_ctrl escalation
  ////////////////////////////////////////////////////

  // Assert that an esclation will transfer the fuse_ctrl into a terminal state.
  `CALIPTRA_ASSERT(FcEscalationTerminalError_A,
    `FC_PATH.lc_escalate_en_i == On
    |-> ##10
    `FC_PATH.u_otp_ctrl_dai.state_q == `FC_PATH.u_otp_ctrl_dai.ErrorSt
  )

  ////////////////////////////////////////////////////
  // lcc volatile raw unlock dft en
  ////////////////////////////////////////////////////

  // Assert that a successful volatile raw unlock will assert the dft output port.
  `CALIPTRA_ASSERT(LccVolatileRawUnlockDftEn_A,
    (`LCC_PATH.lc_sec_volatile_raw_unlock_en_i &&
     `LCC_PATH.volatile_raw_unlock_q &&
     `LCC_PATH.trans_success_q)
    |=>
    (`LCC_PATH.lc_dft_en_o && `LCC_PATH.lc_hw_debug_en_o)
  )

  ////////////////////////////////////////////////////
  // lcc volatile raw unlock decoding
  ////////////////////////////////////////////////////

  `CALIPTRA_ASSERT(LccVolatileRawUnlockDecoding_A,
    (`LCC_PATH.lc_sec_volatile_raw_unlock_en_i &&
     `LCC_PATH.volatile_raw_unlock_q &&
     `LCC_PATH.trans_success_q)
    |->
    (dec_lc_state_e'(`LCC_PATH.dec_lc_state[0]) == DecLcStTestUnlocked0 &&
     dec_lc_state_e'(`LCC_PATH.dec_lc_state[1]) == DecLcStTestUnlocked0 &&
     dec_lc_state_e'(`LCC_PATH.dec_lc_state[2]) == DecLcStTestUnlocked0 &&
     dec_lc_state_e'(`LCC_PATH.dec_lc_state[3]) == DecLcStTestUnlocked0 &&
     dec_lc_state_e'(`LCC_PATH.dec_lc_state[4]) == DecLcStTestUnlocked0 &&
     dec_lc_state_e'(`LCC_PATH.dec_lc_state[5]) == DecLcStTestUnlocked0)
  )

  ////////////////////////////////////////////////////
  // LCC in SCRAP mode
  ////////////////////////////////////////////////////

  // LCC in is SCRAP mode results in the broadcast data to be set to zero.
  `CALIPTRA_ASSERT(LccScrapBroadcastData_A,
    ((`FC_PATH.lcc_is_in_SCRAP_mode) && (!`FC_PATH.rst_ni))
    |=>
    `FC_PATH.otp_broadcast_o == otp_broadcast_t'('0)
  )

  ////////////////////////////////////////////////////
  // fuse_ctrl interrupts
  ////////////////////////////////////////////////////

  // Make sure an `otp_operation_done` interrupt is raised, when enabled, upon a successful DAI operation.
  `CALIPTRA_ASSERT(FcOtpOperationDoneInterrupt_A,
    (`FC_PATH.u_reg_core.u_intr_enable_otp_operation_done.q &&
     $fell(`FC_PATH.otp_operation_done) &&
     otp_err_e'(`FC_PATH.part_error[DaiIdx]) == NoError)
    |=> ##2
    (`FC_PATH.intr_otp_operation_done_o && !`FC_PATH.intr_otp_error_o)
  )

  // Make sure an `otp_error` interrupt is raised, when enabled, upon a failed DAI operation.
  `CALIPTRA_ASSERT(FcOtpErrorInterrupt_A,
    (`FC_PATH.u_reg_core.u_intr_enable_otp_error.q &&
     $fell(`FC_PATH.otp_operation_done) &&
     otp_err_e'(`FC_PATH.part_error[DaiIdx]) != NoError)
    |=> ##2
    (`FC_PATH.intr_otp_error_o)
  )

endmodule
