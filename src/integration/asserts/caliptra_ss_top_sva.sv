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

module caliptra_ss_top_sva
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  ();
  
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
  assign dec_lc_state = decode_lc_state(lc_state_e'(`CPTRA_SS_TOP_PATH.u_otp_ctrl.otp_lc_data_o.state));
  for (genvar i = 0; i < NumPart-1; i++) begin
    fc_partition_lc_phase_write_lock: assert property (
      @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
      dec_lc_state > PartInfo[i].lc_phase |-> mubi8_t'(`CPTRA_SS_TOP_PATH.u_otp_ctrl.part_access[i].write_lock) == MuBi8True
    )
    else $display("SVA ERROR: partition %d is not write-locked for life-cycle state %d", i, dec_lc_state);
  end
  endgenerate

  // Assert that an escalation moves the fuse controller into an terminal unresponsive state.
  // generate
  // for (genvar i = 0; i < NumPart; i++) begin
  //   fc_partition_escalation_lock : assert property (
  //     @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
  //     `CPTRA_SS_TOP_PATH.u_otp_ctrl.lc_escalate_en_i == On |-> ##10 otp_err_e'(`CPTRA_SS_TOP_PATH.u_otp_ctrl.part_error[i]) == FsmStateError
  //   )
  //   else $display("SVA ERROR: partition %d is not locked after escalation", i);
  // end
  // endgenerate
  fc_partition_escalation_dai_lock : assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    `CPTRA_SS_TOP_PATH.u_otp_ctrl.lc_escalate_en_i == On |-> ##10 `CPTRA_SS_TOP_PATH.u_otp_ctrl.u_otp_ctrl_dai.state_q == `CPTRA_SS_TOP_PATH.u_otp_ctrl.u_otp_ctrl_dai.ErrorSt
  ) else $display("SVA ERROR: fuse ctrl dai is not in a terminal state");

  // When the fuse controller filter signals an access error any DAI write must fail.
  fc_access_control_error : assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    ((`CPTRA_SS_TOP_PATH.u_otp_ctrl.u_fuse_ctrl_filter.discard_fuse_write_o) &&
    (`CPTRA_SS_TOP_PATH.u_otp_ctrl.u_otp_ctrl_dai.state_q == `CPTRA_SS_TOP_PATH.u_otp_ctrl.u_otp_ctrl_dai.WriteSt))
    |=> 
    otp_err_e'(`CPTRA_SS_TOP_PATH.u_otp_ctrl.u_otp_ctrl_dai.error_o) == AccessError
  ) else $display("SVA ERROR: fuse ctrl filter discard does not result in DAI error");

  // Zeroization broadcast
  fc_zeroize_broadcast : assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TOP_PATH.u_otp_ctrl.rst_ni)
    ((`CPTRA_SS_TOP_PATH.u_otp_ctrl.FIPS_ZEROIZATION_CMD_i) || (`CPTRA_SS_TOP_PATH.u_otp_ctrl.lcc_is_in_SCRAP_mode))
    |=> 
    `CPTRA_SS_TOP_PATH.u_otp_ctrl.otp_broadcast_o == otp_broadcast_t'('0)
  ) else $display("SVA ERROR: fuse ctrl broadcast data is not zeroized after cmd");
  // fc_release_zeroize_broadcast : assert property (
  //   @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
  //   disable iff (~`CPTRA_SS_TOP_PATH.u_otp_ctrl.rst_ni)
  //   (!(`CPTRA_SS_TOP_PATH.u_otp_ctrl.FIPS_ZEROIZATION_CMD_i) && !(`CPTRA_SS_TOP_PATH.u_otp_ctrl.lcc_is_in_SCRAP_mode))
  //   |-> ##5
  //   `CPTRA_SS_TOP_PATH.u_otp_ctrl.otp_broadcast_o != otp_broadcast_t'('0)
  // ) else $display("SVA ERROR: fuse ctrl broadcast data is not signaled after zeroization relesase");

  //WDT checks:
  cascade_wdt_t1_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.timer1_restart && !`WDT_PATH.timer2_en && !`WDT_PATH.t1_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart on pet");

  cascade_wdt_t2_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.timer2_restart && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart on pet");

  cascade_wdt_t1_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart after interrupt service");

  cascade_wdt_t2_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart after interrupt service");

  independent_wdt_t1_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart on pet");

  independent_wdt_t2_pet: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.timer2_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart on pet");

  independent_wdt_t1_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && `WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart after interrupt service");

  independent_wdt_t2_service: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart after interrupt service");

  wdt_status_t1_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TB_TOP_NAME.cptra_ss_rst_b_i)
    $rose(`WDT_PATH.t1_timeout) |=> $rose(`MCI_PATH.mci_reg_hwif_out.WDT_STATUS.t1_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t1 expiry!");

  wdt_status_t2_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    disable iff (~`CPTRA_SS_TB_TOP_NAME.cptra_ss_rst_b_i)
    $rose(`WDT_PATH.t2_timeout) |=> $rose(`MCI_PATH.mci_reg_hwif_out.WDT_STATUS.t2_timeout.value)
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
            || `LCC_PATH.u_lc_ctrl_fsm.trans_target_i == {DecLcStateNumRep{DecLcStScrap}}))
          |-> (`LCC_PATH.Allow_RMA_or_SCRAP_on_PPD throughout (!`LCC_PATH.trans_success_q));
  endproperty
  
  assert property (Allow_PPD_check_in_LCC)
    else $display("SVA ERROR: Allow_RMA_or_SCRAP_on_PPD was not asserted for SCRAP and RMA.");
    

  //Error handling - TODO: disable conditions
  mci_error_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
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
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_nmi_pin & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_dmi_axi_collision) & (`MCI_REG_TOP_PATH.nmi_intr | `MCI_REG_TOP_PATH.mcu_sram_dmi_axi_collision_error) & `MCI_REG_TOP_PATH.mci_intr |=> ~`MCI_REG_TOP_PATH.all_error_fatal[*5])
  ) else $display("SVA ERROR: all_error_fatal is asserted unexpectedly");
  
  all_error_fatal_sram_doublebit_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_ecc_unc) & `MCI_REG_TOP_PATH.mcu_sram_double_ecc_error & `MCI_REG_TOP_PATH.cif_resp_if.error |=> ~`MCI_REG_TOP_PATH.all_error_fatal[*5])
  ) else $display("SVA ERROR: all_error_fatal for mcu_sram_ecc_unc is asserted unexpectedly");

  //----------------------------------------------
  mci_error_non_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
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
    ((`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox0_ecc_unc & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox1_ecc_unc) & (`MCI_REG_TOP_PATH.mbox0_sram_double_ecc_error | `MCI_REG_TOP_PATH.mbox1_sram_double_ecc_error) & `MCI_REG_TOP_PATH.mci_intr |=> ~`MCI_REG_TOP_PATH.all_error_non_fatal[*5])
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
    (`CPTRA_SS_TOP_PATH.cptra_error_fatal & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal0 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o) and
    (`CPTRA_SS_TOP_PATH.mcu_dccm_ecc_double_error & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal6 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o) and
    ((`CPTRA_SS_TOP_PATH.lc_alerts_o != 0) & (`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal14 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal13 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal12) |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o) and
    ((`CPTRA_SS_TOP_PATH.fc_alerts != 0) & (`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal20 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal19 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal18) |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o) and
    (`CPTRA_SS_TOP_PATH.i3c_peripheral_reset & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal25 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o) and
    (`CPTRA_SS_TOP_PATH.i3c_escalated_reset & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal24 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o)
  ) else $display("SVA ERROR: AGG all_error_fatal is not set correctly");

  agg_all_error_non_fatal_check: assert property (
    @(posedge `CPTRA_SS_TB_TOP_NAME.core_clk)
    (`CPTRA_SS_TOP_PATH.cptra_error_non_fatal & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal0 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o) and
    (`CPTRA_SS_TOP_PATH.mcu_dccm_ecc_single_error & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal6 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o) and
    ((`CPTRA_SS_TOP_PATH.lc_alerts_o != 0) & (`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal14 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal13 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal12) |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o) and
    ((`CPTRA_SS_TOP_PATH.fc_alerts != 0) & (`MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal20 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal19 | `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal18) |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o) and
    (`CPTRA_SS_TOP_PATH.i3c_peripheral_reset & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal25 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o) and
    (`CPTRA_SS_TOP_PATH.i3c_escalated_reset & `MCI_REG_TOP_PATH.mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal24 |=> ##2 ~`CPTRA_SS_TOP_PATH.cptra_ss_all_error_non_fatal_o)
  ) else $display("SVA ERROR: AGG all_error_non_fatal is not set correctly");


endmodule
