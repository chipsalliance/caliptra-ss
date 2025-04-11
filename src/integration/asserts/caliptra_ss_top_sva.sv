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
      disable iff (!`LCC_PATH.rst_ni)
      ($rose(`LCC_PATH.u_lc_ctrl_fsm.trans_cmd_i)
        && (`LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.dec_lc_state_i != {DecLcStateNumRep{DecLcStScrap}})
        && (`LCC_PATH.u_lc_ctrl_fsm.trans_target_i == {DecLcStateNumRep{DecLcStRma}}
            || `LCC_PATH.u_lc_ctrl_fsm.trans_target_i == {DecLcStateNumRep{DecLcStScrap}}))
          |-> (`LCC_PATH.Allow_RMA_or_SCRAP_on_PPD throughout (!`LCC_PATH.trans_success_q));
  endproperty
  
  assert property (Allow_PPD_check_in_LCC)
    else $display("SVA ERROR: Allow_RMA_or_SCRAP_on_PPD was not asserted for SCRAP and RMA.");
    

      
endmodule
