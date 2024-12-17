// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle signal decoder and sender module.

module caliptra_ss_lc_ctrl_signal_decode
  import caliptra_ss_lc_ctrl_pkg::*;
  import caliptra_ss_lc_ctrl_state_pkg::*;
#(
  // Random netlist constants
  // SCRAP, RAW, TEST_LOCKED*, INVALID
  parameter caliptra_ss_lc_keymgr_div_t RndCnstLcKeymgrDivInvalid      = LcKeymgrDivWidth'(0),
  // TEST_UNLOCKED*
  parameter caliptra_ss_lc_keymgr_div_t RndCnstLcKeymgrDivTestUnlocked = LcKeymgrDivWidth'(1),
  // DEV
  parameter caliptra_ss_lc_keymgr_div_t RndCnstLcKeymgrDivDev          = LcKeymgrDivWidth'(2),
  // PROD, PROD_END
  parameter caliptra_ss_lc_keymgr_div_t RndCnstLcKeymgrDivProduction   = LcKeymgrDivWidth'(3),
  // RMA
  parameter caliptra_ss_lc_keymgr_div_t RndCnstLcKeymgrDivRma          = LcKeymgrDivWidth'(4)
  ) (
  input                  clk_i,
  input                  rst_ni,
  // Life cycle state vector.
  input  logic           caliptra_ss_lc_state_valid_i,
  input  caliptra_ss_lc_state_e      caliptra_ss_lc_state_i,
  input  fsm_state_e     fsm_state_i,
  input  caliptra_ss_lc_tx_t         secrets_valid_i,
  // Local life cycle signal
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_raw_test_rma_o,
  // Life cycle broadcast outputs.
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_dft_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_nvm_debug_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_hw_debug_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_cpu_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_creator_seed_sw_rw_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_owner_seed_sw_rw_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_iso_part_sw_rd_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_iso_part_sw_wr_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_seed_hw_rd_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_keymgr_en_o,
  output caliptra_ss_lc_tx_t         caliptra_ss_lc_escalate_en_o,
  // State group diversification value for keymgr
  output caliptra_ss_lc_keymgr_div_t caliptra_ss_lc_keymgr_div_o
);

  //////////////////////////
  // Signal Decoder Logic //
  //////////////////////////

  caliptra_ss_lc_tx_t caliptra_ss_lc_raw_test_rma;
  caliptra_ss_lc_tx_t caliptra_ss_lc_dft_en, caliptra_ss_lc_nvm_debug_en, caliptra_ss_lc_hw_debug_en, caliptra_ss_lc_cpu_en, caliptra_ss_lc_keymgr_en, caliptra_ss_lc_escalate_en;
  caliptra_ss_lc_tx_t caliptra_ss_lc_creator_seed_sw_rw_en, caliptra_ss_lc_owner_seed_sw_rw_en, caliptra_ss_lc_iso_part_sw_rd_en;
  caliptra_ss_lc_tx_t caliptra_ss_lc_iso_part_sw_wr_en, caliptra_ss_lc_seed_hw_rd_en;
  caliptra_ss_lc_keymgr_div_t caliptra_ss_lc_keymgr_div_d, caliptra_ss_lc_keymgr_div_q;

  always_comb begin : p_caliptra_ss_lc_signal_decode
    // Life cycle control signal defaults
    caliptra_ss_lc_raw_test_rma          = Off;
    caliptra_ss_lc_dft_en                = Off;
    caliptra_ss_lc_nvm_debug_en          = Off;
    caliptra_ss_lc_hw_debug_en           = Off;
    caliptra_ss_lc_cpu_en                = Off;
    caliptra_ss_lc_creator_seed_sw_rw_en = Off;
    caliptra_ss_lc_owner_seed_sw_rw_en   = Off;
    caliptra_ss_lc_iso_part_sw_rd_en     = Off;
    caliptra_ss_lc_iso_part_sw_wr_en     = Off;
    caliptra_ss_lc_seed_hw_rd_en         = Off;
    caliptra_ss_lc_keymgr_en             = Off;
    // This ensures that once escalation has been triggered, it cannot go back to Off.
    caliptra_ss_lc_escalate_en           = caliptra_ss_lc_tx_or_hi(Off, caliptra_ss_lc_escalate_en_o);
    // Set to invalid diversification value by default.
    caliptra_ss_lc_keymgr_div_d          = RndCnstLcKeymgrDivInvalid;

    unique case (fsm_state_i)
      ///////////////////////////////////////////////////////////////////
      // Don't broadcast anything in this state.
      ResetSt: ;
      ///////////////////////////////////////////////////////////////////
      // Broadcasting of most signals is only enabled during the following life cycle states.
      IdleSt,
      ClkMuxSt,
      CntIncrSt,
      CntProgSt,
      TransCheckSt,
      FlashRmaSt,
      TokenHashSt,
      TokenCheck0St,
      TokenCheck1St,
      TransProgSt: begin
        if (caliptra_ss_lc_state_valid_i) begin
          unique case (caliptra_ss_lc_state_i)
            ///////////////////////////////////////////////////////////////////
            // Only enable life cycle TAP register for OTP test mechanisms.
            LcStRaw,
            LcStTestLocked0,
            LcStTestLocked1,
            LcStTestLocked2,
            LcStTestLocked3,
            LcStTestLocked4,
            LcStTestLocked5,
            LcStTestLocked6: begin
              caliptra_ss_lc_raw_test_rma = On;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable DFT and debug functionality, including the CPU in the
            // test unlocked states.
            LcStTestUnlocked0,
            LcStTestUnlocked1,
            LcStTestUnlocked2,
            LcStTestUnlocked3,
            LcStTestUnlocked4,
            LcStTestUnlocked5,
            LcStTestUnlocked6: begin
              caliptra_ss_lc_raw_test_rma      = On;
              caliptra_ss_lc_dft_en            = On;
              caliptra_ss_lc_nvm_debug_en      = On;
              caliptra_ss_lc_hw_debug_en       = On;
              caliptra_ss_lc_cpu_en            = On;
              caliptra_ss_lc_iso_part_sw_wr_en = On;
              caliptra_ss_lc_keymgr_div_d      = RndCnstLcKeymgrDivTestUnlocked;
            end
            ///////////////////////////////////////////////////////////////////
            // This is the last TEST_UNLOCKED state. The same feature set is enabled
            // as in the other TEST_UNLOCKED states above, except for NVM debug en,
            // which is disabled in this state.
            LcStTestUnlocked7: begin
              caliptra_ss_lc_raw_test_rma      = On;
              caliptra_ss_lc_dft_en            = On;
              caliptra_ss_lc_hw_debug_en       = On;
              caliptra_ss_lc_cpu_en            = On;
              caliptra_ss_lc_iso_part_sw_wr_en = On;
              caliptra_ss_lc_keymgr_div_d      = RndCnstLcKeymgrDivTestUnlocked;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable production functions
            LcStProd,
            LcStProdEnd: begin
              caliptra_ss_lc_cpu_en              = On;
              caliptra_ss_lc_keymgr_en           = On;
              caliptra_ss_lc_owner_seed_sw_rw_en = On;
              caliptra_ss_lc_iso_part_sw_wr_en   = On;
              caliptra_ss_lc_iso_part_sw_rd_en   = On;
              caliptra_ss_lc_keymgr_div_d        = RndCnstLcKeymgrDivProduction;
              // Only allow provisioning if the device has not yet been personalized.
              // If secrets_valid_i is set to ON, we output OFF.
              // Note that we can convert ON to OFF with a bitwise inversion due to the encoding.
              caliptra_ss_lc_creator_seed_sw_rw_en = caliptra_ss_lc_tx_t'(~secrets_valid_i);
              // Only allow hardware to consume the seeds once personalized.
              // If secrets_valid_i is set to ON, we output ON.
              caliptra_ss_lc_seed_hw_rd_en = secrets_valid_i;
            end
            ///////////////////////////////////////////////////////////////////
            // Similar functions as PROD, with the following differences:
            // - hardware debug functionality (CPU TAP) is enabled,
            // - access to the isolated flash partition is disabled.
            LcStDev: begin
              caliptra_ss_lc_hw_debug_en         = On;
              caliptra_ss_lc_cpu_en              = On;
              caliptra_ss_lc_keymgr_en           = On;
              caliptra_ss_lc_owner_seed_sw_rw_en = On;
              caliptra_ss_lc_iso_part_sw_wr_en   = On;
              caliptra_ss_lc_keymgr_div_d        = RndCnstLcKeymgrDivDev;
              // Only allow provisioning if the device has not yet been personalized.
              // If secrets_valid_i is set to ON, we output OFF.
              // Note that we can convert ON to OFF with a bitwise inversion due to the encoding.
              caliptra_ss_lc_creator_seed_sw_rw_en = caliptra_ss_lc_tx_t'(~secrets_valid_i);
              // Only allow hardware to consume the seeds once personalized.
              // If secrets_valid_i is set to ON, we output ON.
              caliptra_ss_lc_seed_hw_rd_en = secrets_valid_i;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable all test and production functions.
            LcStRma: begin
              caliptra_ss_lc_raw_test_rma          = On;
              caliptra_ss_lc_dft_en                = On;
              caliptra_ss_lc_nvm_debug_en          = On;
              caliptra_ss_lc_hw_debug_en           = On;
              caliptra_ss_lc_cpu_en                = On;
              caliptra_ss_lc_keymgr_en             = On;
              caliptra_ss_lc_creator_seed_sw_rw_en = On;
              caliptra_ss_lc_owner_seed_sw_rw_en   = On;
              caliptra_ss_lc_iso_part_sw_wr_en     = On;
              caliptra_ss_lc_iso_part_sw_rd_en     = On;
              caliptra_ss_lc_seed_hw_rd_en         = On;
              caliptra_ss_lc_keymgr_div_d          = RndCnstLcKeymgrDivRma;
            end
            ///////////////////////////////////////////////////////////////////
            // Invalid or scrapped life cycle state, make sure the escalation
            // signal is also asserted in this case.
            default: begin
              caliptra_ss_lc_escalate_en = On;
            end
          endcase // caliptra_ss_lc_state_i
        end else begin
          caliptra_ss_lc_escalate_en = On;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Post-transition state. Behaves similarly to the virtual scrap
      // states below, with the exception that escalate_en is NOT asserted,
      // since that could trigger unwanted alerts / escalations and system resets.
      PostTransSt: ;
      ///////////////////////////////////////////////////////////////////
      // Virtual scrap states, make sure the escalation signal is
      // also asserted in this case.
      ScrapSt,
      EscalateSt,
      InvalidSt: begin
        caliptra_ss_lc_escalate_en = On;
      end
      default: begin
        caliptra_ss_lc_escalate_en = On;
      end
    endcase // fsm_state_i
  end

  /////////////////////////////////
  // Control signal output flops //
  /////////////////////////////////

  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_raw_test_rma (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_raw_test_rma),
    .lc_en_o(caliptra_ss_lc_raw_test_rma_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_dft_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_dft_en),
    .lc_en_o(caliptra_ss_lc_dft_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_nvm_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_nvm_debug_en),
    .lc_en_o(caliptra_ss_lc_nvm_debug_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_hw_debug_en),
    .lc_en_o(caliptra_ss_lc_hw_debug_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_cpu_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_cpu_en),
    .lc_en_o(caliptra_ss_lc_cpu_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_creator_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_creator_seed_sw_rw_en),
    .lc_en_o(caliptra_ss_lc_creator_seed_sw_rw_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_owner_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_owner_seed_sw_rw_en),
    .lc_en_o(caliptra_ss_lc_owner_seed_sw_rw_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_iso_part_sw_rd_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_iso_part_sw_rd_en),
    .lc_en_o(caliptra_ss_lc_iso_part_sw_rd_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_iso_part_sw_wr_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_iso_part_sw_wr_en),
    .lc_en_o(caliptra_ss_lc_iso_part_sw_wr_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_seed_hw_rd_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_seed_hw_rd_en),
    .lc_en_o(caliptra_ss_lc_seed_hw_rd_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_keymgr_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_keymgr_en),
    .lc_en_o(caliptra_ss_lc_keymgr_en_o)
  );
  caliptra_prim_lc_sender u_caliptra_prim_lc_sender_escalate_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(caliptra_ss_lc_escalate_en),
    .lc_en_o(caliptra_ss_lc_escalate_en_o)
  );

  assign caliptra_ss_lc_keymgr_div_o = caliptra_ss_lc_keymgr_div_q;

  caliptra_prim_flop #(
    .Width(LcKeymgrDivWidth),
    .ResetValue(RndCnstLcKeymgrDivInvalid)
  ) u_caliptra_prim_flop_keymgr_div (
    .clk_i  ( clk_i           ),
    .rst_ni ( rst_ni          ),
    .d_i    ( caliptra_ss_lc_keymgr_div_d ),
    .q_o    ( caliptra_ss_lc_keymgr_div_q )
  );

  ////////////////
  // Assertions //
  ////////////////

  // Need to make sure that the random netlist constants are all unique.
  `CALIPTRA_ASSERT_INIT(LcKeymgrDivUnique0_A,
      !(RndCnstLcKeymgrDivInvalid inside {RndCnstLcKeymgrDivTestUnlocked,
                                          RndCnstLcKeymgrDivDev,
                                          RndCnstLcKeymgrDivRma,
                                          RndCnstLcKeymgrDivProduction}))
  `CALIPTRA_ASSERT_INIT(LcKeymgrDivUnique1_A,
      !(RndCnstLcKeymgrDivTestUnlocked inside {RndCnstLcKeymgrDivInvalid,
                                               RndCnstLcKeymgrDivDev,
                                               RndCnstLcKeymgrDivRma,
                                               RndCnstLcKeymgrDivProduction}))
  `CALIPTRA_ASSERT_INIT(LcKeymgrDivUnique2_A,
      !(RndCnstLcKeymgrDivDev inside {RndCnstLcKeymgrDivInvalid,
                                      RndCnstLcKeymgrDivTestUnlocked,
                                      RndCnstLcKeymgrDivRma,
                                      RndCnstLcKeymgrDivProduction}))
  `CALIPTRA_ASSERT_INIT(LcKeymgrDivUnique3_A,
      !(RndCnstLcKeymgrDivRma inside {RndCnstLcKeymgrDivInvalid,
                                      RndCnstLcKeymgrDivTestUnlocked,
                                      RndCnstLcKeymgrDivDev,
                                      RndCnstLcKeymgrDivProduction}))

  `CALIPTRA_ASSERT(SignalsAreOffWhenNotEnabled_A,
      !caliptra_ss_lc_state_valid_i
      |=>
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_raw_test_rma_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_dft_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_nvm_debug_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_hw_debug_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_cpu_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_creator_seed_sw_rw_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_owner_seed_sw_rw_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_iso_part_sw_rd_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_iso_part_sw_wr_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_seed_hw_rd_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_keymgr_en_o) &&
      caliptra_ss_lc_tx_test_false_strict(caliptra_ss_lc_dft_en_o) &&
      caliptra_ss_lc_keymgr_div_o == RndCnstLcKeymgrDivInvalid)


  `CALIPTRA_ASSERT(FsmInScrap_A,
      !(fsm_state_i inside {ResetSt,
                            TransProgSt,
                            IdleSt,
                            ClkMuxSt,
                            CntIncrSt,
                            CntProgSt,
                            TransCheckSt,
                            FlashRmaSt,
                            TokenHashSt,
                            TokenCheck0St,
                            TokenCheck1St,
                            PostTransSt})
      |=>
      caliptra_ss_lc_tx_test_true_strict(caliptra_ss_lc_escalate_en_o))

  `CALIPTRA_ASSERT(StateInScrap_A,
      caliptra_ss_lc_state_valid_i &&
      fsm_state_i inside {IdleSt,
                          ClkMuxSt,
                          CntIncrSt,
                          CntProgSt,
                          TransCheckSt,
                          FlashRmaSt,
                          TokenHashSt,
                          TokenCheck0St,
                          TokenCheck1St} &&
      !(caliptra_ss_lc_state_i inside {LcStRaw,
                           LcStTestUnlocked0,
                           LcStTestUnlocked1,
                           LcStTestUnlocked2,
                           LcStTestUnlocked3,
                           LcStTestUnlocked4,
                           LcStTestUnlocked5,
                           LcStTestUnlocked6,
                           LcStTestUnlocked7,
                           LcStTestLocked0,
                           LcStTestLocked1,
                           LcStTestLocked2,
                           LcStTestLocked3,
                           LcStTestLocked4,
                           LcStTestLocked5,
                           LcStTestLocked6,
                           LcStDev,
                           LcStProd,
                           LcStProdEnd,
                           LcStRma})
      |=>
      caliptra_ss_lc_tx_test_true_strict(caliptra_ss_lc_escalate_en_o))

endmodule : caliptra_ss_lc_ctrl_signal_decode
