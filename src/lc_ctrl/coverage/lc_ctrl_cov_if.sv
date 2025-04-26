// SPDX-License-Identifier: Apache-2.0
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

`ifndef VERILATOR

interface lc_ctrl_cov_if
    import lc_ctrl_pkg::*;
    import lc_ctrl_state_pkg::*;
    import lc_ctrl_reg_pkg::*;
(
    input  logic clk_i,
    input  logic rst_ni
);

    ext_dec_lc_state_t dec_lc_state, next_dec_state;
    dec_lc_cnt_t       dec_lc_cnt;
    logic st_trans_cmd;

    // Casting the interface signals to the proper types from the package.
    assign dec_lc_state = ext_dec_lc_state_t'(lc_ctrl.dec_lc_state);
    assign dec_lc_cnt   = dec_lc_cnt_t'(lc_ctrl.dec_lc_cnt);


    assign st_trans_cmd = ext_dec_lc_state_t'(lc_ctrl.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_cmd_i);
    assign next_dec_state = ext_dec_lc_state_t'(lc_ctrl.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.trans_target_i);

    bit sec_volatile_raw_unlock;
    assign sec_volatile_raw_unlock = lc_ctrl.SecVolatileRawUnlockEn;

    logic [NumAlerts-1:0] alerts;
    assign alerts = lc_ctrl.alerts;

    // Precompute replicated constants for the state bins:
    localparam ext_dec_lc_state_t DEC_LC_ST_RAW_REP             =    {DecLcStateNumRep{DecLcStRaw}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED0_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked0}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED0_REP    =    {DecLcStateNumRep{DecLcStTestLocked0}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED1_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked1}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED1_REP    =    {DecLcStateNumRep{DecLcStTestLocked1}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED2_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked2}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED2_REP    =    {DecLcStateNumRep{DecLcStTestLocked2}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED3_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked3}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED3_REP    =    {DecLcStateNumRep{DecLcStTestLocked3}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED4_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked4}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED4_REP    =    {DecLcStateNumRep{DecLcStTestLocked4}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED5_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked5}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED5_REP    =    {DecLcStateNumRep{DecLcStTestLocked5}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED6_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked6}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_LOCKED6_REP    =    {DecLcStateNumRep{DecLcStTestLocked6}};
    localparam ext_dec_lc_state_t DEC_LC_ST_TEST_UNLOCKED7_REP  =    {DecLcStateNumRep{DecLcStTestUnlocked7}};
    localparam ext_dec_lc_state_t DEC_LC_ST_DEV_REP             =    {DecLcStateNumRep{DecLcStDev}};
    localparam ext_dec_lc_state_t DEC_LC_ST_PROD_REP            =    {DecLcStateNumRep{DecLcStProd}};
    localparam ext_dec_lc_state_t DEC_LC_ST_PROD_END_REP        =    {DecLcStateNumRep{DecLcStProdEnd}};
    localparam ext_dec_lc_state_t DEC_LC_ST_RMA_REP             =    {DecLcStateNumRep{DecLcStRma}};
    localparam ext_dec_lc_state_t DEC_LC_ST_SCRAP_REP           =    {DecLcStateNumRep{DecLcStScrap}};
    localparam ext_dec_lc_state_t DEC_LC_ST_POST_TRANS_REP      =    {DecLcStateNumRep{DecLcStPostTrans}};
    localparam ext_dec_lc_state_t DEC_LC_ST_ESCALATE_REP        =    {DecLcStateNumRep{DecLcStEscalate}};
    localparam ext_dec_lc_state_t DEC_LC_ST_INVALID_REP         =    {DecLcStateNumRep{DecLcStInvalid}};

    covergroup lc_ctrl_cg @(posedge clk_i);
        option.per_instance = 1;
    
        // Coverpoint for the state signal with its bins.
        lc_state_cp: coverpoint dec_lc_state {
            bins DecLcStRaw           = {DEC_LC_ST_RAW_REP};
            bins DecLcStTestUnlocked0 = {DEC_LC_ST_TEST_UNLOCKED0_REP};
            bins DecLcStTestLocked0   = {DEC_LC_ST_TEST_LOCKED0_REP};
            bins DecLcStTestUnlocked1 = {DEC_LC_ST_TEST_UNLOCKED1_REP};
            bins DecLcStTestLocked1   = {DEC_LC_ST_TEST_LOCKED1_REP};
            bins DecLcStTestUnlocked2 = {DEC_LC_ST_TEST_UNLOCKED2_REP};
            bins DecLcStTestLocked2   = {DEC_LC_ST_TEST_LOCKED2_REP};
            bins DecLcStTestUnlocked3 = {DEC_LC_ST_TEST_UNLOCKED3_REP};
            bins DecLcStTestLocked3   = {DEC_LC_ST_TEST_LOCKED3_REP};
            bins DecLcStTestUnlocked4 = {DEC_LC_ST_TEST_UNLOCKED4_REP};
            bins DecLcStTestLocked4   = {DEC_LC_ST_TEST_LOCKED4_REP};
            bins DecLcStTestUnlocked5 = {DEC_LC_ST_TEST_UNLOCKED5_REP};
            bins DecLcStTestLocked5   = {DEC_LC_ST_TEST_LOCKED5_REP};
            bins DecLcStTestUnlocked6 = {DEC_LC_ST_TEST_UNLOCKED6_REP};
            bins DecLcStTestLocked6   = {DEC_LC_ST_TEST_LOCKED6_REP};
            bins DecLcStTestUnlocked7 = {DEC_LC_ST_TEST_UNLOCKED7_REP};
            bins DecLcStDev           = {DEC_LC_ST_DEV_REP};
            bins DecLcStProd          = {DEC_LC_ST_PROD_REP};
            bins DecLcStProdEnd       = {DEC_LC_ST_PROD_END_REP};
            bins DecLcStRma           = {DEC_LC_ST_RMA_REP};
            bins DecLcStScrap         = {DEC_LC_ST_SCRAP_REP};
            bins DecLcStPostTrans     = {DEC_LC_ST_POST_TRANS_REP};
            bins DecLcStEscalate      = {DEC_LC_ST_ESCALATE_REP};
            bins DecLcStInvalid       = {DEC_LC_ST_INVALID_REP};
        }
    
        // Coverpoint for the counter with its bins.
        // Here, each bin is defined using the symbolic constant from lc_ctrl_state_pkg.
        lc_cnt_cp: coverpoint dec_lc_cnt {
            bins cnt0 =  { 0 };
            bins cnt1 =  { 1 };
            bins cnt2 =  { 2 };
            bins cnt3 =  { 3 };
            bins cnt4 =  { 4 };
            bins cnt5 =  { 5 };
            bins cnt6 =  { 6 };
            bins cnt7 =  { 7 };
            bins cnt8 =  { 8 };
            bins cnt9 =  { 9 };
            bins cnt10 = { 10 };
            bins cnt11 = { 11 };
            bins cnt12 = { 12 };
            bins cnt13 = { 13 };
            bins cnt14 = { 14 };
            bins cnt15 = { 15 };
            bins cnt16 = { 16 };
            bins cnt17 = { 17 };
            bins cnt18 = { 18 };
            bins cnt19 = { 19 };
            bins cnt20 = { 20 };
            bins cnt21 = { 21 };
            bins cnt22 = { 22 };
            bins cnt23 = { 23 };
            bins cnt24 = { 24 };
        }
    
        // Cross coverage between state and counter, recording the cross only when
        // the counter equals LcCnt0.
        initialized_lc_state_cr: cross lc_state_cp, lc_cnt_cp{
            bins cnt0_vs_stateX = binsof(lc_cnt_cp.cnt0);
        }

        // Coverpoint for the state signal with its bins.
        lc_early_prov_state: coverpoint next_dec_state {
            bins DecLcStDev           = {DEC_LC_ST_DEV_REP};
            bins DecLcStProd          = {DEC_LC_ST_PROD_REP};
            bins DecLcStProdEnd       = {DEC_LC_ST_PROD_END_REP};
            bins DecLcStRma           = {DEC_LC_ST_RMA_REP};
            bins DecLcStScrap         = {DEC_LC_ST_SCRAP_REP};
        }
        // Coverpoint for the state signal with its bins.
        lc_valid_early_prov_state_cp: coverpoint next_dec_state && st_trans_cmd;

        // the counter equals LcCnt0.
        from_TU0_to_Prov_cr: cross lc_valid_early_prov_state_cp, lc_state_cp{
            bins TestUnlcked0_to_PROV_X = binsof(lc_state_cp.DecLcStTestUnlocked0);
        }

        lc_voltatile_raw_unlock_cp: coverpoint sec_volatile_raw_unlock
        {
            bins Disabled = { 1'b0 };
            bins Enabled  = { 1'b1 };
        }
        
        // All life-cycle alerts are triggered.
        lc_ctrl_alerts_cp: coverpoint alerts
        {
            bins Alerts[] = { NumAlerts'(3'b001), NumAlerts'(3'b010), NumAlerts'(3'b100) };
        }
    endgroup

    initial begin
        lc_ctrl_cg lc_ctrl_cg1 = new();
    end

    localparam lc_state_e lc_states [NumLcStates] = {
        LcStRaw, LcStTestUnlocked0, LcStTestLocked0, LcStTestUnlocked1, LcStTestLocked1, LcStTestUnlocked2, LcStTestLocked2, LcStTestUnlocked3,
        LcStTestLocked3, LcStTestUnlocked4, LcStTestLocked4, LcStTestUnlocked5, LcStTestLocked5, LcStTestUnlocked6, LcStTestLocked6, LcStTestUnlocked7,
        LcStDev,LcStProd, LcStProdEnd, LcStRma, LcStScrap
    };

    covergroup lc_ctrl_state_transition_cg @(posedge clk_i);
        lc_state_transition_cp: coverpoint dec_lc_state {
                        // Raw to TestUnlocked0.
            bins RawTestUnlocked0 = (DEC_LC_ST_RMA_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED0_REP);
            // TestUnlocked0 to TestLocked0...6.
            bins TestUnlocked0TestLocked0 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED0_REP);
            bins TestUnlocked0TestLocked1 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED1_REP);
            bins TestUnlocked0TestLocked2 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED2_REP);
            bins TestUnlocked0TestLocked3 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED3_REP);
            bins TestUnlocked0TestLocked4 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED4_REP);
            bins TestUnlocked0TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked0TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked0 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked0Dev         = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked0Prod        = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked0ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked0Rma         = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked0Scrap       = (DEC_LC_ST_TEST_UNLOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked1 to TestLocked1...6.
            bins TestUnlocked1TestLocked1 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED1_REP);
            bins TestUnlocked1TestLocked2 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED2_REP);
            bins TestUnlocked1TestLocked3 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED3_REP);
            bins TestUnlocked1TestLocked4 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED4_REP);
            bins TestUnlocked1TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked1TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked1 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked1Dev         = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked1Prod        = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked1ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked1Rma         = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked1Scrap       = (DEC_LC_ST_TEST_UNLOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked2 to TestLocked2...6.
            bins TestUnlocked2TestLocked2 = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED2_REP);
            bins TestUnlocked2TestLocked3 = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED3_REP);
            bins TestUnlocked2TestLocked4 = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED4_REP);
            bins TestUnlocked2TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked2TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked2 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked2Dev         = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked2Prod        = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked2ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked2Rma         = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked2Scrap       = (DEC_LC_ST_TEST_UNLOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked3 to TestLocked3...6.
            bins TestUnlocked3TestLocked3 = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED3_REP);
            bins TestUnlocked3TestLocked4 = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED4_REP);
            bins TestUnlocked3TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked3TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked3 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked3Dev         = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked3Prod        = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked3ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked3Rma         = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked3Scrap       = (DEC_LC_ST_TEST_UNLOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked4 to TestLocked4...6.
            bins TestUnlocked4TestLocked4 = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED4_REP);
            bins TestUnlocked4TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked4TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked4 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked4Dev         = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked4Prod        = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked4ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked4Rma         = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked4Scrap       = (DEC_LC_ST_TEST_UNLOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked5 to TestLocked5...6.
            bins TestUnlocked5TestLocked5 = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED5_REP);
            bins TestUnlocked5TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked5 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked5Dev         = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked5Prod        = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked5ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked5Rma         = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked5Scrap       = (DEC_LC_ST_TEST_UNLOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked6 to TestLocked6.
            bins TestUnlocked6TestLocked6 = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_LOCKED6_REP);
            // TestUnlocked6 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked6Dev         = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked6Prod        = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked6ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked6Rma         = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked6Scrap       = (DEC_LC_ST_TEST_UNLOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
            // TestUnlocked7 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked7Dev         = (DEC_LC_ST_TEST_UNLOCKED7_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestUnlocked7Prod        = (DEC_LC_ST_TEST_UNLOCKED7_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestUnlocked7ProdEnd     = (DEC_LC_ST_TEST_UNLOCKED7_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestUnlocked7Rma         = (DEC_LC_ST_TEST_UNLOCKED7_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins TestUnlocked7Scrap       = (DEC_LC_ST_TEST_UNLOCKED7_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked0 to TestUnlocked1...7.
            bins TestLocked0TestUnlocked1 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED1_REP);
            bins TestLocked0TestUnlocked2 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED2_REP);
            bins TestLocked0TestUnlocked3 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED3_REP);
            bins TestLocked0TestUnlocked4 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED4_REP);
            bins TestLocked0TestUnlocked5 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED5_REP);
            bins TestLocked0TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked0TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked0 to DEV, PROD, PRODEND, SCR.
            bins TestLocked0Dev         = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked0Prod        = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked0ProdEnd     = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked0Scrap       = (DEC_LC_ST_TEST_LOCKED0_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked1 to TestUnlocked2...7.
            bins TestLocked1TestUnlocked2 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED2_REP);
            bins TestLocked1TestUnlocked3 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED3_REP);
            bins TestLocked1TestUnlocked4 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED4_REP);
            bins TestLocked1TestUnlocked5 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED5_REP);
            bins TestLocked1TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked1TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked1 to DEV, PROD, PRODEND, SCR.
            bins TestLocked1Dev         = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked1Prod        = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked1ProdEnd     = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked1Scrap       = (DEC_LC_ST_TEST_LOCKED1_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked2 to TestUnlocked3...7.
            bins TestLocked2TestUnlocked3 = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED3_REP);
            bins TestLocked2TestUnlocked4 = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED4_REP);
            bins TestLocked2TestUnlocked5 = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED5_REP);
            bins TestLocked2TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked2TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked2 to DEV, PROD, PRODEND, SCR.
            bins TestLocked2Dev         = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked2Prod        = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked2ProdEnd     = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked2Scrap       = (DEC_LC_ST_TEST_LOCKED2_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked3 to TestUnlocked4...7.
            bins TestLocked3TestUnlocked4 = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED4_REP);
            bins TestLocked3TestUnlocked5 = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED5_REP);
            bins TestLocked3TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked3TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked3 to DEV, PROD, PRODEND, SCR.
            bins TestLocked3Dev         = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked3Prod        = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked3ProdEnd     = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked3Scrap       = (DEC_LC_ST_TEST_LOCKED3_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked4 to TestUnlocked5...7.
            bins TestLocked4TestUnlocked5 = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED5_REP);
            bins TestLocked4TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked4TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked4 to DEV, PROD, PRODEND, SCR.
            bins TestLocked4Dev         = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked4Prod        = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked4ProdEnd     = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked4Scrap       = (DEC_LC_ST_TEST_LOCKED4_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked5 to TestUnlocked6...7.
            bins TestLocked5TestUnlocked6 = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED6_REP);
            bins TestLocked5TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked5 to DEV, PROD, PRODEND, SCR.
            bins TestLocked5Dev         = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked5Prod        = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked5ProdEnd     = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked5Scrap       = (DEC_LC_ST_TEST_LOCKED5_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // TestLocked6 to TestUnlocked6...7.
            bins TestLocked6TestUnlocked7 = (DEC_LC_ST_TEST_LOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_TEST_UNLOCKED7_REP);
            // TestLocked6 to DEV, PROD, PRODEND, SCR.
            bins TestLocked6Dev         = (DEC_LC_ST_TEST_LOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_DEV_REP);
            bins TestLocked6Prod        = (DEC_LC_ST_TEST_LOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins TestLocked6ProdEnd     = (DEC_LC_ST_TEST_LOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins TestLocked6Scrap       = (DEC_LC_ST_TEST_LOCKED6_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // DEV to PROD, PRODEND, RMA, SCR.
            bins LcStDevProd            = (DEC_LC_ST_DEV_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_REP);
            bins LcStDevProdEnd         = (DEC_LC_ST_DEV_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins LcStDevRma             = (DEC_LC_ST_DEV_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins LcStDevScrap           = (DEC_LC_ST_DEV_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // PROD to PRODEND, RMA, SCR.
            bins LcStProdProdEnd         = (DEC_LC_ST_PROD_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_PROD_END_REP);
            bins LcStProdRma             = (DEC_LC_ST_PROD_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_RMA_REP);
            bins LcStProdScrap           = (DEC_LC_ST_PROD_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // PRODEND to SCR.
            bins LcStProdEndScr          = (DEC_LC_ST_PROD_END_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);

            // RMA to SCR.
            bins LcStRmaScr              = (DEC_LC_ST_RMA_REP => DEC_LC_ST_POST_TRANS_REP => DEC_LC_ST_INVALID_REP =>  DEC_LC_ST_SCRAP_REP);
        }
    endgroup

    lc_ctrl_state_transition_cg lc_ctrl_state_transition_cg1 = new();

    otp_ctrl_pkg::otp_lc_data_t otp_lc_data_i;
    assign otp_lc_data_i = lc_ctrl.otp_lc_data_i;

    // Make sure all valid state transitions are covered.
    covergroup lc_ctrl_transition_cg(input lc_state_e src, input lc_state_e dst, input token_idx_e token) @(posedge clk_i);
        lc_ctrl_valid_transition_cp: coverpoint otp_lc_data_i.state iff (token != InvalidTokenIdx)
        {
            bins ValidTransition = ( src => [0:] => dst);
        }
        lc_ctrl_invalid_transition_cp: coverpoint otp_lc_data_i.state iff (token == InvalidTokenIdx && src != dst)
        {
            illegal_bins InvalidTransition = ( src => [0:] => dst);
        }
    endgroup

    lc_ctrl_transition_cg lc_ctrl_transitions_cg [NumLcStates][NumLcStates];

    initial begin
        for (int i = 0; i < NumLcStates; i++)
            for (int j = 0; j < NumLcStates; j++)
                lc_ctrl_transitions_cg[i][j] = new(lc_states[i], lc_states[j], TransTokenIdxMatrix[i][j]);
    end

    logic volatile_raw_unlock_i = lc_ctrl.u_lc_ctrl_fsm.volatile_raw_unlock_i;
    lc_state_e lc_state_q = lc_state_e'(lc_ctrl.u_lc_ctrl_fsm.lc_state_q);

    // Make sure we observe a successful volatile raw unlock transition.
    covergroup lc_ctrl_volatile_raw_unlock_transition_cg @(posedge clk_i);
        lc_ctrl_volatile_raw_unlock_transition_cp: coverpoint lc_state_q iff (sec_volatile_raw_unlock && volatile_raw_unlock_i)
        {
            bins VolatileRawUnlockTransition = ( LcStRaw => LcStTestUnlocked0);
        }
    endgroup

    lc_ctrl_volatile_raw_unlock_transition_cg lc_ctrl_volatile_raw_unlock_transition_cg1 = new();

    logic trans_cnt_oflw_error_o = lc_ctrl.u_lc_ctrl_fsm.trans_cnt_oflw_error_o;
    logic trans_invalid_error_o = lc_ctrl.u_lc_ctrl_fsm.trans_invalid_error_o;
    logic token_invalid_error_o = lc_ctrl.u_lc_ctrl_fsm.token_invalid_error_o;
    logic flash_rma_error_o = lc_ctrl.u_lc_ctrl_fsm.flash_rma_error_o;
    logic otp_prog_error_o = lc_ctrl.u_lc_ctrl_fsm.otp_prog_error_o;
    logic state_invalid_error_o = lc_ctrl.u_lc_ctrl_fsm.state_invalid_error_o;

    covergroup lc_ctrl_errors_cg @(posedge clk_i);
        lc_ctrl_cnt_oflw_error_cp: coverpoint trans_cnt_oflw_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_trans_invalid_error_cp: coverpoint trans_invalid_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_token_invalid_error_cp: coverpoint token_invalid_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_flash_rma_error_cp: coverpoint flash_rma_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_otp_prog_error_cp: coverpoint otp_prog_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_state_invalid_error_cp: coverpoint state_invalid_error_o
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
    endgroup

    initial begin
        lc_ctrl_errors_cg lc_ctrl_errors_cg1 = new();
    end

endinterface

`endif
