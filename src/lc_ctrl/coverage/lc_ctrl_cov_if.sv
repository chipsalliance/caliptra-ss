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
    assign sec_volatile_raw_unlock = lc_ctrl.lc_sec_volatile_raw_unlock_en_i;

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

    otp_ctrl_pkg::otp_lc_data_t otp_lc_data_i;
    assign otp_lc_data_i = lc_ctrl.otp_lc_data_i;

    logic ack;
    assign ack = lc_ctrl.lc_otp_program_i.ack;

    lc_state_t states[2];
    logic adv;

    covergroup lc_ctrl_transitions_cg with function sample(lc_state_e src, lc_state_e dst);
        option.per_instance = 1;

        foobar: coverpoint {src, dst}
        {
            bins RawTestUnlocked0 = {{LcStRaw, LcStTestUnlocked0}};
            // TestUnlocked0 to TestLocked0...6.
            bins TestUnlocked0TestLocked0 = {{LcStTestUnlocked0, LcStTestLocked0}};
            bins TestUnlocked0TestLocked1 = {{LcStTestUnlocked0, LcStTestLocked1}};
            bins TestUnlocked0TestLocked2 = {{LcStTestUnlocked0, LcStTestLocked2}};
            bins TestUnlocked0TestLocked3 = {{LcStTestUnlocked0, LcStTestLocked3}};
            bins TestUnlocked0TestLocked4 = {{LcStTestUnlocked0, LcStTestLocked4}};
            bins TestUnlocked0TestLocked5 = {{LcStTestUnlocked0, LcStTestLocked5}};
            bins TestUnlocked0TestLocked6 = {{LcStTestUnlocked0, LcStTestLocked6}};
            // TestUnlocked0 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked0Dev         = {{LcStTestUnlocked0, LcStDev}};
            bins TestUnlocked0Prod        = {{LcStTestUnlocked0, LcStProd}};
            bins TestUnlocked0ProdEnd     = {{LcStTestUnlocked0, LcStProdEnd}};
            bins TestUnlocked0Rma         = {{LcStTestUnlocked0, LcStRma}};
            bins TestUnlocked0Scrap       = {{LcStTestUnlocked0, LcStScrap}};
            // TestUnlocked1 to TestLocked1...6.
            bins TestUnlocked1TestLocked1 = {{LcStTestUnlocked1, LcStTestLocked1}};
            bins TestUnlocked1TestLocked2 = {{LcStTestUnlocked1, LcStTestLocked2}};
            bins TestUnlocked1TestLocked3 = {{LcStTestUnlocked1, LcStTestLocked3}};
            bins TestUnlocked1TestLocked4 = {{LcStTestUnlocked1, LcStTestLocked4}};
            bins TestUnlocked1TestLocked5 = {{LcStTestUnlocked1, LcStTestLocked5}};
            bins TestUnlocked1TestLocked6 = {{LcStTestUnlocked1, LcStTestLocked6}};
            // TestUnlocked1 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked1Dev         = {{LcStTestUnlocked1, LcStDev}};
            bins TestUnlocked1Prod        = {{LcStTestUnlocked1, LcStProd}};
            bins TestUnlocked1ProdEnd     = {{LcStTestUnlocked1, LcStProdEnd}};
            bins TestUnlocked1Rma         = {{LcStTestUnlocked1, LcStRma}};
            bins TestUnlocked1Scrap       = {{LcStTestUnlocked1, LcStScrap}};
            // TestUnlocked2 to TestLocked2...6.
            bins TestUnlocked2TestLocked2 = {{LcStTestUnlocked2, LcStTestLocked2}};
            bins TestUnlocked2TestLocked3 = {{LcStTestUnlocked2, LcStTestLocked3}};
            bins TestUnlocked2TestLocked4 = {{LcStTestUnlocked2, LcStTestLocked4}};
            bins TestUnlocked2TestLocked5 = {{LcStTestUnlocked2, LcStTestLocked5}};
            bins TestUnlocked2TestLocked6 = {{LcStTestUnlocked2, LcStTestLocked6}};
            // TestUnlocked2 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked2Dev         = {{LcStTestUnlocked2, LcStDev}};
            bins TestUnlocked2Prod        = {{LcStTestUnlocked2, LcStProd}};
            bins TestUnlocked2ProdEnd     = {{LcStTestUnlocked2, LcStProdEnd}};
            bins TestUnlocked2Rma         = {{LcStTestUnlocked2, LcStRma}};
            bins TestUnlocked2Scrap       = {{LcStTestUnlocked2, LcStScrap}};
            // TestUnlocked3 to TestLocked3...6.
            bins TestUnlocked3TestLocked3 = {{LcStTestUnlocked3, LcStTestLocked3}};
            bins TestUnlocked3TestLocked4 = {{LcStTestUnlocked3, LcStTestLocked4}};
            bins TestUnlocked3TestLocked5 = {{LcStTestUnlocked3, LcStTestLocked5}};
            bins TestUnlocked3TestLocked6 = {{LcStTestUnlocked3, LcStTestLocked6}};
            // TestUnlocked3 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked3Dev         = {{LcStTestUnlocked3, LcStDev}};
            bins TestUnlocked3Prod        = {{LcStTestUnlocked3, LcStProd}};
            bins TestUnlocked3ProdEnd     = {{LcStTestUnlocked3, LcStProdEnd}};
            bins TestUnlocked3Rma         = {{LcStTestUnlocked3, LcStRma}};
            bins TestUnlocked3Scrap       = {{LcStTestUnlocked3, LcStScrap}};
            // TestUnlocked4 to TestLocked4...6.
            bins TestUnlocked4TestLocked4 = {{LcStTestUnlocked4, LcStTestLocked4}};
            bins TestUnlocked4TestLocked5 = {{LcStTestUnlocked4, LcStTestLocked5}};
            bins TestUnlocked4TestLocked6 = {{LcStTestUnlocked4, LcStTestLocked6}};
            // TestUnlocked4 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked4Dev         = {{LcStTestUnlocked4, LcStDev}};
            bins TestUnlocked4Prod        = {{LcStTestUnlocked4, LcStProd}};
            bins TestUnlocked4ProdEnd     = {{LcStTestUnlocked4, LcStProdEnd}};
            bins TestUnlocked4Rma         = {{LcStTestUnlocked4, LcStRma}};
            bins TestUnlocked4Scrap       = {{LcStTestUnlocked4, LcStScrap}};
            // TestUnlocked5 to TestLocked5...6.
            bins TestUnlocked5TestLocked5 = {{LcStTestUnlocked5, LcStTestLocked5}};
            bins TestUnlocked5TestLocked6 = {{LcStTestUnlocked5, LcStTestLocked6}};
            // TestUnlocked5 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked5Dev         = {{LcStTestUnlocked5, LcStDev}};
            bins TestUnlocked5Prod        = {{LcStTestUnlocked5, LcStProd}};
            bins TestUnlocked5ProdEnd     = {{LcStTestUnlocked5, LcStProdEnd}};
            bins TestUnlocked5Rma         = {{LcStTestUnlocked5, LcStRma}};
            bins TestUnlocked5Scrap       = {{LcStTestUnlocked5, LcStScrap}};
            // TestUnlocked6 to TestLocked6.
            bins TestUnlocked6TestLocked6 = {{LcStTestUnlocked6, LcStTestLocked6}};
            // TestUnlocked6 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked6Dev         = {{LcStTestUnlocked6, LcStDev}};
            bins TestUnlocked6Prod        = {{LcStTestUnlocked6, LcStProd}};
            bins TestUnlocked6ProdEnd     = {{LcStTestUnlocked6, LcStProdEnd}};
            bins TestUnlocked6Rma         = {{LcStTestUnlocked6, LcStRma}};
            bins TestUnlocked6Scrap       = {{LcStTestUnlocked6, LcStScrap}};
            // TestUnlocked7 to DEV, PROD, PRODEND, RMA, SCR.
            bins TestUnlocked7Dev         = {{LcStTestUnlocked7, LcStDev}};
            bins TestUnlocked7Prod        = {{LcStTestUnlocked7, LcStProd}};
            bins TestUnlocked7ProdEnd     = {{LcStTestUnlocked7, LcStProdEnd}};
            bins TestUnlocked7Rma         = {{LcStTestUnlocked7, LcStRma}};
            bins TestUnlocked7Scrap       = {{LcStTestUnlocked7, LcStScrap}};

            // TestLocked0 to TestUnlocked1...7.
            bins TestLocked0TestUnlocked1 = {{LcStTestLocked0, LcStTestUnlocked1}};
            bins TestLocked0TestUnlocked2 = {{LcStTestLocked0, LcStTestUnlocked2}};
            bins TestLocked0TestUnlocked3 = {{LcStTestLocked0, LcStTestUnlocked3}};
            bins TestLocked0TestUnlocked4 = {{LcStTestLocked0, LcStTestUnlocked4}};
            bins TestLocked0TestUnlocked5 = {{LcStTestLocked0, LcStTestUnlocked5}};
            bins TestLocked0TestUnlocked6 = {{LcStTestLocked0, LcStTestUnlocked6}};
            bins TestLocked0TestUnlocked7 = {{LcStTestLocked0, LcStTestUnlocked7}};
            // TestLocked0 to DEV, PROD, PRODEND, SCR.
            bins TestLocked0Dev         = {{LcStTestLocked0, LcStDev}};
            bins TestLocked0Prod        = {{LcStTestLocked0, LcStProd}};
            bins TestLocked0ProdEnd     = {{LcStTestLocked0, LcStProdEnd}};
            bins TestLocked0Scrap       = {{LcStTestLocked0, LcStScrap}};

            // TestLocked1 to TestUnlocked2...7.
            bins TestLocked1TestUnlocked2 = {{LcStTestLocked1, LcStTestUnlocked2}};
            bins TestLocked1TestUnlocked3 = {{LcStTestLocked1, LcStTestUnlocked3}};
            bins TestLocked1TestUnlocked4 = {{LcStTestLocked1, LcStTestUnlocked4}};
            bins TestLocked1TestUnlocked5 = {{LcStTestLocked1, LcStTestUnlocked5}};
            bins TestLocked1TestUnlocked6 = {{LcStTestLocked1, LcStTestUnlocked6}};
            bins TestLocked1TestUnlocked7 = {{LcStTestLocked1, LcStTestUnlocked7}};
            // TestLocked1 to DEV, PROD, PRODEND, SCR.
            bins TestLocked1Dev         = {{LcStTestLocked1, LcStDev}};
            bins TestLocked1Prod        = {{LcStTestLocked1, LcStProd}};
            bins TestLocked1ProdEnd     = {{LcStTestLocked1, LcStProdEnd}};
            bins TestLocked1Scrap       = {{LcStTestLocked1, LcStScrap}};

            // TestLocked2 to TestUnlocked3...7.
            bins TestLocked2TestUnlocked3 = {{LcStTestLocked2, LcStTestUnlocked3}};
            bins TestLocked2TestUnlocked4 = {{LcStTestLocked2, LcStTestUnlocked4}};
            bins TestLocked2TestUnlocked5 = {{LcStTestLocked2, LcStTestUnlocked5}};
            bins TestLocked2TestUnlocked6 = {{LcStTestLocked2, LcStTestUnlocked6}};
            bins TestLocked2TestUnlocked7 = {{LcStTestLocked2, LcStTestUnlocked7}};
            // TestLocked2 to DEV, PROD, PRODEND, SCR.
            bins TestLocked2Dev         = {{LcStTestLocked2, LcStDev}};
            bins TestLocked2Prod        = {{LcStTestLocked2, LcStProd}};
            bins TestLocked2ProdEnd     = {{LcStTestLocked2, LcStProdEnd}};
            bins TestLocked2Scrap       = {{LcStTestLocked2, LcStScrap}};

            // TestLocked3 to TestUnlocked4...7.
            bins TestLocked3TestUnlocked4 = {{LcStTestLocked3, LcStTestUnlocked4}};
            bins TestLocked3TestUnlocked5 = {{LcStTestLocked3, LcStTestUnlocked5}};
            bins TestLocked3TestUnlocked6 = {{LcStTestLocked3, LcStTestUnlocked6}};
            bins TestLocked3TestUnlocked7 = {{LcStTestLocked3, LcStTestUnlocked7}};
            // TestLocked3 to DEV, PROD, PRODEND, SCR.
            bins TestLocked3Dev         = {{LcStTestLocked3, LcStDev}};
            bins TestLocked3Prod        = {{LcStTestLocked3, LcStProd}};
            bins TestLocked3ProdEnd     = {{LcStTestLocked3, LcStProdEnd}};
            bins TestLocked3Scrap       = {{LcStTestLocked3, LcStScrap}};

            // TestLocked4 to TestUnlocked5...7.
            bins TestLocked4TestUnlocked5 = {{LcStTestLocked4, LcStTestUnlocked5}};
            bins TestLocked4TestUnlocked6 = {{LcStTestLocked4, LcStTestUnlocked6}};
            bins TestLocked4TestUnlocked7 = {{LcStTestLocked4, LcStTestUnlocked7}};
            // TestLocked4 to DEV, PROD, PRODEND, SCR.
            bins TestLocked4Dev         = {{LcStTestLocked4, LcStDev}};
            bins TestLocked4Prod        = {{LcStTestLocked4, LcStProd}};
            bins TestLocked4ProdEnd     = {{LcStTestLocked4, LcStProdEnd}};
            bins TestLocked4Scrap       = {{LcStTestLocked4, LcStScrap}};

            // TestLocked5 to TestUnlocked6...7.
            bins TestLocked5TestUnlocked6 = {{LcStTestLocked5, LcStTestUnlocked6}};
            bins TestLocked5TestUnlocked7 = {{LcStTestLocked5, LcStTestUnlocked7}};
            // TestLocked5 to DEV, PROD, PRODEND, SCR.
            bins TestLocked5Dev         = {{LcStTestLocked5, LcStDev}};
            bins TestLocked5Prod        = {{LcStTestLocked5, LcStProd}};
            bins TestLocked5ProdEnd     = {{LcStTestLocked5, LcStProdEnd}};
            bins TestLocked5Scrap       = {{LcStTestLocked5, LcStScrap}};

            // TestLocked6 to TestUnlocked6...7.
            bins TestLocked6TestUnlocked7 = {{LcStTestLocked6, LcStTestUnlocked7}};
            // TestLocked6 to DEV, PROD, PRODEND, SCR.
            bins TestLocked6Dev         = {{LcStTestLocked6, LcStDev}};
            bins TestLocked6Prod        = {{LcStTestLocked6, LcStProd}};
            bins TestLocked6ProdEnd     = {{LcStTestLocked6, LcStProdEnd}};
            bins TestLocked6Scrap       = {{LcStTestLocked6, LcStScrap}};

            // DEV to PROD, PRODEND, RMA, SCR.
            bins LcStDevProd            = {{LcStDev, LcStProd}};
            bins LcStDevProdEnd         = {{LcStDev, LcStProdEnd}};
            bins LcStDevRma             = {{LcStDev, LcStRma}};
            bins LcStDevScrap           = {{LcStDev, LcStScrap}};

            // PROD to PRODEND, RMA, SCR.
            bins LcStProdProdEnd         = {{LcStProd, LcStProdEnd}};
            bins LcStProdRma             = {{LcStProd, LcStRma}};
            bins LcStProdScrap           = {{LcStProd, LcStScrap}};

            // PRODEND to SCR.
            bins LcStProdEndScr          = {{LcStProdEnd, LcStScrap}};

            // RMA to SCR.
            bins LcStRmaScr              = {{LcStRma, LcStScrap}};
        }
    endgroup

    lc_ctrl_transitions_cg trans_cg = new();

    always @(posedge clk_i) begin
        if (!rst_ni) begin
            adv <= '0;
        end else if (ack && adv) begin
            states[0] <= states[1];
            states[1] <= otp_lc_data_i.state;
        end

        // Only advance states for every second otp ack.
        if (ack) begin
            adv <= adv ^ 1'b1;
        end

        for (int i = 0; i < NumLcStates; i++) begin
            if (states[0] == lc_states[i]) begin
                for (int j = 0; j < NumLcStates; j++) begin
                    if (states[1] == lc_states[j] && TransTokenIdxMatrix[i][j] != InvalidTokenIdx) begin
                        trans_cg.sample(lc_states[i], lc_states[j]);
                    end
                end
            end
        end
    end

    logic volatile_raw_unlock_i;
    assign volatile_raw_unlock_i = lc_ctrl.u_lc_ctrl_fsm.volatile_raw_unlock_i;
    
    lc_state_e lc_state_q;
    assign lc_state_q = lc_state_e'(lc_ctrl.u_lc_ctrl_fsm.lc_state_q);

    // Make sure we observe a successful volatile raw unlock transition.
    covergroup lc_ctrl_volatile_raw_unlock_transition_cg @(posedge clk_i);
        lc_ctrl_volatile_raw_unlock_transition_cp: coverpoint lc_state_q iff (sec_volatile_raw_unlock && volatile_raw_unlock_i)
        {
            bins VolatileRawUnlockTransition = ( LcStRaw => LcStTestUnlocked0);
        }
    endgroup

    lc_ctrl_volatile_raw_unlock_transition_cg lc_ctrl_volatile_raw_unlock_transition_cg1 = new();

    logic trans_cnt_oflw_error, trans_invalid_error, token_invalid_error, flash_rma_error, otp_prog_error, state_invalid_error;
    assign trans_cnt_oflw_error = lc_ctrl.u_lc_ctrl_fsm.trans_cnt_oflw_error_o;
    assign trans_invalid_error = lc_ctrl.u_lc_ctrl_fsm.trans_invalid_error_o;
    assign token_invalid_error = lc_ctrl.u_lc_ctrl_fsm.token_invalid_error_o;
    assign flash_rma_error = lc_ctrl.u_lc_ctrl_fsm.flash_rma_error_o;
    assign otp_prog_error = lc_ctrl.u_lc_ctrl_fsm.otp_prog_error_o;
    assign state_invalid_error = lc_ctrl.u_lc_ctrl_fsm.state_invalid_error_o;

    covergroup lc_ctrl_errors_cg @(posedge clk_i);
        lc_ctrl_cnt_oflw_error_cp: coverpoint trans_cnt_oflw_error
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_trans_invalid_error_cp: coverpoint trans_invalid_error
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_token_invalid_error_cp: coverpoint token_invalid_error
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_flash_rma_error_cp: coverpoint flash_rma_error
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_otp_prog_error_cp: coverpoint otp_prog_error
        {
            bins On  = { 1'b1 };
            bins Off = { 1'b0 };
        }
        lc_ctrl_state_invalid_error_cp: coverpoint state_invalid_error
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
