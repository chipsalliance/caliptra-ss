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
(
    input logic clk,
    input logic rst_ni
);

    ext_dec_lc_state_t dec_lc_state;
    dec_lc_cnt_t       dec_lc_cnt;

    assign dec_lc_state = lc_ctrl.dec_lc_state;
    assign dec_lc_cnt = lc_ctrl.dec_lc_cnt;

    covergroup lc_ctrl_cg @(posedge clk);
        option.per_instance = 1;

        lc_state_cp: coverpoint dec_lc_state
        {
            bins DecLcStRaw             = { DecLcStRaw };
            bins DecLcStTestUnlocked0   = { DecLcStTestUnlocked0 };
            bins DecLcStTestLocked0     = { DecLcStTestLocked0 };
            bins DecLcStTestUnlocked1   = { DecLcStTestUnlocked1 };
            bins DecLcStTestLocked1     = { DecLcStTestLocked1 };
            bins DecLcStTestUnlocked2   = { DecLcStTestUnlocked2 };
            bins DecLcStTestLocked2     = { DecLcStTestLocked2 };
            bins DecLcStTestUnlocked3   = { DecLcStTestUnlocked3 };
            bins DecLcStTestLocked3     = { DecLcStTestLocked3 };
            bins DecLcStTestUnlocked4   = { DecLcStTestUnlocked4 };
            bins DecLcStTestLocked4     = { DecLcStTestLocked4 };
            bins DecLcStTestUnlocked5   = { DecLcStTestUnlocked5 };
            bins DecLcStTestLocked5     = { DecLcStTestLocked5 };
            bins DecLcStTestUnlocked6   = { DecLcStTestUnlocked6 };
            bins DecLcStTestLocked6     = { DecLcStTestLocked6 };
            bins DecLcStTestUnlocked7   = { DecLcStTestUnlocked7 };
            bins DecLcStDev             = { DecLcStDev };
            bins DecLcStProd            = { DecLcStProd };
            bins DecLcStProdEnd         = { DecLcStProdEnd };
            bins DecLcStRma             = { DecLcStRma };
            bins DecLcStScrap           = { DecLcStScrap };
            bins DecLcStPostTrans       = { DecLcStPostTrans };
            bins DecLcStEscalate        = { DecLcStEscalate };
            bins DecLcStInvalid         = { DecLcStInvalid };
        }

        lc_cnt_cp: coverpoint  dec_lc_cnt
        {
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
    endgroup

endinterface

`endif