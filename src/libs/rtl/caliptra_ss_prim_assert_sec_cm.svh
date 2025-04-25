//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************
//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************
`ifndef CALIPTRA_SS_PRIM_ASSERT_SEC_CM_SVH
`define CALIPTRA_SS_PRIM_ASSERT_SEC_CM_SVH
  
`define CALIPTRA_SS_ASSERT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, ERR_NAME_)    \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, ERR_NAME_, \
                            `CALIPTRA_ASSERT_DEFAULT_CLK, `CALIPTRA_ASSERT_DEFAULT_RST)                      \
  `CALIPTRA_ASSUME_FPV(``NAME_``TriggerAfterAlertInit_S,                                            \
              $stable(rst_ni) == 0 |-> HIER_.ERR_NAME_ == 0 [*10])

`define CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_CALIPTRA_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_SS_ASSERT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_SS_ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_CALIPTRA_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_SS_ASSERT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_CALIPTRA_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_SS_ASSERT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, unused_err_o)

`define CALIPTRA_SS_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_CALIPTRA_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_SS_ASSERT_ERROR_TRIGGER_ALERT(NAME_, HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_SS_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, REG_TOP_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_CALIPTRA_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_SS_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, \
    REG_TOP_HIER_.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check, ALERT_, GATE_, MAX_CYCLES_)

`endif