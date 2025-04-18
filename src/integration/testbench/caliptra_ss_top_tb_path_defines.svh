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
//

`ifndef CALIPTRA_SS_TOP_TB_PATH_DEFINES
    `define CALIPTRA_SS_TOP_TB_PATH_DEFINES
    
    `ifndef CPTRA_SS_TB_TOP_NAME
      `define CPTRA_SS_TB_TOP_NAME caliptra_ss_top_tb
    `endif
    `ifndef CPTRA_SS_TOP_PATH
      `define CPTRA_SS_TOP_PATH      `CPTRA_SS_TB_TOP_NAME.caliptra_ss_dut
    `endif
    `ifndef MCI_PATH
      `define MCI_PATH      `CPTRA_SS_TOP_PATH.mci_top_i
    `endif
    `ifndef MCI_REG_TOP_PATH
      `define MCI_REG_TOP_PATH      `CPTRA_SS_TOP_PATH.mci_top_i.i_mci_reg_top
    `endif
    `ifndef MCU_PATH
      `define MCU_PATH      `CPTRA_SS_TOP_PATH.rvtop_wrapper
    `endif
    `ifndef MCU_DEC 
      `define MCU_DEC       `MCU_PATH.rvtop.veer.dec
    `endif
    `ifndef LCC_PATH
      `define LCC_PATH      `CPTRA_SS_TOP_PATH.u_lc_ctrl
    `endif
    `ifndef FC_PATH
      `define FC_PATH      `CPTRA_SS_TOP_PATH.u_otp_ctrl
    `endif
    `ifndef FC_MEM
      `define FC_MEM `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem
    `endif
    `ifndef CPTRA_CORE_TOP_PATH
      `define CPTRA_CORE_TOP_PATH      `CPTRA_SS_TOP_PATH.caliptra_top_dut
    `endif
    `ifndef MCI_WDT_PATH
      `define MCI_WDT_PATH  `MCI_PATH.i_mci_wdt_top
    `endif
    `ifndef FC_LCC_TB_SERV_PATH
      `define FC_LCC_TB_SERV_PATH      `CPTRA_SS_TB_TOP_NAME.u_caliptra_ss_top_tb_services.u_fc_lcc_tb_services
    `endif

`endif
