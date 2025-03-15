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

// =================== DESCRIPTION ===================
// This module provides supporting functionality that is shared between the standalone
// and UVM benches for caliptra_top.
// This includes the following:
//  - Contains all SRAM exports
//  - Mem init functions (from .hex files, with ECC functionality as applicable)
//  - RV Firmware STDOUT behavior (ASCII dump + sim kill + Error injection + interrupt + security_state)
//  - RV and internal AHB interface monitoring to activity dumps
// The purpose of this module is to centralize identical code that is shared to
// improve maintainability.
// ===================================================

`default_nettype none

`ifndef CPTRA_SS_TB_TOP_NAME
  `define CPTRA_SS_TB_TOP_NAME caliptra_ss_top_tb
`endif
`ifndef CPTRA_SS_TOP_PATH
  `define CPTRA_TOP_PATH      `CPTRA_SS_TB_TOP_NAME.caliptra_ss_dut
`endif

`ifndef CPTRA_CORE_TOP_PATH
  `define CPTRA_TOP_PATH      `CPTRA_SS_TOP_PATH.caliptra_ss_dut.caliptra_top_dut
`endif


module caliptra_ss_top_tb_services 
#(
    parameter UVM_TB = 0
) (
    input wire                    clk,

    input wire                    cptra_rst_b,
    input wire                    valid_tb_service_cmd,
    input wire [7:0]             valid_tb_service_data
);



/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */


endmodule
