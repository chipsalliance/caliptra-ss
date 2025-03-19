//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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

`ifndef CALIPTRA_SS_TB_CMD_LIST_SVH
`define CALIPTRA_SS_TB_CMD_LIST_SVH


`ifndef CPTRA_SS_TB_TOP_NAME
  `define CPTRA_SS_TB_TOP_NAME caliptra_ss_top_tb
`endif
`ifndef CPTRA_SS_TOP_PATH
  `define CPTRA_SS_TOP_PATH      `CPTRA_SS_TB_TOP_NAME.caliptra_ss_dut
`endif
`ifndef MCI_PATH
  `define MCI_PATH      `CPTRA_SS_TOP_PATH.mci_top_i
`endif
`ifndef LCC_PATH
  `define LCC_PATH      `CPTRA_SS_TOP_PATH.u_lc_ctrl
`endif
`ifndef FC_PATH
  `define FC_PATH      `CPTRA_SS_TOP_PATH.u_otp_ctrl
`endif
`ifndef CPTRA_CORE_TOP_PATH
  `define CPTRA_CORE_TOP_PATH      `CPTRA_SS_TOP_PATH.caliptra_top_dut
`endif

localparam FC_LCC_CMD_OFFSET                = 8'hb0;

localparam TB_SERVICE_CMD_NOPE              = 8'h00;


localparam CMD_FC_LCC_RESET                 = FC_LCC_CMD_OFFSET + 8'h02;
localparam CMD_FORCE_AWUSER_0               = FC_LCC_CMD_OFFSET + 8'h03;
localparam CMD_FORCE_AWUSER_1               = FC_LCC_CMD_OFFSET + 8'h04;
localparam CMD_RELEASE_AWUSER               = FC_LCC_CMD_OFFSET + 8'h05;
localparam CMD_FC_FORCE_ZEROIZATION         = FC_LCC_CMD_OFFSET + 8'h06;
localparam CMD_FC_FORCE_ZEROIZATION_RESET   = FC_LCC_CMD_OFFSET + 8'h07;
localparam CMD_RELEASE_ZEROIZATION          = FC_LCC_CMD_OFFSET + 8'h08;
localparam CMD_FORCE_LC_TOKENS              = FC_LCC_CMD_OFFSET + 8'h09;

`endif // CALIPTRA_SS_TB_CMD_LIST_SVH
