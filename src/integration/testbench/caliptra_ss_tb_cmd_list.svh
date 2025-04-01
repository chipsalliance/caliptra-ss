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

`include "caliptra_ss_top_tb_path_defines.svh"

//=========================================================================-
// STDOUT and Trace Logic
//=========================================================================-
// NOTE: The following decode is used to interpret TB operation requests by the
//       MCU via register writes to the STDOUT register (DEBUG_OUT).
//       Functionality currently implemented at this offset is as follows
//       (relative to the WriteData used to trigger that function):
//         8'h0         - Do nothing
//         8'h1         - Kill the simulation with a Failed status
//         8'h2 : 8'h5  - Do nothing
//         8'h6 : 8'h7E - WriteData is an ASCII character - dump to console.log
//         8'h7F        - Do nothing
//         --
//         8'hb0        - FC/LCC Command Offset
//         8'hb2        - FC/LCC CMD_FC_LCC_RESET              
//         8'hb3        - FC/LCC CMD_FORCE_FC_AWUSER_CPTR_CORE 
//         8'hb4        - FC/LCC CMD_FORCE_FC_AWUSER_MCU       
//         8'hb5        - FC/LCC CMD_RELEASE_AWUSER            
//         8'hb6        - FC/LCC CMD_FC_FORCE_ZEROIZATION      
//         8'hb7        - FC/LCC CMD_FC_FORCE_ZEROIZATION_RESET
//         8'hb8        - FC/LCC CMD_RELEASE_ZEROIZATION       
//         8'hb9        - FC/LCC CMD_FORCE_LC_TOKENS           
//         8'hba        - FC/LCC CMD_LC_FORCE_RMA_SCRAP_PPD    
//         --
//         8'he0        - Disable ECC Error Injection
//         8'he2        - Inject Single-bit ECC errors into MCU DCCM
//         8'he3        - Inject Double-bit ECC errors into MCU DCCM
//         --
//         8'hff        - End the simulation with a Success status
localparam TB_SERVICE_CMD_NOPE              = 8'h00;
localparam TB_CMD_END_SIM_WITH_FAILURE      = 8'h01;

localparam FC_LCC_CMD_OFFSET                = 8'hb0;
localparam CMD_FC_LCC_RESET                 = FC_LCC_CMD_OFFSET + 8'h02;
localparam CMD_FORCE_FC_AWUSER_CPTR_CORE    = FC_LCC_CMD_OFFSET + 8'h03;
localparam CMD_FORCE_FC_AWUSER_MCU          = FC_LCC_CMD_OFFSET + 8'h04;
localparam CMD_RELEASE_AWUSER               = FC_LCC_CMD_OFFSET + 8'h05;
localparam CMD_FC_FORCE_ZEROIZATION         = FC_LCC_CMD_OFFSET + 8'h06;
localparam CMD_FC_FORCE_ZEROIZATION_RESET   = FC_LCC_CMD_OFFSET + 8'h07;
localparam CMD_RELEASE_ZEROIZATION          = FC_LCC_CMD_OFFSET + 8'h08;
localparam CMD_FORCE_LC_TOKENS              = FC_LCC_CMD_OFFSET + 8'h09;
localparam CMD_LC_FORCE_RMA_SCRAP_PPD       = FC_LCC_CMD_OFFSET + 8'h0a;

localparam TB_CMD_DISABLE_INJECT_ECC_ERROR     = 8'he0;
localparam TB_CMD_INJECT_ECC_ERROR_SINGLE_DCCM = 8'he2;
localparam TB_CMD_INJECT_ECC_ERROR_DOUBLE_DCCM = 8'he3;

localparam TB_CMD_END_SIM_WITH_SUCCESS         = 8'hFF;

`endif // CALIPTRA_SS_TB_CMD_LIST_SVH
