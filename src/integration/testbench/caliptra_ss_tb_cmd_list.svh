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
//         8'h80        - Load SHA Test Vector into MCU SRAM
//         --
//         8'h90        - FC/LCC Command Offset
//         8'h92        - FC/LCC CMD_FC_LCC_RESET
//         8'h93        - FC/LCC CMD_FORCE_FC_AWUSER_CPTR_CORE
//         8'h94        - FC/LCC CMD_FORCE_FC_AWUSER_MCU
//         8'h95        - FC/LCC CMD_RELEASE_AWUSER
//         8'h96        - FC/LCC CMD_FC_FORCE_ZEROIZATION
//         8'h97        - FC/LCC CMD_FC_FORCE_ZEROIZATION_RESET
//         8'h98        - FC/LCC CMD_RELEASE_ZEROIZATION
//         8'h99        - FC/LCC CMD_FORCE_LC_TOKENS
//         8'h9a        - FC/LCC CMD_LC_FORCE_RMA_SCRAP_PPD
//         8'h9b        - FC/LCC CMD_FC_TRIGGER_ESCALATION
//         8'ha2        - FC/LCC CMD_LC_TRIGGER_ESCALATION0
//         8'ha3        - FC/LCC CMD_LC_TRIGGER_ESCALATION1
//         --
//         8'hc0        - Disable ommand Offset
//
//         --
//         8'he0        - Disable ECC Error Injection
//         8'he2        - Inject Single-bit ECC errors into MCU DCCM
//         8'he3        - Inject Double-bit ECC errors into MCU DCCM
//         8'he4        - Inject Single-bit ECC errors into MCU MBOX 
//         8'he5        - Inject Double-bit ECC errors into MCU MBOX 
//         8'he6        - Disable ECC Error Injection MCU MBOX
//         8'he7        - Inject random ECC errors into MCU MBOX
//         8'he8        - Inject Single-bit ECC errors into MCU SRAM 
//         8'he9        - Inject Double-bit ECC errors into MCU SRAM 
//         8'hea        - Disable ECC Error Injection MCU SRAM
//         8'heb        - Inject random ECC errors into MCU SRAM
//         8'hec        - Inject MCI error fatal (nmi, mcu_sram_ecc_unc, mcu_sram_dmi_axi_collision)
//         8'hed        - Inject MCI error non fatal (mbox0/mbox1_ecc_unc)
//         8'hee        - Inject aggregate error fatal
//         8'hef        - Inject aggregate error non-fatal
//         8'hf0        - Inject notif0 intr conditions
//         --
//         8'hfb        - Set the isr_active bit
//         8'hfc        - Clear the isr_active bit
//         --
//         8'hff        - End the simulation with a Success status
localparam TB_SERVICE_CMD_NOPE              = 8'h00;
localparam TB_CMD_END_SIM_WITH_FAILURE      = 8'h01;

localparam TB_CMD_SHA_VECTOR_TO_MCU_SRAM    = 8'h80;

localparam FC_LCC_CMD_OFFSET                = 8'h90;
localparam CMD_FC_LCC_RESET                 = FC_LCC_CMD_OFFSET + 8'h02;
localparam CMD_FORCE_FC_AWUSER_CPTR_CORE    = FC_LCC_CMD_OFFSET + 8'h03;
localparam CMD_FORCE_FC_AWUSER_MCU          = FC_LCC_CMD_OFFSET + 8'h04;
localparam CMD_RELEASE_AWUSER               = FC_LCC_CMD_OFFSET + 8'h05;
localparam CMD_FC_FORCE_ZEROIZATION         = FC_LCC_CMD_OFFSET + 8'h06;
localparam CMD_FC_FORCE_ZEROIZATION_RESET   = FC_LCC_CMD_OFFSET + 8'h07;
localparam CMD_RELEASE_ZEROIZATION          = FC_LCC_CMD_OFFSET + 8'h08;
localparam CMD_FORCE_LC_TOKENS              = FC_LCC_CMD_OFFSET + 8'h09;
localparam CMD_LC_FORCE_RMA_SCRAP_PPD       = FC_LCC_CMD_OFFSET + 8'h0a;
localparam CMD_FC_TRIGGER_ESCALATION        = FC_LCC_CMD_OFFSET + 8'h0b;
localparam CMD_FC_LCC_EXT_CLK_500MHZ        = FC_LCC_CMD_OFFSET + 8'h0c;
localparam CMD_FC_LCC_EXT_CLK_160MHZ        = FC_LCC_CMD_OFFSET + 8'h0d;
localparam CMD_FC_LCC_EXT_CLK_400MHZ        = FC_LCC_CMD_OFFSET + 8'h0e;
localparam CMD_FC_LCC_EXT_CLK_1000MHZ       = FC_LCC_CMD_OFFSET + 8'h0f;
localparam CMD_FC_LCC_FAULT_DIGEST          = FC_LCC_CMD_OFFSET + 8'h10;
localparam CMD_FC_LCC_FAULT_BUS_ECC         = FC_LCC_CMD_OFFSET + 8'h11;
localparam CMD_LC_TRIGGER_ESCALATION0       = FC_LCC_CMD_OFFSET + 8'h12;
localparam CMD_LC_TRIGGER_ESCALATION1       = FC_LCC_CMD_OFFSET + 8'h13;
localparam CMD_LC_DISABLE_SVA               = FC_LCC_CMD_OFFSET + 8'h14;
localparam CMD_LC_ENABLE_SVA                = FC_LCC_CMD_OFFSET + 8'h15;
localparam CMD_FC_LCC_CORRECTABLE_FAULT     = FC_LCC_CMD_OFFSET + 8'h16;
localparam CMD_FC_LCC_UNCORRECTABLE_FAULT   = FC_LCC_CMD_OFFSET + 8'h17;
localparam CMD_LCC_FATAL_BUS_INTEG_ERROR    = FC_LCC_CMD_OFFSET + 8'h18;
localparam CMD_LC_FAULT_CNTR                = FC_LCC_CMD_OFFSET + 8'h19;
localparam CMD_DISABLE_CLK_BYP_ACK          = FC_LCC_CMD_OFFSET + 8'h1A;


localparam TB_DISABLE_MCU_SRAM_PROT_ASSERTS = 8'hc0;

localparam TB_CMD_DISABLE_INJECT_ECC_ERROR     = 8'he0;
localparam TB_CMD_INJECT_ECC_ERROR_SINGLE_DCCM = 8'he2;
localparam TB_CMD_INJECT_ECC_ERROR_DOUBLE_DCCM = 8'he3;
localparam TB_CMD_INJECT_MBOX_SRAM_SINGLE_ECC_ERROR = 8'he4;
localparam TB_CMD_INJECT_MBOX_SRAM_DOUBLE_ECC_ERROR = 8'he5;
localparam TB_CMD_DISABLE_MBOX_SRAM_ECC_ERROR_INJECTION = 8'he6;
localparam TB_CMD_RANDOMIZE_MBOX_SRAM_ECC_ERROR_INJECTION = 8'he7;
localparam TB_CMD_INJECT_MCU_SRAM_SINGLE_ECC_ERROR = 8'he8;
localparam TB_CMD_INJECT_MCU_SRAM_DOUBLE_ECC_ERROR = 8'he9;
localparam TB_CMD_DISABLE_MCU_SRAM_ECC_ERROR_INJECTION = 8'hea;
localparam TB_CMD_RANDOMIZE_MCU_SRAM_ECC_ERROR_INJECTION = 8'heb;
localparam TB_CMD_INJECT_MCI_ERROR_FATAL = 8'hec;
localparam TB_CMD_INJECT_MCI_ERROR_NON_FATAL = 8'hed;
localparam TB_CMD_INJECT_AGG_ERROR_FATAL = 8'hee;
localparam TB_CMD_INJECT_AGG_ERROR_NON_FATAL = 8'hef;
localparam TB_CMD_INJECT_NOTIF0 = 8'hf0;

localparam TB_CMD_COLD_RESET                  = 8'hF5;
localparam TB_CMD_WARM_RESET                  = 8'hF6;

localparam TB_CMD_INCR_INTR_ACTIVE            = 8'hFB;
localparam TB_CMD_DECR_INTR_ACTIVE            = 8'hFC;
localparam TB_CMD_END_SIM_WITH_SUCCESS        = 8'hFF;

`endif // CALIPTRA_SS_TB_CMD_LIST_SVH
