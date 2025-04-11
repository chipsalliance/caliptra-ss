//********************************************************************************
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
//********************************************************************************

`ifndef CALIPTRA_SS_TOP_TB_INTC_INCLUDES_SVH
`define CALIPTRA_SS_TOP_TB_INTC_INCLUDES_SVH

    // Interconnect Config
    `define CSS_INTC_MINTF_MCU_LSU_IDX    0
    `define CSS_INTC_MINTF_MCU_IFU_IDX    1
    `define CSS_INTC_MINTF_MCU_SB_IDX     2
    `define CSS_INTC_MINTF_CPTRA_DMA_IDX  3
    `define CSS_INTC_MINTF_SOC_BFM_IDX    4

    `define CSS_INTC_SINTF_NC0_IDX           0 /* Currently unconnected */
    `define CSS_INTC_SINTF_I3C_IDX           1
    `define CSS_INTC_SINTF_MCU_ROM_IDX       2
    `define CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX 3
    `define CSS_INTC_SINTF_MCI_IDX           4
    `define CSS_INTC_SINTF_FC_IDX            5
    `define CSS_INTC_SINTF_NC1_IDX           6 /* Currently unconnected */
    `define CSS_INTC_SINTF_LCC_IDX           7


`endif // CALIPTRA_SS_TOP_TB_INTC_INCLUDES_SVH
