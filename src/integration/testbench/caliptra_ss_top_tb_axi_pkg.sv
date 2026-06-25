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
//
// AXI types and interconnect configuration for the Caliptra SS testbench.

`include "soc_address_map_defines.svh"
`include "caliptra_ss_top_tb_intc_includes.svh"
`include "axi/caliptra_ss_tb_axi_typedef.svh"

package caliptra_ss_top_tb_axi_pkg;

  import tb_top_pkg::*;

  // Port counts (previously the AAXI_INTC_MASTER_CNT/AAXI_INTC_SLAVE_CNT
  // build defines; port index mapping in caliptra_ss_top_tb_intc_includes.svh)
  localparam int unsigned NumMgr = 5;   // Crossbar slave ports
  localparam int unsigned NumSub = 10;  // Crossbar master ports

  localparam int unsigned AddrWidth       = 64;
  localparam int unsigned DataWidth       = 64;
  localparam int unsigned NarrowDataWidth = 32;
  localparam int unsigned UserWidth       = 32;
  localparam int unsigned MgrIdWidth      = 5;
  localparam int unsigned XbarSubIdWidth  = MgrIdWidth + $clog2(NumMgr);

  // Manager (xbar slave-side) ports carrying 32-bit data; all others are
  // native 64-bit.
  localparam bit [NumMgr-1:0] MgrPortNarrow =
      (NumMgr'(1) << `CSS_INTC_MINTF_CPTRA_DMA_IDX) |
      (NumMgr'(1) << `CSS_INTC_MINTF_SOC_BFM_IDX);
  // Subordinate (xbar master-side) ports carrying 32-bit data.
  localparam bit [NumSub-1:0] SubPortNarrow =
      ~((NumSub'(1) << `CSS_INTC_SINTF_NC0_IDX) |
        (NumSub'(1) << `CSS_INTC_SINTF_MCU_ROM_IDX));

  typedef logic [AddrWidth-1:0]         axi_addr_t;
  typedef logic [DataWidth-1:0]         axi_data_t;
  typedef logic [DataWidth/8-1:0]       axi_strb_t;
  typedef logic [NarrowDataWidth-1:0]   axi_nrw_data_t;
  typedef logic [NarrowDataWidth/8-1:0] axi_nrw_strb_t;
  typedef logic [UserWidth-1:0]         axi_user_t;
  typedef logic [MgrIdWidth-1:0]        axi_id_t;
  typedef logic [XbarSubIdWidth-1:0]    axi_xbar_id_t;

  // Native 64-bit channels with the manager-port ID width (used at the
  // manager and subordinate ports of the interconnect).
  `CALIPTRA_SS_TB_AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_RESP_T(axi_rsp_t, axi_b_t, axi_r_t)

  // Narrow (32-bit data) channel variants for the data width converters.
  `CALIPTRA_SS_TB_AXI_TYPEDEF_W_CHAN_T(axi_nrw_w_t, axi_nrw_data_t, axi_nrw_strb_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_R_CHAN_T(axi_nrw_r_t, axi_nrw_data_t, axi_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_REQ_T(axi_nrw_req_t, axi_aw_t, axi_nrw_w_t, axi_ar_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_RESP_T(axi_nrw_rsp_t, axi_b_t, axi_nrw_r_t)

  // Channels at the xbar master ports (ID widened by $clog2(NumMgr)).
  `CALIPTRA_SS_TB_AXI_TYPEDEF_AW_CHAN_T(axi_xbar_aw_t, axi_addr_t, axi_xbar_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_B_CHAN_T(axi_xbar_b_t, axi_xbar_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_AR_CHAN_T(axi_xbar_ar_t, axi_addr_t, axi_xbar_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_R_CHAN_T(axi_xbar_r_t, axi_data_t, axi_xbar_id_t, axi_user_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_REQ_T(axi_xbar_req_t, axi_xbar_aw_t, axi_w_t, axi_xbar_ar_t)
  `CALIPTRA_SS_TB_AXI_TYPEDEF_RESP_T(axi_xbar_rsp_t, axi_xbar_b_t, axi_xbar_r_t)

  // Address map; end_addr is exclusive.
  localparam caliptra_ss_tb_axi_pkg::caliptra_ss_tb_xbar_rule_64_t [NumSub-1:0] AddrMap = '{
    '{
      idx:        `CSS_INTC_SINTF_UART_IDX,
      start_addr: 64'(`SOC_UART_BASE_ADDR),
      end_addr:   64'(`SOC_UART_BASE_ADDR) + 64'h100
    },
    '{
      idx:        `CSS_INTC_SINTF_SPI_IDX,
      start_addr: 64'(`SOC_SPI_HOST_BASE_ADDR),
      end_addr:   64'(`SOC_SPI_HOST_BASE_ADDR) + 64'h100
    },
    '{
      idx:        `CSS_INTC_SINTF_LCC_IDX,
      start_addr: 64'(`SOC_LC_CTRL_BASE_ADDR),
      end_addr:   64'(`SOC_LC_CTRL_BASE_ADDR) + 64'h200
    },
    '{
      idx:        `CSS_INTC_SINTF_SOC_SRAM_IDX,
      start_addr: 64'(SOC_SRAM_BASE_ADDR),
      end_addr:   64'(SOC_SRAM_BASE_ADDR) + 64'(SOC_SRAM_SIZE_BYTES)
    },
    '{
      idx:        `CSS_INTC_SINTF_FC_IDX,
      start_addr: 64'(`SOC_OTP_CTRL_BASE_ADDR),
      end_addr:   64'(`SOC_OTP_CTRL_BASE_ADDR) + 64'h200
    },
    '{
      idx:        `CSS_INTC_SINTF_MCI_IDX,
      start_addr: 64'(`SOC_MCI_TOP_MCI_REG_BASE_ADDR),
      end_addr:   64'(`SOC_MCI_TOP_MCU_SRAM_END_ADDR) + 64'h1 // Required to make the addr inclusive
    },
    '{
      idx:        `CSS_INTC_SINTF_CPTRA_SOC_IFC_IDX,
      start_addr: 64'(`SOC_MBOX_CSR_BASE_ADDR),
      end_addr:   64'(`SOC_MBOX_CSR_BASE_ADDR) + 64'h2_0001
    },
    '{
      idx:        `CSS_INTC_SINTF_MCU_ROM_IDX,
      start_addr: 64'h8000_0000,
      end_addr:   64'h8100_0000
    },
    '{
      idx:        `CSS_INTC_SINTF_I3C_IDX,
      start_addr: 64'(`SOC_I3CCSR_BASE_ADDR),
      end_addr:   64'(`SOC_I3CCSR_BASE_ADDR) + 64'h1000
    },
    '{
      idx:        `CSS_INTC_SINTF_NC0_IDX,
      start_addr: 64'h1000_0000,
      end_addr:   64'h1001_0000
    }
  };

  localparam caliptra_ss_tb_axi_pkg::caliptra_ss_tb_xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NumMgr,
    NoMstPorts:         NumSub,
    MaxMstTrans:        32'd8,
    MaxSlvTrans:        32'd8,
    FallThrough:        1'b0,
    LatencyMode:        caliptra_ss_tb_axi_pkg::CUT_ALL_PORTS,
    PipelineStages:     32'd0,
    AxiIdWidthSlvPorts: MgrIdWidth,
    AxiIdUsedSlvPorts:  MgrIdWidth,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AddrWidth,
    AxiDataWidth:       DataWidth,
    NoAddrRules:        NumSub
  };

endpackage
