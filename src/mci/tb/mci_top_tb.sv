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
//======================================================================
//======================================================================

module mci_top_tb
  import mci_pkg::*;
  import axi_pkg::*;
  ();

  parameter MCI_TB_MCU_SRAM_SIZE_KB = 1024;

  //Mailbox configuration
  parameter MCI_TB_MBOX0_DMI_DLEN_ADDR = 0; //TODO define
  parameter MCI_TB_MBOX0_SIZE_KB = 4;
  localparam MCI_TB_MBOX0_DEPTH = (MCI_TB_MBOX0_SIZE_KB * KB * 8) / MCI_MBOX_DATA_W;
  localparam MCI_TB_MBOX0_ADDR_W = $clog2(MCI_TB_MBOX0_DEPTH);
  localparam MCI_TB_MBOX0_DEPTH_LOG2 = $clog2(MCI_TB_MBOX0_DEPTH);

  parameter MCI_TB_MBOX1_DMI_DLEN_ADDR = 0; //TODO define
  parameter MCI_TB_MBOX1_SIZE_KB = 4;
  localparam MCI_TB_MBOX1_DEPTH = (MCI_TB_MBOX1_SIZE_KB * KB * 8) / MCI_MBOX_DATA_W;
  localparam MCI_TB_MBOX1_ADDR_W = $clog2(MCI_TB_MBOX1_DEPTH);
  localparam MCI_TB_MBOX1_DEPTH_LOG2 = $clog2(MCI_TB_MBOX1_DEPTH);

  // MCI AXI Interface
  axi_if s_axi_w_if();
  axi_if s_axi_r_if();

  // MCU SRAM Interface
  mci_mcu_sram_if mci_mcu_sram_req_if();

  // Mbox0 SRAM Interface
  mci_mcu_sram_if#(.ADDR_WIDTH(MCI_TB_MBOX0_ADDR_W)) mci_mbox0_sram_req_if();

  // Mbox0 SRAM Interface
  mci_mcu_sram_if#(.ADDR_WIDTH(MCI_TB_MBOX1_ADDR_W)) mci_mbox1_sram_req_if(); 

  logic clk;

  // MCI Resets
  logic mci_rst_b;
  logic mci_pwrgood;
  
  // Straps
  logic [s_axi_r_if.UW-1:0] strap_mcu_lsu_axi_user;
  logic [s_axi_r_if.UW-1:0] strap_mcu_ifu_axi_user;
  logic [s_axi_r_if.UW-1:0] strap_clp_axi_user;

  // SRAM ADHOC connections
  logic mcu_sram_fw_exec_region_lock;

  // SOC Interrupts
  logic error_fatal;

  // NMI Vector 
  logic nmi_intr;

  mci_top
  #(
    .MCU_SRAM_SIZE_KB(MCI_TB_MCU_SRAM_SIZE_KB), 

    //Mailbox configuration
    .MCI_MBOX0_DMI_DLEN_ADDR(MCI_TB_MBOX0_DMI_DLEN_ADDR),
    .MCI_MBOX0_SIZE_KB(MCI_TB_MBOX0_SIZE_KB),
    .MCI_MBOX1_DMI_DLEN_ADDR(MCI_TB_MBOX1_DMI_DLEN_ADDR),
    .MCI_MBOX1_SIZE_KB(MCI_TB_MBOX1_SIZE_KB)
  )
  mci_top_inst
  (
  .clk,

  // MCI Resets
  .mci_rst_b,
  .mci_pwrgood,

  // MCI AXI Interface
  .s_axi_w_if,
  .s_axi_r_if,
  
  // Straps
  .strap_mcu_lsu_axi_user,
  .strap_mcu_ifu_axi_user,
  .strap_clp_axi_user,

  // SRAM ADHOC connections
  .mcu_sram_fw_exec_region_lock,

  // SOC Interrupts
  .error_fatal,

  // NMI Vector 
  .nmi_intr,

  // MCU SRAM Interface
  .mci_mcu_sram_req_if,

  // Mbox0 SRAM Interface
  .mci_mbox0_sram_req_if,

  // Mbox0 SRAM Interface
  .mci_mbox1_sram_req_if 
  );

endmodule