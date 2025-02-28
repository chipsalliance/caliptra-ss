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

  parameter MCI_TB_MCU_SRAM_SIZE_KB = 512;

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
  axi_if s_axi_w_if(.clk('0), .rst_n('0));
  axi_if s_axi_r_if(.clk('0), .rst_n('0));
  

  // MCU SRAM Interface
  mci_mcu_sram_if mci_mcu_sram_req_if(.clk('0), .rst_b('0));

  // Mbox0 SRAM Interface
  mci_mcu_sram_if#(.ADDR_WIDTH(MCI_TB_MBOX0_ADDR_W)) mci_mbox0_sram_req_if(.clk('0), .rst_b('0));

  // Mbox0 SRAM Interface
  mci_mcu_sram_if#(.ADDR_WIDTH(MCI_TB_MBOX1_ADDR_W)) mci_mbox1_sram_req_if(.clk('0), .rst_b('0)); 

  mci_top
  #(
    .MCU_SRAM_SIZE_KB(MCI_TB_MCU_SRAM_SIZE_KB), 

    //Mailbox configuration
    .MCI_MBOX0_SIZE_KB(MCI_TB_MBOX0_SIZE_KB),
    .MCI_MBOX1_SIZE_KB(MCI_TB_MBOX1_SIZE_KB)
  )
  mci_top_inst
  (
  
    .clk('0),

    // MCI Resets
    .mci_rst_b('0),
    .mci_pwrgood('0),
    
    .scan_mode('0),

    // MCI AXI Interface
    .s_axi_w_if,
    .s_axi_r_if,
    
    // Straps
    .strap_mcu_lsu_axi_user('0),
    .strap_mcu_ifu_axi_user('0),

    // SRAM ADHOC connections
    .mcu_sram_fw_exec_region_lock('0),

    // SS error signals
    .agg_error_fatal('0),
    .agg_error_non_fatal('0),

    // SOC Interrupts
    .all_error_fatal(),
    .all_error_non_fatal(),
    
    // Generic in/out
    .mci_generic_input_wires('0),
    .mci_generic_output_wires(),
    
    // MCU interrupts
    .mcu_timer_int(),
    .mci_intr(),

    // MCU Reset vector
    .strap_mcu_reset_vector('0), // default reset vector
    .mcu_reset_vector(),       // reset vector used by MCU
    .mcu_no_rom_config('0),                // Determines boot sequencer boot flow

    // NMI Vector 
    .nmi_intr(),
    .mcu_nmi_vector(),
    
    // Reset controls
    .mcu_rst_b(),
    .cptra_rst_b(),

    // SoC signals
    .mci_boot_seq_brkpoint('0),

    // LCC Signals
    .lc_done('0),
    .lc_init(),


    // FC Signals
    .fc_opt_done('0),
    .fc_opt_init(),


    // MCU SRAM Interface
    .mci_mcu_sram_req_if,

    // Mbox0 SRAM Interface
    .mci_mbox0_sram_req_if,

    // Mbox1 SRAM Interface
    .mci_mbox1_sram_req_if 

  );

endmodule
