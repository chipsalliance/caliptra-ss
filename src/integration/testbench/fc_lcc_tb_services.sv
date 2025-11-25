// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

`default_nettype none

module fc_lcc_tb_services (
  input  logic        clk,
  input  logic        cptra_rst_b,
  input  logic        tb_service_cmd_valid,
  input  logic [7:0]  tb_service_cmd
);

  // Include the command list definitions (e.g., CMD_FORCE_AWUSER_0, CMD_FORCE_AWUSER_1, etc.)
  `include "caliptra_ss_tb_cmd_list.svh"
  `include "caliptra_ss_includes.svh"
  `include "soc_address_map_defines.svh"

  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;

  logic disable_lcc_sva;
  logic disable_fc_all_ones_sva;

  logic ecc_fault_en = 1'b0;
  logic lcc_bus_error_en = 1'b0;
  logic lcc_external_clk_req;
 
  always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
      `CPTRA_SS_TB_TOP_NAME.lcc_clock_selection   <= 1000;
      lcc_external_clk_req                        <= 1'b0;  
    end
    else begin
      if (`CPTRA_SS_TB_TOP_NAME.lcc_clock_switch_req) begin
        lcc_external_clk_req <= 0;
      end 
      if (tb_service_cmd_valid) begin
        case (tb_service_cmd)
          CMD_FORCE_FC_AWUSER_CPTR_CORE: begin
            $display("fc_lcc_tb_services: Forcing fuse ctrl core_axi_wr_req.awuser = CLPTRA_CORE_AXI_USER");
            force `FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser = `CPTRA_SS_TOP_PATH.cptra_ss_strap_caliptra_dma_axi_user_i;
          end
          CMD_FORCE_FC_AWUSER_MCU: begin
            $display("fc_lcc_tb_services: Forcing fuse ctrl core_axi_wr_req.awuser = MCU_LSU_AXI_USER");
            force `FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser = `CPTRA_SS_TOP_PATH.cptra_ss_strap_mcu_lsu_axi_user_i;
          end
          CMD_RELEASE_AWUSER: begin
            $display("fc_lcc_tb_services: Releasing fuse ctrl's force on core_axi_wr_req.awuser");
            release `FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser;
          end
          CMD_FC_FORCE_ZEROIZATION: begin
            $display("fc_lcc_tb_services: Forcing FIPS_ZEROIZATION_PPD_i = 1, ROM mask = 32'hFFFFFFFF, and lcc_is_in_SCRAP_mode = 0");
            force `CPTRA_SS_TOP_PATH.cptra_ss_FIPS_ZEROIZATION_PPD_i = 1'b1;
            force `MCI_PATH.LCC_state_translator.ss_soc_MCU_ROM_zeroization_mask_reg = 32'hFFFFFFFF;
            force `FC_PATH.lcc_is_in_SCRAP_mode = 1'b0;
            force `FC_PATH.FIPS_ZEROIZATION_CMD_i = 1'b1;
          end
          CMD_FC_FORCE_ZEROIZATION_RESET: begin
            $display("fc_lcc_tb_services: Forcing FIPS_ZEROIZATION_PPD_i = 0, ROM mask = 32'h0, and lcc_is_in_SCRAP_mode = 1");
            force `CPTRA_SS_TOP_PATH.cptra_ss_FIPS_ZEROIZATION_PPD_i = 1'b0;
            force `MCI_PATH.LCC_state_translator.ss_soc_MCU_ROM_zeroization_mask_reg = 32'h0;
            force `FC_PATH.lcc_is_in_SCRAP_mode = 1'b1;
          end
          CMD_RELEASE_ZEROIZATION: begin
            $display("fc_lcc_tb_services: Releasing forces on zeroization signals");
            release `CPTRA_SS_TOP_PATH.cptra_ss_FIPS_ZEROIZATION_PPD_i;
            release `MCI_PATH.LCC_state_translator.ss_soc_MCU_ROM_zeroization_mask_reg;
            release `FC_PATH.lcc_is_in_SCRAP_mode;
          end
          CMD_FORCE_LC_TOKENS: begin
            $display("fc_lcc_tb_services: Forcing LCC TOKENS");            
            force `LCC_PATH.otp_lc_data_i.test_tokens_valid = 4'b0101; //from_otp_caliptra_ss_lc_data_i.test_tokens_valid;//caliptra_ss_lc_tx_t'(On);
            force `LCC_PATH.otp_lc_data_i.test_unlock_token = 128'h3852_305b_aecf_5ff1_d5c1_d25f_6db9_058d;
            force `LCC_PATH.otp_lc_data_i.test_exit_dev_token = 128'hd10ceca9_725373ec_32ac874c_7381bd54;
            force `LCC_PATH.otp_lc_data_i.dev_exit_prod_token = 128'hf1c0bd8a_da705018_5d3667f5_aeebc767;
            force `LCC_PATH.otp_lc_data_i.prod_exit_prodend_token = 128'hdb17c6f2_fa63d690_734a8a31_6147d7e5;
            force `LCC_PATH.otp_lc_data_i.rma_token_valid = 4'b0101;//from_otp_caliptra_ss_lc_data_i.rma_token_valid;//caliptra_ss_lc_tx_t'(On);
            force `LCC_PATH.otp_lc_data_i.rma_token = 128'h67926115_6880f4cc_51785553_16c51e4d;
          end
          CMD_LC_FORCE_RMA_SCRAP_PPD: begin
            $display("fc_lcc_tb_services: Forcing Allow_RMA_or_SCRAP_on_PPD  = 1");
            force `CPTRA_SS_TOP_PATH.cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i = 1'b1;
          end
          CMD_FC_TRIGGER_ESCALATION: begin
            $display("fc_lcc_tb_services: triggering an escalation");
            force `FC_PATH.lc_escalate_en_i = lc_ctrl_pkg::On;     
          end
          CMD_FC_LCC_EXT_CLK_500MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 500 mhz");       
            `CPTRA_SS_TB_TOP_NAME.lcc_clock_selection   <= 500;
            lcc_external_clk_req                        <= 1;
          end
          CMD_FC_LCC_EXT_CLK_160MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 160 mhz");     
            `CPTRA_SS_TB_TOP_NAME.lcc_clock_selection   <= 160; 
            lcc_external_clk_req                        <= 1;
          end
          CMD_FC_LCC_EXT_CLK_400MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 400 mhz");       
            `CPTRA_SS_TB_TOP_NAME.lcc_clock_selection   <= 400; 
            lcc_external_clk_req                        <= 1;
          end
          CMD_FC_LCC_EXT_CLK_1000MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 1000 mhz");      
            `CPTRA_SS_TB_TOP_NAME.lcc_clock_selection   <= 1000; 
            lcc_external_clk_req                        <= 1;
          end
          CMD_FC_LCC_FAULT_DIGEST: begin
            $display("fc_lcc_tb_services: fault the transition tokens partition digest");
            force `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[SecretLcTransitionPartitionDigestOffset/2] = '0;
          end
          CMD_FC_LCC_FAULT_BUS_ECC: begin
            $display("fc_lcc_tb_services: fault one bit in axi write request");
            force ecc_fault_en = 1'b1;
            // XXX: The AXI controller blocks when observing a write response error.
            // This manually pulls the signal down to allow for program continuation.
            force `FC_PATH.core_axi_wr_rsp.bresp = '0;
          end
          CMD_LC_TRIGGER_ESCALATION0: begin
            $display("fc_lcc_tb_services: triggering esc_scrap_state0 escalation");
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_lc_esclate_scrap_state0_i = 1'b1;
          end
          CMD_LC_TRIGGER_ESCALATION1: begin
            $display("fc_lcc_tb_services: triggering esc_scrap_state1 escalation");
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_lc_esclate_scrap_state1_i = 1'b1;
          end
          CMD_LCC_FATAL_BUS_INTEG_ERROR: begin
            $display("fc_lcc_tb_services: triggering a bus integrity fault");
            force lcc_bus_error_en = 1'b1;
            // XXX: The AXI controller blocks when observing a write response error.
            // This manually pulls the signal down to allow for program continuation.
            force `LCC_PATH.axi_wr_rsp.bresp = '0;
          end
          CMD_LC_FAULT_CNTR: begin
            $display("fc_lcc_tb_services: fault lcc cntr fuse");
            force `LCC_PATH.u_lc_ctrl_fsm.u_lc_ctrl_state_transition.lc_cnt_i[0] = '0;
          end
          CMD_DISABLE_CLK_BYP_ACK: begin
            $display("fc_lcc_tb_services: disable clk_byp_ack");
            force `CPTRA_SS_TB_TOP_NAME.cptra_ss_lc_clk_byp_ack_i = '0;
          end
          CMD_LC_TRIGGER_ESCALATION0_DIS: begin
            $display("fc_lcc_tb_services: releasing esc_scrap_state0 escalation");
            release `CPTRA_SS_TB_TOP_NAME.cptra_ss_lc_esclate_scrap_state0_i;
          end
          CMD_LC_TRIGGER_ESCALATION1_DIS: begin
            $display("fc_lcc_tb_services: releasing esc_scrap_state1 escalation");
            release `CPTRA_SS_TB_TOP_NAME.cptra_ss_lc_esclate_scrap_state1_i;
          end
          CMD_FC_FORCE_FUSE_FAULT: begin
            $display("fc_lcc_tb_services: Fault 2 LSBs of the HEK_PROD_1 zeroization marker");
            force `FC_MEM[CptraSsLockHekProd1ZerOffset/2][1:0] = '0;
          end
          CMD_FC_RELEASE_FUSE_FAULT: begin
            $display("fc_lcc_tb_services: Release fault on the HEK_PROD_1 zeroization marker");
            release `FC_MEM[CptraSsLockHekProd1ZerOffset/2][1:0];
          end
          CMD_FC_FORCE_FUSE_UNZEROIZ: begin
            $display("fc_lcc_tb_services: Fault %0d LSBs of the VENDOR_SECRET_PROD_PARTITION zeroization marker to be below the threshold", otp_ctrl_pkg::ScrmblBlockWidth-otp_ctrl_pkg::ZeroizationValidBound+1);
            force `FC_MEM[VendorSecretProdPartitionZerOffset/2][otp_ctrl_pkg::ScrmblBlockWidth-otp_ctrl_pkg::ZeroizationValidBound:0] = '0;
          end
          CMD_FC_RELEASE_FUSE_UNZEROIZ: begin
            $display("fc_lcc_tb_services: Release fault on the VENDOR_SECRET_PROD_PARTITION zeroization marker");
            release `FC_MEM[VendorSecretProdPartitionZerOffset/2][otp_ctrl_pkg::ScrmblBlockWidth-otp_ctrl_pkg::ZeroizationValidBound+1:0];
          end
          default: begin
            // No action for unrecognized commands.
          end
        endcase
      end
    end
  end

  // Toggle a bit when observing a fuse_ctrl DAI write.
  always_comb begin
    if (ecc_fault_en == 1'b1 && `FC_PATH.u_core_axi2tlul.i_sub2tlul.write == 1'b1 && `FC_PATH.u_core_axi2tlul.i_sub2tlul.addr == `SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0) begin
      force `FC_PATH.u_core_axi2tlul.i_sub2tlul.tl_o.a_data[0] = `FC_PATH.u_core_axi2tlul.i_sub2tlul.wdata ^ 1;
    end else begin
      release `FC_PATH.u_core_axi2tlul.i_sub2tlul.tl_o.a_data;
    end
  end

  always_comb begin
  if (lcc_bus_error_en == 1'b1 && `LCC_PATH.u_lc_axi2tlul.i_sub2tlul.write == 1'b1 && `LCC_PATH.u_lc_axi2tlul.i_sub2tlul.addr == `SOC_LC_CTRL_ALERT_TEST) begin
      force `LCC_PATH.u_lc_axi2tlul.i_sub2tlul.tl_o.a_data[0] = `LCC_PATH.u_lc_axi2tlul.i_sub2tlul.wdata ^ 1;
    end else begin
      release `LCC_PATH.u_lc_axi2tlul.i_sub2tlul.tl_o.a_data;
    end
  end

  assign `CPTRA_SS_TB_TOP_NAME.lcc_clock_switch_req = (`LCC_PATH.lc_clk_byp_ack_i == lc_ctrl_pkg::On) & lcc_external_clk_req;


  //-------------------------------------------------------------------------
  // Top-level service: Force FC, LCC reset for 10 cycles then release it.
  // Here we choose the command 8'h10 for FC, LCC reset.
  //-------------------------------------------------------------------------
  reg  [3:0] fc_lcc_reset_counter;
  reg        fc_lcc_reset_active;
  reg        fc_lcc_reset_0ing_active;

  always_ff @(posedge clk or negedge cptra_rst_b) begin
      if (!cptra_rst_b) begin
          fc_lcc_reset_0ing_active <= 1'b0;
          fc_lcc_reset_active      <= 1'b0;
          fc_lcc_reset_counter     <= '0;
          disable_lcc_sva          <= 1'b0;
          disable_fc_all_ones_sva  <= 1'b0;
      end
      else begin
          // Detect CMD_FC_LCC_EN_RESET_WHILE_0ING command.
          if (tb_service_cmd_valid && tb_service_cmd == CMD_FC_LCC_EN_RESET_WHILE_0ING) begin
              fc_lcc_reset_0ing_active <= 1'b1;
          end

          // Detect CMD_FC_LCC_DIS_RESET_WHILE_0ING command.
          if (tb_service_cmd_valid && tb_service_cmd == CMD_FC_LCC_DIS_RESET_WHILE_0ING) begin
              fc_lcc_reset_0ing_active <= 1'b0;
          end

          // Reset FC_LCC if it isn't currently active and one of the following happens:
          // - the CMD_FC_LCC_RESET is detected;
          // - reset-while-zeroizing is active and zeroization is detected.
          if (!fc_lcc_reset_active && (
                  (tb_service_cmd_valid && tb_service_cmd == CMD_FC_LCC_RESET) ||
                  (fc_lcc_reset_0ing_active &&
                      `FC_OTP_PRIM.state_q == 10'b0100110111 /* ZerWriteSt */ &&
                      `FC_OTP_PRIM.cnt_q != '0)
          )) begin
              fc_lcc_reset_active  <= 1'b1;
              fc_lcc_reset_counter <= '0;
              $display("Top-level: Forcing FC_LCC reset for 10 cycles.");
          end
          if (fc_lcc_reset_active) begin
              if (fc_lcc_reset_counter == 10) begin
                fc_lcc_reset_active    <= 1'b0;
                fc_lcc_reset_counter   <= '0;
              end else begin
                  fc_lcc_reset_active <= 1'b1;
                  fc_lcc_reset_counter <= fc_lcc_reset_counter + 1;
              end
          end

          if (tb_service_cmd_valid && tb_service_cmd == CMD_LC_DISABLE_SVA && !disable_lcc_sva) begin
            disable_lcc_sva  <= 1'b1;
            $display("Top-level: Received disable LCC's Assertions.");
          end
          
          if (tb_service_cmd_valid && tb_service_cmd == CMD_LC_ENABLE_SVA && disable_lcc_sva) begin
            disable_lcc_sva  <= 1'b0;
            $display("Top-level: Received enable LCC's Assertions.");
          end

          if (tb_service_cmd_valid && tb_service_cmd == CMD_FC_ALL_ONES_DISABLE_SVA && !disable_fc_all_ones_sva) begin
            disable_fc_all_ones_sva  <= 1'b1;
            $display("Top-level: Received disable FC_all_ones assertion.");
          end
          
          if (tb_service_cmd_valid && tb_service_cmd == CMD_FC_ALL_ONES_ENABLE_SVA && disable_fc_all_ones_sva) begin
            disable_fc_all_ones_sva  <= 1'b0;
            $display("Top-level: Received enable FC_all_ones assertion.");
          end
      end
  end

  always_comb begin
    if(fc_lcc_reset_active) begin
      force `LCC_PATH.rst_ni  = 1'b0;
      force `FC_PATH.rst_ni  = 1'b0;
      force `MCI_PATH.LCC_state_translator.rst_ni  = 1'b0;
    end else begin
      release `LCC_PATH.rst_ni;
      release `FC_PATH.rst_ni;
      release `MCI_PATH.LCC_state_translator.rst_ni;
    end
  end

  //-------------------------------------------------------------------------
  // OTP memory fault injection
  //
  // This is designed to allow the caliptra_ss_fuse_ctrl_init_fail test to cause an ECC error in
  // some chosen partition.
  //
  //   - Correctable error: One bit flip in a locked partition
  //   - Uncorrectable error: Flip all bits of a word in a locked partition
  //
  //-------------------------------------------------------------------------

  // The offsets in the address map for the first word of some partitions, together with the offset
  // to that partition's digest.
  //
  // Note that these offsets are measured in bytes, so need to be halved when indexing into `FC_MEM.
  // Also note that the arrays are packed (a tool requirement), but are listed in increasing order,
  // so that indexing looks more like the C code with which we're interacting.
  localparam [31:0] PartitionOffsetsAndDigests[0:7][0:1] = '{
    '{ SwTestUnlockPartitionOffset,       SwTestUnlockPartitionDigestOffset },
    '{ SecretManufPartitionOffset,        SecretManufPartitionDigestOffset },
    '{ SecretProdPartition0Offset,        SecretProdPartition0DigestOffset },
    '{ SecretProdPartition1Offset,        SecretProdPartition1DigestOffset },
    '{ SecretProdPartition2Offset,        SecretProdPartition2DigestOffset },
    '{ SecretProdPartition3Offset,        SecretProdPartition3DigestOffset },
    '{ SecretLcTransitionPartitionOffset, SecretLcTransitionPartitionDigestOffset },
    '{ VendorSecretProdPartitionOffset,   VendorSecretProdPartitionDigestOffset }
  };

  localparam int unsigned NumFaultablePartitions = $size(PartitionOffsetsAndDigests);

  reg fault_active_q;
  reg [15:0] before_fault_q[NumFaultablePartitions], fault_mask_q [NumFaultablePartitions];

  logic new_fault_req;
  assign new_fault_req = (tb_service_cmd_valid && !fault_active_q &&
                          tb_service_cmd inside {CMD_FC_LCC_CORRECTABLE_FAULT,
                                                 CMD_FC_LCC_UNCORRECTABLE_FAULT});

  always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (!cptra_rst_b) begin
      fault_active_q <= 1'b0;
    end else begin
      if (new_fault_req) begin
        fault_active_q <= 1'b1;
      end
    end
  end

  for (genvar i = 0; i < NumFaultablePartitions; i++) begin : partition_faults
    always_ff @(posedge clk or negedge cptra_rst_b) begin
      if (!cptra_rst_b) begin
        before_fault_q[i] <= '0;
        fault_mask_q[i] <= '0;
      end else begin
        // If some sort of fault is being requested, take a snapshot of the bottom 16 bits of the
        // uncorrupted word for this partition.
        if (new_fault_req) begin
          before_fault_q[i] <= `FC_MEM[PartitionOffsetsAndDigests[i][0] / 2][15:0];

          // Now check to see which sort of fault was being requested. If correctable, then the
          // fault mask to inject is just a single bit.
          if (tb_service_cmd == CMD_FC_LCC_CORRECTABLE_FAULT) fault_mask_q[i] = 1;
          // If uncorrectable, the fault mask should be all the bits of the word.
          else if (tb_service_cmd == CMD_FC_LCC_UNCORRECTABLE_FAULT) fault_mask_q[i] = ~0;
        end
      end
    end

    always_comb begin
      if (fault_active_q) begin
        force `FC_MEM[PartitionOffsetsAndDigests[i][0] / 2][15:0] = (before_fault_q[i] ^
                                                                     fault_mask_q[i]);
      end else begin
        release `FC_MEM[PartitionOffsetsAndDigests[i][0] / 2][15:0];
      end
    end
  end

endmodule
