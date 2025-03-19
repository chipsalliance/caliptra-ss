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

 
  always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (cptra_rst_b) begin
      if (tb_service_cmd_valid) begin
        case (tb_service_cmd)
          CMD_FORCE_AWUSER_0: begin
            $display("fc_lcc_tb_services: Forcing fuse ctrl core_axi_wr_req.awuser = CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER");
            force `FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser = CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER;
          end
          CMD_FORCE_AWUSER_1: begin
            $display("fc_lcc_tb_services: Forcing fuse ctrl core_axi_wr_req.awuser = CPTRA_SS_STRAP_MCU_LSU_AXI_USER");
            force `FC_PATH.u_fuse_ctrl_filter.core_axi_wr_req.awuser = CPTRA_SS_STRAP_MCU_LSU_AXI_USER;
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
            force `LCC_PATH.otp_lc_data_i.test_exit_dev_token = 128'hee4f_e51a_73f2_9e7b_542f_2d2d_e65e_577c;
            force `LCC_PATH.otp_lc_data_i.dev_exit_prod_token = 128'h3656_71d1_31ba_fcef_ac7f_4d2a_776a_6ed3;
            force `LCC_PATH.otp_lc_data_i.prod_exit_prodend_token = 128'h5622_8106_a663_40c7_0f86_ccda_dcbc_2b7f;
            force `LCC_PATH.otp_lc_data_i.rma_token_valid = 4'b0101;//from_otp_caliptra_ss_lc_data_i.rma_token_valid;//caliptra_ss_lc_tx_t'(On);
            force `LCC_PATH.otp_lc_data_i.rma_token = 128'h9704_5d52_04f2_f7fc_8756_e714_5ad7_6df9;
          end
          default: begin
            // No action for unrecognized commands.
          end
        endcase
      end
    end
  end


  //-------------------------------------------------------------------------
  // Top-level service: Force FC, LCC reset for 10 cycles then release it.
  // Here we choose the command 8'h10 for FC, LCC reset.
  //-------------------------------------------------------------------------
  reg  [3:0] fc_lcc_reset_counter;
  reg        fc_lcc_reset_active;

  always_ff @(posedge clk or negedge cptra_rst_b) begin
      if (!cptra_rst_b) begin
          fc_lcc_reset_active  <= 1'b0;
          fc_lcc_reset_counter <= '0;
      end
      else begin
          // Detect the fc_lcc reset command from the mailbox
          if (tb_service_cmd_valid && tb_service_cmd == CMD_FC_LCC_RESET && !fc_lcc_reset_active) begin
              fc_lcc_reset_active  <= 1'b1;
              fc_lcc_reset_counter <= '0;
              $display("Top-level: Received fc_lcc reset command. Forcing reset for 10 cycles.");
          end
          else if (fc_lcc_reset_active) begin
              if (fc_lcc_reset_counter == 10) begin
                fc_lcc_reset_active    <= 1'b0;
                fc_lcc_reset_counter   <= '0;
              end
              else begin
                  fc_lcc_reset_active <= 1'b1;
                  fc_lcc_reset_counter <= fc_lcc_reset_counter + 1;
              end
          end
      end
  end

  always_comb begin
    if(fc_lcc_reset_active) begin
      force `LCC_PATH.rst_ni  = 1'b0;
      force `FC_PATH.rst_ni  = 1'b0;
    end else begin
      release `LCC_PATH.rst_ni;
      release `FC_PATH.rst_ni;
    end
  end


endmodule
