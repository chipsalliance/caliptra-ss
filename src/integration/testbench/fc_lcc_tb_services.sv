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

  logic [1:0] freq_sel;
  assign freq_sel = '0;
 
  always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (cptra_rst_b) begin
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
            force freq_sel = 2'b00;
          end
          CMD_FC_LCC_EXT_CLK_160MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 160 mhz");
            force freq_sel = 2'b01;
          end
          CMD_FC_LCC_EXT_CLK_400MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 400 mhz");
            force freq_sel = 2'b10;
          end
          CMD_FC_LCC_EXT_CLK_1000MHZ: begin
            $display("fc_lcc_tb_services: setting ext clock frequency to 1000 mhz");
            force freq_sel = 2'b11;
          end
          CMD_FC_LCC_FAULT_DIGEST: begin
            $display("fc_lcc_tb_services: fault the transition tokens partition digest");
            force `CPTRA_SS_TB_TOP_NAME.u_otp.u_prim_ram_1p_adv.u_mem.mem[696] = '0;
          end
          default: begin
            // No action for unrecognized commands.
          end
        endcase
      end
    end
  end

  bit clk_160;
  bit clk_400;
  bit clk_500;
  bit clk_1000;

  initial begin
    clk_500 = 0;
    forever clk_500 = #(1.00) ~clk_500;
  end

  initial begin
    clk_400 = 0;
    forever clk_400 = #(1.25) ~clk_400;
  end

  initial begin
    clk_160 = 0;
    forever clk_160 = #(3.125) ~clk_160;
  end

  initial begin
    clk_1000 = 0;
    forever clk_1000 = #(0.5) ~clk_1000;
  end

  bit clk_sel;
  assign clk_sel = freq_sel == 2'b00 ? clk_500 :
                   freq_sel == 2'b01 ? clk_160 :
                   freq_sel == 2'b10 ? clk_400 : 
                   freq_sel == 2'b11 ? clk_1000 : clk_500;

  always_comb begin
    if (`LCC_PATH.lc_clk_byp_ack_i == lc_ctrl_pkg::On) begin
      force `CPTRA_SS_TB_TOP_NAME.core_clk = clk_sel;
    end else begin
      force `CPTRA_SS_TB_TOP_NAME.core_clk = clk_500;
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
