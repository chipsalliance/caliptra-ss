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

module mci_lcc_st_trans 
    import mci_pkg::*;
    import lc_ctrl_state_pkg::*;
    import soc_ifc_pkg::*;
 (
    input logic clk,
    input logic rst_n,
    // Inputs from top level of MCI
    input logic                                         state_error, // That represents any invalid state errors
    // Inputs from LCC
    input  otp_ctrl_pkg::lc_otp_program_req_t           from_lcc_to_otp_program_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_dft_en_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_hw_debug_en_i,
    // Inputs from OTP_Ctrl
    input  otp_ctrl_pkg::otp_lc_data_t                  from_otp_to_lcc_program_i,
    // Inputs from Caliptra_Core
    input logic                                         ss_dbg_manuf_enable_i,    
    input logic [63:0]                                  ss_soc_dbg_unlock_level_i,
    // Inputs from SoC
    input logic [63:0]                                  ss_soc_dft_en_mask_reg0_1,
    input logic [63:0]                                  ss_soc_dbg_unlock_mask_reg0_1, // Check FSM's TRANSLATOR_PROD_NON_DEBUG state
    input logic [63:0]                                  ss_soc_CLTAP_unlock_mask_reg0_1,

    // Converted Signals from LCC 
    output  logic                                       SOC_DFT_EN,
    output 	logic                                       SOC_HW_DEBUG_EN,

    output soc_ifc_pkg::security_state_t                security_state_o
);

soc_ifc_pkg::security_state_t                security_state_comb;
mci_state_translator_fsm_state_e             mci_trans_st_next;
mci_state_translator_fsm_state_e             mci_trans_st_current;
lc_state_e                                   lc_alive_state;
lc_state_e                                   otp_static_state;

logic                                        otp_data_valid;
logic                                        lc_otp_prog_req;
logic                                        lcc_valid_SCRAP_req;
logic                                        SOC_DFT_EN_AND;
logic                                        SOC_HW_DEBUG_EN_AND;
logic                                        CLPTR_PROD_DEBUG_UNLOCK_AND;


assign otp_data_valid               = from_otp_to_lcc_program_i.valid;
assign lc_otp_prog_req              = from_lcc_to_otp_program_i.req;
assign lc_alive_state               = from_lcc_to_otp_program_i.state;
assign SOC_DFT_EN_AND               = |(ss_soc_dbg_unlock_level_i & ss_soc_dft_en_mask_reg0_1);
assign SOC_HW_DEBUG_EN_AND          = |(ss_soc_dbg_unlock_level_i & ss_soc_CLTAP_unlock_mask_reg0_1);
assign CLPTR_PROD_DEBUG_UNLOCK_AND  = |(ss_soc_dbg_unlock_level_i & ss_soc_dbg_unlock_mask_reg0_1);
assign lcc_valid_SCRAP_req          = (lc_alive_state ==  LcStScrap && lc_otp_prog_req);

always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        mci_trans_st_current            <= TRANSLATOR_RESET;
        security_state_o                <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};  // Default case
        otp_static_state                <=  LcStRaw; // This is all zeros
        SOC_DFT_EN                      <= 1'b0;
        SOC_HW_DEBUG_EN                 <= 1'b0;
    end
    else begin
        if (otp_data_valid) begin
            mci_trans_st_current            <= mci_trans_st_next;
            security_state_o                <= security_state_comb;  // Default case
            otp_static_state                <= lc_state_e'(from_otp_to_lcc_program_i.state);
            SOC_DFT_EN                      <= (lc_dft_en_i == lc_ctrl_pkg::On) | SOC_DFT_EN_AND;
            SOC_HW_DEBUG_EN                 <= (lc_hw_debug_en_i == lc_ctrl_pkg::On)  | SOC_HW_DEBUG_EN_AND;
        end
        else begin
            mci_trans_st_current            <= TRANSLATOR_RESET;
            security_state_o                <= '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};  // Default case
            otp_static_state                <=  LcStRaw; // This is all zeros
            SOC_DFT_EN                      <= 1'b0;
            SOC_HW_DEBUG_EN                 <= 1'b0;
        end
    end
end



always_comb begin: state_branch
    
    case(mci_trans_st_current)
        TRANSLATOR_RESET: begin
            security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};  // Default case
            if (otp_data_valid) begin
                mci_trans_st_next = TRANSLATOR_IDLE;
            end
            else begin
                mci_trans_st_next = TRANSLATOR_RESET;
            end
        end
        TRANSLATOR_IDLE: begin
            security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};  // Default case
            // This module takes lcc state as a valid input only if LCC decides to enter SCRAP 
            // or Invalid state. This if condition also take SoC decision if it wants to put Caliptra
            // into non-debug mode due to a state error triggered through MCI fatal error logic
            if (lcc_valid_SCRAP_req || otp_static_state ==  LcStScrap || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
            end
            // RAW to TEST_LOCK0-6 are the non-debug modes. RAW is the default mode of LCC
            else if  (otp_static_state  inside {LcStRaw,
                                                LcStTestLocked0,
                                                LcStTestLocked1,
                                                LcStTestLocked2,
                                                LcStTestLocked3,
                                                LcStTestLocked4,
                                                LcStTestLocked5,
                                                LcStTestLocked6}) begin

                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
            end
            else if  (otp_static_state  inside {LcStTestUnlocked0,
                                                LcStTestUnlocked1,
                                                LcStTestUnlocked2,
                                                LcStTestUnlocked3,
                                                LcStTestUnlocked4,
                                                LcStTestUnlocked5,
                                                LcStTestUnlocked6,
                                                LcStTestUnlocked7}) begin

                mci_trans_st_next = TRANSLATOR_UNPROV_DEBUG;
            end
            else if  (otp_static_state == LcStDev) begin

                mci_trans_st_next = TRANSLATOR_MANUF_NON_DEBUG;
            end
            else if  (otp_static_state == LcStProd) begin

                mci_trans_st_next = TRANSLATOR_PROD_NON_DEBUG;
            end
            else if  (otp_static_state == LcStProdEnd) begin

                mci_trans_st_next = TRANSLATOR_PROD_NON_DEBUG;
            end
            else if  (otp_static_state == LcStRma) begin

                mci_trans_st_next = TRANSLATOR_PROD_DEBUG;
            end
            else begin

                mci_trans_st_next = TRANSLATOR_IDLE;
            end
        end
        TRANSLATOR_NON_DEBUG: begin
            mci_trans_st_next = TRANSLATOR_NON_DEBUG;
            security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
        end
        TRANSLATOR_UNPROV_DEBUG: begin
            if (lcc_valid_SCRAP_req || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else begin
                mci_trans_st_next = TRANSLATOR_UNPROV_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_UNPROVISIONED, debug_locked: 1'b0}; 
            end
        end
        TRANSLATOR_MANUF_NON_DEBUG: begin
            if (lcc_valid_SCRAP_req || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else if (ss_dbg_manuf_enable_i) begin
                mci_trans_st_next = TRANSLATOR_MANUF_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: 1'b1}; 
            end
            else begin
                mci_trans_st_next = TRANSLATOR_MANUF_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: 1'b1}; 
            end
        end
        TRANSLATOR_MANUF_DEBUG: begin
            if (lcc_valid_SCRAP_req || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else begin
                mci_trans_st_next = TRANSLATOR_MANUF_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: 1'b0}; 
            end
        end
        TRANSLATOR_PROD_NON_DEBUG: begin
            if (lcc_valid_SCRAP_req || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else if (CLPTR_PROD_DEBUG_UNLOCK_AND) begin // TODO: Be careful for fault injections
                mci_trans_st_next = TRANSLATOR_PROD_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else begin
                mci_trans_st_next = TRANSLATOR_PROD_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
        end
        TRANSLATOR_PROD_DEBUG: begin
            if (lcc_valid_SCRAP_req || state_error) begin
                mci_trans_st_next = TRANSLATOR_NON_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1}; 
            end
            else begin
                mci_trans_st_next = TRANSLATOR_MANUF_DEBUG;
                security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b0}; 
            end
        end
        default: begin
            security_state_comb = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};  // Default case
            mci_trans_st_next = TRANSLATOR_IDLE;
        end
    endcase

end

endmodule


