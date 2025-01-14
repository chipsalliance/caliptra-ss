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


module lc_ctrl_bfm 
    import otp_ctrl_pkg::*;
    import lc_ctrl_pkg::*;
    import lc_ctrl_reg_pkg::*;
    import lc_ctrl_state_pkg::*;
(
    input  logic clk,
    input  logic reset_n,

    
    input axi_struct_pkg::axi_rd_req_t lc_axi_rd_req,
    input axi_struct_pkg::axi_rd_rsp_t lc_axi_rd_rsp,
    output logic fake_reset,
    output logic Allow_RMA_on_PPD,
    output logic [7:0] from_bfm_lc_flash_rma_ack,
    input  [3:0]        to_bfm_lc_flash_rma_req_o,

    // Power manager interface
    output pwrmgr_pkg::pwr_lc_req_t pwr_lc_i,
    input  pwrmgr_pkg::pwr_lc_rsp_t pwr_lc_o,
    input  logic                                cptra_pwrgood,

    // TL-UL Interface
    output tlul_pkg::tl_h2d_t lc_ctrl_dmi_tl_h2d,
    input  tlul_pkg::tl_d2h_t lc_ctrl_dmi_tl_d2h,

    // Scan Interface
    output lc_ctrl_scan_rst_ni,
    output caliptra_prim_mubi_pkg::mubi4_t lc_ctrl_scanmode_i,

    // Alert Handler Interface
    input [lc_ctrl_reg_pkg::NumAlerts-1:0] lc_alerts_o,

    // Escalation State Interface
    output  esc_scrap_state0,
    output  esc_scrap_state1,


    // OTP Hack
    output otp_ctrl_pkg::otp_lc_data_t   otp_lc_data_o,
    input otp_ctrl_pkg::otp_lc_data_t   from_otp_lc_data_i,
    // Clock manager interface
    input  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req_o,
    output lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_i
);

    // Internal signals
    logic [35:0] clk_counter;
    // Declare the shift register for buffering
    logic power_and_reset_indication;
    logic [19:0] power_and_reset_buffer;
    // Buffered signal
    logic power_and_reset_indication_buffered;


    logic pwr_lc_i_active;
    pwrmgr_pkg::pwr_lc_req_t pwr_lc_i_internal;

    lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_internal;
    assign lc_clk_byp_ack_i = lc_clk_byp_ack_internal;
    assign lc_ctrl_scan_rst_ni = 1;
    assign pwr_lc_i = pwr_lc_i_internal;

    // Default values
    assign lc_ctrl_dmi_tl_h2d = tlul_pkg::TL_H2D_DEFAULT;
    assign lc_ctrl_scanmode_i = caliptra_prim_mubi_pkg::MuBi4False;
    

    //OTP assignments
    assign otp_lc_data_o.valid = from_otp_lc_data_i.valid;
    assign otp_lc_data_o.error = from_otp_lc_data_i.error;
    assign otp_lc_data_o.state = from_otp_lc_data_i.state;
    assign otp_lc_data_o.count = from_otp_lc_data_i.count;
    assign otp_lc_data_o.secrets_valid = from_otp_lc_data_i.secrets_valid;//lc_tx_t'(On);
    assign otp_lc_data_o.test_tokens_valid = lc_tx_t'(On); //from_otp_lc_data_i.test_tokens_valid;//lc_tx_t'(On);
    assign otp_lc_data_o.test_unlock_token = 128'h3852_305b_aecf_5ff1_d5c1_d25f_6db9_058d;
    assign otp_lc_data_o.test_exit_token = 128'h3852_305b_aecf_5ff1_d5c1_d25f_6db9_058d;
    assign otp_lc_data_o.rma_token_valid = lc_tx_t'(On);//from_otp_lc_data_i.rma_token_valid;//lc_tx_t'(On);
    assign otp_lc_data_o.rma_token = 128'h3852_305b_aecf_5ff1_d5c1_d25f_6db9_058d;

    assign from_bfm_lc_flash_rma_ack = (to_bfm_lc_flash_rma_req_o==3'h5) ? 8'h55 : 8'hAA;

    assign esc_scrap_state0 = (|lc_alerts_o)? 1'b1: 1'b0;
    assign esc_scrap_state1 = (|lc_alerts_o)? 1'b1: 1'b0;


    // TODO: This is used for keeping RMA strap to a desired value
    //-------------------------------------------------------------------
    always@(posedge clk or negedge reset_n) begin
        if (!reset_n)
            Allow_RMA_on_PPD <= 0;
        else if (lc_axi_rd_req.arvalid && lc_axi_rd_rsp.arready && lc_axi_rd_req.araddr == 32'h7000_0448 && !power_and_reset_indication)
            Allow_RMA_on_PPD <= ~Allow_RMA_on_PPD;
    end
    //-------------------------------------------------------------------

    
    // TODO: This is used for reset and power init, a temporal solution
    //-------------------------------------------------------------------
    always@(posedge clk or negedge reset_n) begin
        if (!reset_n)
            power_and_reset_indication <= 0;
        else if (lc_axi_rd_req.arvalid && lc_axi_rd_rsp.arready && lc_axi_rd_req.araddr == 32'h7000_0444 && !power_and_reset_indication)
            power_and_reset_indication <= 1;
        else
            power_and_reset_indication <= 0;
    end
    //-------------------------------------------------------------------

    // Power Management Logic
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            clk_counter <= 0;
            pwr_lc_i_internal = '{default: '0};
            fake_reset  <= 1'b1;
            power_and_reset_buffer <= 20'b0; // Reset the buffer
            power_and_reset_indication_buffered <= 1'b0;
        end else if (cptra_pwrgood) begin
            // Update the shift register
            power_and_reset_buffer <= {power_and_reset_buffer[18:0], power_and_reset_indication};
            power_and_reset_indication_buffered <= power_and_reset_buffer[19]; // Use the buffered value
            if (clk_counter < 500) begin
                clk_counter <= clk_counter + 1;
                pwr_lc_i_internal.lc_init = 1'b0;
                fake_reset  <= fake_reset;
            end
            else if (power_and_reset_indication_buffered) begin
                clk_counter <= 0;
                pwr_lc_i_internal.lc_init = 1'b0;
                fake_reset  <= 1'b0;
            end            
            else begin
                clk_counter <= clk_counter;
                pwr_lc_i_internal.lc_init = 1'b1;
                fake_reset  <= 1'b1;
            end
        end
    end

    // Clock Manager Interface
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            lc_clk_byp_ack_internal <= lc_tx_t'(Off);
        end else begin
            if (lc_clk_byp_req_o == lc_tx_t'(On) && !lc_clk_byp_ack_internal) begin
                lc_clk_byp_ack_internal <= lc_tx_t'(On);
            end else begin
                lc_clk_byp_ack_internal <= lc_tx_t'(Off);
            end
        end
    end

endmodule