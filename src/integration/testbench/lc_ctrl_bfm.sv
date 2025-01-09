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
    import lc_ctrl_pkg::*;
    import lc_ctrl_reg_pkg::*;
    import lc_ctrl_state_pkg::*;
(
    input  logic clk,
    input  logic reset_n,

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
    output caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0] lc_ctrl_alert_rx,
    input  caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0] lc_ctrl_alert_tx,

    // Escape State Interface
    output  caliptra_prim_esc_pkg::esc_rx_t esc_scrap_state0_tx_i,
    input caliptra_prim_esc_pkg::esc_tx_t esc_scrap_state0_rx_o,
    output  caliptra_prim_esc_pkg::esc_rx_t esc_scrap_state1_tx_i,
    input caliptra_prim_esc_pkg::esc_tx_t esc_scrap_state1_rx_o,

    // Clock manager interface
    input  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req_o,
    output lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_i
);

    // Internal signals
    logic [35:0] clk_counter;
    logic pwr_lc_i_active;
    pwrmgr_pkg::pwr_lc_req_t pwr_lc_i_internal;

    logic lc_clk_byp_ack_internal;
    assign lc_clk_byp_ack_i = lc_clk_byp_ack_internal;
    assign lc_ctrl_scan_rst_ni = 1;
    assign pwr_lc_i = pwr_lc_i_internal;

    // Default values
    assign lc_ctrl_dmi_tl_h2d = tlul_pkg::TL_H2D_DEFAULT;
    assign lc_ctrl_scanmode_i = caliptra_prim_mubi_pkg::MuBi4False;
    assign lc_ctrl_alert_rx = '{default: caliptra_prim_alert_pkg::ALERT_RX_DEFAULT};
    assign esc_scrap_state0_tx_i.resp_p = 1'b0;
    assign esc_scrap_state0_tx_i.resp_n = 1'b1;
    assign esc_scrap_state1_tx_i.resp_p = 1'b0;
    assign esc_scrap_state1_tx_i.resp_n = 1'b1;

    // Power Management Logic
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            clk_counter <= 0;
            pwr_lc_i_internal = '{default: '0};
        end else if (cptra_pwrgood) begin
            if (clk_counter < 500) begin
                clk_counter <= clk_counter + 1;
                pwr_lc_i_internal.lc_init = 1'b0;
            end else begin
                clk_counter <= clk_counter;
                pwr_lc_i_internal.lc_init = 1'b1;
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

