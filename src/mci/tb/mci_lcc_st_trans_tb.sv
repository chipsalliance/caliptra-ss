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
`timescale 1ps/1ps


module mci_lcc_st_trans_tb 
    import mci_pkg::*;
    import lc_ctrl_state_pkg::*;
    import soc_ifc_pkg::*;
 ();
// Testbench signals
 logic clk;
 logic rst_n;
 logic state_error;

 otp_ctrl_pkg::lc_otp_program_req_t from_lcc_to_otp_program_i;
 lc_ctrl_pkg::lc_tx_t lc_dft_en_i;
 lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i;
 otp_ctrl_pkg::otp_lc_data_t from_otp_to_lcc_program_i;
 logic ss_dbg_manuf_enable_i;
 logic [63:0] ss_soc_dbg_unlock_level_i;
 logic [63:0] ss_soc_dft_en_mask_reg0_1;
 logic [63:0] ss_soc_dbg_unlock_mask_reg0_1;
 logic [63:0] ss_soc_CLTAP_unlock_mask_reg0_1;

 logic SOC_DFT_EN;
 logic SOC_HW_DEBUG_EN;
 soc_ifc_pkg::security_state_t security_state_o;

 // DUT instantiation
 mci_lcc_st_trans dut (
     .clk(clk),
     .rst_n(rst_n),
     .state_error(state_error),
     .from_lcc_to_otp_program_i(from_lcc_to_otp_program_i),
     .lc_dft_en_i(lc_dft_en_i),
     .lc_hw_debug_en_i(lc_hw_debug_en_i),
     .from_otp_to_lcc_program_i(from_otp_to_lcc_program_i),
     .ss_dbg_manuf_enable_i(ss_dbg_manuf_enable_i),
     .ss_soc_dbg_unlock_level_i(ss_soc_dbg_unlock_level_i),
     .ss_soc_dft_en_mask_reg0_1(ss_soc_dft_en_mask_reg0_1),
     .ss_soc_dbg_unlock_mask_reg0_1(ss_soc_dbg_unlock_mask_reg0_1),
     .ss_soc_CLTAP_unlock_mask_reg0_1(ss_soc_CLTAP_unlock_mask_reg0_1),
     .SOC_DFT_EN(SOC_DFT_EN),
     .SOC_HW_DEBUG_EN(SOC_HW_DEBUG_EN),
     .security_state_o(security_state_o)
 );

//  Clock generation
 always
 begin : clk_gen
   #5;
   clk = !clk;
 end // clk_gen

 // Reset logic
 initial begin
     rst_n = 0;
     repeat(10) @(negedge clk);
     rst_n = 1;
 end

 // Test stimulus
 initial begin
     // Initialize inputs
     clk = 0;
     state_error = 0;
     from_lcc_to_otp_program_i = '{req: 0, state: LcStRaw, count: LcCnt0};
     lc_dft_en_i = lc_ctrl_pkg::Off;
     lc_hw_debug_en_i = lc_ctrl_pkg::Off;
     from_otp_to_lcc_program_i = '0;
     from_otp_to_lcc_program_i.valid = 0;
     from_otp_to_lcc_program_i.state = LcStRaw;
     ss_dbg_manuf_enable_i = 0;
     ss_soc_dbg_unlock_level_i = 64'h0;
     ss_soc_dft_en_mask_reg0_1 = 64'h0;
     ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
     ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h0;

     #100;
 end

 task apply_reset();
    rst_n = 0;
    from_otp_to_lcc_program_i.valid = 0;
    from_otp_to_lcc_program_i.valid = 0;
    repeat(10) @(negedge clk);
    rst_n = 1;
    repeat(5) @(negedge clk);
    from_otp_to_lcc_program_i.valid = 1;
    repeat(5) @(negedge clk);
    from_otp_to_lcc_program_i.valid = 1;
endtask

 // Task to set valid OTP state
task set_valid_otp_state(input lc_state_e state);
    from_otp_to_lcc_program_i.valid = 1;
    from_otp_to_lcc_program_i.state = state;
endtask

// Task to set LCC state and request
task set_lcc_state_req(input lc_state_e state);
    from_lcc_to_otp_program_i.state = state;
    from_lcc_to_otp_program_i.req = 1;
endtask

// Task to assert Caliptra Core signals and registers
task assert_prod_debug(input logic [2:0] switch_case);
    case(switch_case)
        0: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dft_en_mask_reg0_1 = 64'h4;
            ss_soc_dbg_unlock_level_i = 64'h2;
        end
        1: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dft_en_mask_reg0_1 = 64'h4;
            ss_soc_dbg_unlock_level_i = 64'h4;
        end
        2: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dft_en_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h6;
            ss_soc_dbg_unlock_level_i = 64'h4;
        end
        3: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dft_en_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h6;
            ss_soc_dbg_unlock_level_i = 64'h6;
        end
        4: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dft_en_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dbg_unlock_level_i = 64'h8;
        end
        5: begin
            ss_soc_dbg_unlock_mask_reg0_1 = 64'h8;
            ss_soc_dft_en_mask_reg0_1 = 64'h0;
            ss_soc_CLTAP_unlock_mask_reg0_1 = 64'h0;
            ss_soc_dbg_unlock_level_i = 64'h8;
        end
        default: $fatal("Invalid switch_case value");
    endcase
endtask

// Task to set LC debug signals
task set_lc_debug_signals(input logic enable);
    lc_dft_en_i = enable ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
    lc_hw_debug_en_i = enable ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
endtask


initial begin
    repeat(10) @(negedge clk);
    set_valid_otp_state(LcStScrap);
    @(posedge clk);
    apply_reset();
    repeat(20) @(negedge clk);
    set_valid_otp_state(LcStTestUnlocked0);
    repeat(20) @(negedge clk);
    apply_reset();
    set_valid_otp_state(LcStDev);
    repeat(20) @(negedge clk);
    set_valid_otp_state(LcStScrap);
    repeat(20) @(negedge clk);
    apply_reset();
    set_valid_otp_state(LcStDev);
    ss_dbg_manuf_enable_i = 1;
    apply_reset();
    ss_dbg_manuf_enable_i = 0;
    repeat(20) @(negedge clk);
    apply_reset();
    set_valid_otp_state(LcStProd);
    repeat(20) @(negedge clk);
    assert_prod_debug(0);
    repeat(20) @(negedge clk);
    apply_reset();
    assert_prod_debug(1);
    repeat(20) @(negedge clk);
    apply_reset();
    assert_prod_debug(2);
    repeat(20) @(negedge clk);
    apply_reset();
    repeat(20) @(negedge clk);
    assert_prod_debug(3);
    repeat(20) @(negedge clk);
    repeat(20) @(negedge clk);
    apply_reset();
    assert_prod_debug(4);
    repeat(20) @(negedge clk);
    apply_reset();
    repeat(20) @(negedge clk);
    assert_prod_debug(5);
    repeat(20) @(negedge clk);
    $finish;
end

endmodule


