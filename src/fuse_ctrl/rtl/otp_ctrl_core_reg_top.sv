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



`include "caliptra_prim_assert.sv"

module otp_ctrl_core_reg_top (
  input clk_i,
  input rst_ni,
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Output port for window
  output tlul_pkg::tl_h2d_t tl_win_o,
  input  tlul_pkg::tl_d2h_t tl_win_i,

  // To HW
  output otp_ctrl_reg_pkg::otp_ctrl_core_reg2hw_t reg2hw, // Write
  input  otp_ctrl_reg_pkg::otp_ctrl_core_hw2reg_t hw2reg, // Read

  // Integrity check errors
  output logic intg_err_o
);

  import otp_ctrl_reg_pkg::* ;

  localparam int AW = 13;
  localparam int DW = 32;
  localparam int DBW = DW/8;                    // Byte Width

  // register signals
  logic           reg_we;
  logic           reg_re;
  logic [AW-1:0]  reg_addr;
  logic [DW-1:0]  reg_wdata;
  logic [DBW-1:0] reg_be;
  logic [DW-1:0]  reg_rdata;
  logic           reg_error;

  logic          addrmiss, wr_err;

  logic [DW-1:0] reg_rdata_next;
  logic reg_busy;

  tlul_pkg::tl_h2d_t tl_reg_h2d;
  tlul_pkg::tl_d2h_t tl_reg_d2h;


  // incoming payload check
  logic intg_err;
  tlul_cmd_intg_chk u_chk (
    .tl_i(tl_i),
    .err_o(intg_err)
  );

  // also check for spurious write enables
  logic reg_we_err;
  logic [104:0] reg_we_check;
  caliptra_prim_reg_we_check #(
    .OneHotWidth(105)
  ) u_caliptra_prim_reg_we_check (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .oh_i  (reg_we_check),
    .en_i  (reg_we && !addrmiss),
    .err_o (reg_we_err)
  );

  logic err_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_q <= '0;
    end else if (intg_err || reg_we_err) begin
      err_q <= 1'b1;
    end
  end

  // integrity error output is permanent and should be used for alert generation
  // register errors are transactional
  assign intg_err_o = err_q | intg_err | reg_we_err;

  // outgoing integrity generation
  tlul_pkg::tl_d2h_t tl_o_pre;
  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_rsp_intg_gen (
    .tl_i(tl_o_pre),
    .tl_o(tl_o)
  );

  tlul_pkg::tl_h2d_t tl_socket_h2d [2];
  tlul_pkg::tl_d2h_t tl_socket_d2h [2];

  logic [0:0] reg_steer;

  // socket_1n connection
  assign tl_reg_h2d = tl_socket_h2d[1];
  assign tl_socket_d2h[1] = tl_reg_d2h;

  assign tl_win_o = tl_socket_h2d[0];
  assign tl_socket_d2h[0] = tl_win_i;

  // Create Socket_1n
  tlul_socket_1n #(
    .N            (2),
    .HReqPass     (1'b1),
    .HRspPass     (1'b1),
    .DReqPass     ({2{1'b1}}),
    .DRspPass     ({2{1'b1}}),
    .HReqDepth    (4'h0),
    .HRspDepth    (4'h0),
    .DReqDepth    ({2{4'h0}}),
    .DRspDepth    ({2{4'h0}}),
    .ExplicitErrs (1'b0)
  ) u_socket (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .tl_h_i (tl_i),
    .tl_h_o (tl_o_pre),
    .tl_d_o (tl_socket_h2d),
    .tl_d_i (tl_socket_d2h),
    .dev_select_i (reg_steer)
  );

  // Create steering logic
  always_comb begin
    reg_steer =
        tl_i.a_address[AW-1:0] inside {[4096:8191]} ? 1'd0 :
        // Default set to register
        1'd1;

    // Override this in case of an integrity error
    if (intg_err) begin
      reg_steer = 1'd1;
    end
  end

  tlul_adapter_reg #(
    .RegAw(AW),
    .RegDw(DW),
    .EnableDataIntgGen(0)
  ) u_reg_if (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),

    .tl_i (tl_reg_h2d),
    .tl_o (tl_reg_d2h),

    .en_ifetch_i(caliptra_prim_mubi_pkg::MuBi4False),
    .intg_error_o(),

    .we_o    (reg_we),
    .re_o    (reg_re),
    .addr_o  (reg_addr),
    .wdata_o (reg_wdata),
    .be_o    (reg_be),
    .busy_i  (reg_busy),
    .rdata_i (reg_rdata),
    .error_i (reg_error)
  );

  // cdc oversampling signals

  assign reg_rdata = reg_rdata_next ;
  assign reg_error = addrmiss | wr_err | intg_err;

  // Define SW related signals
  // Format: <reg>_<field>_{wd|we|qs}
  //        or <reg>_{wd|we|qs} if field == 1 or 0
  logic intr_state_we;
  logic intr_state_otp_operation_done_qs;
  logic intr_state_otp_operation_done_wd;
  logic intr_state_otp_error_qs;
  logic intr_state_otp_error_wd;
  logic intr_enable_we;
  logic intr_enable_otp_operation_done_qs;
  logic intr_enable_otp_operation_done_wd;
  logic intr_enable_otp_error_qs;
  logic intr_enable_otp_error_wd;
  logic intr_test_we;
  logic intr_test_otp_operation_done_wd;
  logic intr_test_otp_error_wd;
  logic alert_test_we;
  logic alert_test_fatal_macro_error_wd;
  logic alert_test_fatal_check_error_wd;
  logic alert_test_fatal_bus_integ_error_wd;
  logic alert_test_fatal_prim_otp_alert_wd;
  logic alert_test_recov_prim_otp_alert_wd;
  logic status_re;
  logic status_sw_test_unlock_partition_error_qs;
  logic status_secret_manuf_partition_error_qs;
  logic status_secret_prod_partition_0_error_qs;
  logic status_secret_prod_partition_1_error_qs;
  logic status_secret_prod_partition_2_error_qs;
  logic status_secret_prod_partition_3_error_qs;
  logic status_sw_manuf_partition_error_qs;
  logic status_secret_lc_transition_partition_error_qs;
  logic status_svn_partition_error_qs;
  logic status_vendor_test_partition_error_qs;
  logic status_vendor_hashes_manuf_partition_error_qs;
  logic status_vendor_hashes_prod_partition_error_qs;
  logic status_vendor_revocations_prod_partition_error_qs;
  logic status_vendor_secret_prod_partition_error_qs;
  logic status_vendor_non_secret_prod_partition_error_qs;
  logic status_cptra_ss_lock_hek_prod_0_error_qs;
  logic status_cptra_ss_lock_hek_prod_1_error_qs;
  logic status_cptra_ss_lock_hek_prod_2_error_qs;
  logic status_cptra_ss_lock_hek_prod_3_error_qs;
  logic status_cptra_ss_lock_hek_prod_4_error_qs;
  logic status_cptra_ss_lock_hek_prod_5_error_qs;
  logic status_cptra_ss_lock_hek_prod_6_error_qs;
  logic status_cptra_ss_lock_hek_prod_7_error_qs;
  logic status_life_cycle_error_qs;
  logic status_dai_error_qs;
  logic status_lci_error_qs;
  logic status_timeout_error_qs;
  logic status_lfsr_fsm_error_qs;
  logic status_scrambling_fsm_error_qs;
  logic status_bus_integ_error_qs;
  logic status_dai_idle_qs;
  logic status_check_pending_qs;
  logic err_code_0_re;
  logic [2:0] err_code_0_qs;
  logic err_code_1_re;
  logic [2:0] err_code_1_qs;
  logic err_code_2_re;
  logic [2:0] err_code_2_qs;
  logic err_code_3_re;
  logic [2:0] err_code_3_qs;
  logic err_code_4_re;
  logic [2:0] err_code_4_qs;
  logic err_code_5_re;
  logic [2:0] err_code_5_qs;
  logic err_code_6_re;
  logic [2:0] err_code_6_qs;
  logic err_code_7_re;
  logic [2:0] err_code_7_qs;
  logic err_code_8_re;
  logic [2:0] err_code_8_qs;
  logic err_code_9_re;
  logic [2:0] err_code_9_qs;
  logic err_code_10_re;
  logic [2:0] err_code_10_qs;
  logic err_code_11_re;
  logic [2:0] err_code_11_qs;
  logic err_code_12_re;
  logic [2:0] err_code_12_qs;
  logic err_code_13_re;
  logic [2:0] err_code_13_qs;
  logic err_code_14_re;
  logic [2:0] err_code_14_qs;
  logic err_code_15_re;
  logic [2:0] err_code_15_qs;
  logic err_code_16_re;
  logic [2:0] err_code_16_qs;
  logic err_code_17_re;
  logic [2:0] err_code_17_qs;
  logic err_code_18_re;
  logic [2:0] err_code_18_qs;
  logic err_code_19_re;
  logic [2:0] err_code_19_qs;
  logic err_code_20_re;
  logic [2:0] err_code_20_qs;
  logic err_code_21_re;
  logic [2:0] err_code_21_qs;
  logic err_code_22_re;
  logic [2:0] err_code_22_qs;
  logic err_code_23_re;
  logic [2:0] err_code_23_qs;
  logic err_code_24_re;
  logic [2:0] err_code_24_qs;
  logic err_code_25_re;
  logic [2:0] err_code_25_qs;
  logic direct_access_regwen_re;
  logic direct_access_regwen_we;
  logic direct_access_regwen_qs;
  logic direct_access_regwen_wd;
  logic direct_access_cmd_we;
  logic direct_access_cmd_rd_wd;
  logic direct_access_cmd_wr_wd;
  logic direct_access_cmd_digest_wd;
  logic direct_access_cmd_zeroize_wd;
  logic direct_access_address_we;
  logic [11:0] direct_access_address_qs;
  logic [11:0] direct_access_address_wd;
  logic direct_access_wdata_0_we;
  logic [31:0] direct_access_wdata_0_qs;
  logic [31:0] direct_access_wdata_0_wd;
  logic direct_access_wdata_1_we;
  logic [31:0] direct_access_wdata_1_qs;
  logic [31:0] direct_access_wdata_1_wd;
  logic direct_access_rdata_0_re;
  logic [31:0] direct_access_rdata_0_qs;
  logic direct_access_rdata_1_re;
  logic [31:0] direct_access_rdata_1_qs;
  logic check_trigger_regwen_we;
  logic check_trigger_regwen_qs;
  logic check_trigger_regwen_wd;
  logic check_trigger_we;
  logic check_trigger_integrity_wd;
  logic check_trigger_consistency_wd;
  logic check_regwen_we;
  logic check_regwen_qs;
  logic check_regwen_wd;
  logic check_timeout_we;
  logic [31:0] check_timeout_qs;
  logic [31:0] check_timeout_wd;
  logic integrity_check_period_we;
  logic [31:0] integrity_check_period_qs;
  logic [31:0] integrity_check_period_wd;
  logic consistency_check_period_we;
  logic [31:0] consistency_check_period_qs;
  logic [31:0] consistency_check_period_wd;
  logic sw_manuf_partition_read_lock_we;
  logic sw_manuf_partition_read_lock_qs;
  logic sw_manuf_partition_read_lock_wd;
  logic svn_partition_read_lock_we;
  logic svn_partition_read_lock_qs;
  logic svn_partition_read_lock_wd;
  logic vendor_test_partition_read_lock_we;
  logic vendor_test_partition_read_lock_qs;
  logic vendor_test_partition_read_lock_wd;
  logic vendor_hashes_manuf_partition_read_lock_we;
  logic vendor_hashes_manuf_partition_read_lock_qs;
  logic vendor_hashes_manuf_partition_read_lock_wd;
  logic vendor_hashes_prod_partition_read_lock_we;
  logic vendor_hashes_prod_partition_read_lock_qs;
  logic vendor_hashes_prod_partition_read_lock_wd;
  logic vendor_revocations_prod_partition_read_lock_we;
  logic vendor_revocations_prod_partition_read_lock_qs;
  logic vendor_revocations_prod_partition_read_lock_wd;
  logic vendor_non_secret_prod_partition_read_lock_we;
  logic vendor_non_secret_prod_partition_read_lock_qs;
  logic vendor_non_secret_prod_partition_read_lock_wd;
  logic cptra_ss_lock_hek_prod_0_read_lock_we;
  logic cptra_ss_lock_hek_prod_0_read_lock_qs;
  logic cptra_ss_lock_hek_prod_0_read_lock_wd;
  logic cptra_ss_lock_hek_prod_1_read_lock_we;
  logic cptra_ss_lock_hek_prod_1_read_lock_qs;
  logic cptra_ss_lock_hek_prod_1_read_lock_wd;
  logic cptra_ss_lock_hek_prod_2_read_lock_we;
  logic cptra_ss_lock_hek_prod_2_read_lock_qs;
  logic cptra_ss_lock_hek_prod_2_read_lock_wd;
  logic cptra_ss_lock_hek_prod_3_read_lock_we;
  logic cptra_ss_lock_hek_prod_3_read_lock_qs;
  logic cptra_ss_lock_hek_prod_3_read_lock_wd;
  logic cptra_ss_lock_hek_prod_4_read_lock_we;
  logic cptra_ss_lock_hek_prod_4_read_lock_qs;
  logic cptra_ss_lock_hek_prod_4_read_lock_wd;
  logic cptra_ss_lock_hek_prod_5_read_lock_we;
  logic cptra_ss_lock_hek_prod_5_read_lock_qs;
  logic cptra_ss_lock_hek_prod_5_read_lock_wd;
  logic cptra_ss_lock_hek_prod_6_read_lock_we;
  logic cptra_ss_lock_hek_prod_6_read_lock_qs;
  logic cptra_ss_lock_hek_prod_6_read_lock_wd;
  logic cptra_ss_lock_hek_prod_7_read_lock_we;
  logic cptra_ss_lock_hek_prod_7_read_lock_qs;
  logic cptra_ss_lock_hek_prod_7_read_lock_wd;
  logic vendor_pk_hash_volatile_lock_we;
  logic [31:0] vendor_pk_hash_volatile_lock_qs;
  logic [31:0] vendor_pk_hash_volatile_lock_wd;
  logic ratchet_seed_volatile_lock_we;
  logic [31:0] ratchet_seed_volatile_lock_qs;
  logic [31:0] ratchet_seed_volatile_lock_wd;
  logic sw_test_unlock_partition_digest_0_re;
  logic [31:0] sw_test_unlock_partition_digest_0_qs;
  logic sw_test_unlock_partition_digest_1_re;
  logic [31:0] sw_test_unlock_partition_digest_1_qs;
  logic secret_manuf_partition_digest_0_re;
  logic [31:0] secret_manuf_partition_digest_0_qs;
  logic secret_manuf_partition_digest_1_re;
  logic [31:0] secret_manuf_partition_digest_1_qs;
  logic secret_prod_partition_0_digest_0_re;
  logic [31:0] secret_prod_partition_0_digest_0_qs;
  logic secret_prod_partition_0_digest_1_re;
  logic [31:0] secret_prod_partition_0_digest_1_qs;
  logic secret_prod_partition_1_digest_0_re;
  logic [31:0] secret_prod_partition_1_digest_0_qs;
  logic secret_prod_partition_1_digest_1_re;
  logic [31:0] secret_prod_partition_1_digest_1_qs;
  logic secret_prod_partition_2_digest_0_re;
  logic [31:0] secret_prod_partition_2_digest_0_qs;
  logic secret_prod_partition_2_digest_1_re;
  logic [31:0] secret_prod_partition_2_digest_1_qs;
  logic secret_prod_partition_3_digest_0_re;
  logic [31:0] secret_prod_partition_3_digest_0_qs;
  logic secret_prod_partition_3_digest_1_re;
  logic [31:0] secret_prod_partition_3_digest_1_qs;
  logic sw_manuf_partition_digest_0_re;
  logic [31:0] sw_manuf_partition_digest_0_qs;
  logic sw_manuf_partition_digest_1_re;
  logic [31:0] sw_manuf_partition_digest_1_qs;
  logic secret_lc_transition_partition_digest_0_re;
  logic [31:0] secret_lc_transition_partition_digest_0_qs;
  logic secret_lc_transition_partition_digest_1_re;
  logic [31:0] secret_lc_transition_partition_digest_1_qs;
  logic vendor_test_partition_digest_0_re;
  logic [31:0] vendor_test_partition_digest_0_qs;
  logic vendor_test_partition_digest_1_re;
  logic [31:0] vendor_test_partition_digest_1_qs;
  logic vendor_hashes_manuf_partition_digest_0_re;
  logic [31:0] vendor_hashes_manuf_partition_digest_0_qs;
  logic vendor_hashes_manuf_partition_digest_1_re;
  logic [31:0] vendor_hashes_manuf_partition_digest_1_qs;
  logic vendor_hashes_prod_partition_digest_0_re;
  logic [31:0] vendor_hashes_prod_partition_digest_0_qs;
  logic vendor_hashes_prod_partition_digest_1_re;
  logic [31:0] vendor_hashes_prod_partition_digest_1_qs;
  logic vendor_revocations_prod_partition_digest_0_re;
  logic [31:0] vendor_revocations_prod_partition_digest_0_qs;
  logic vendor_revocations_prod_partition_digest_1_re;
  logic [31:0] vendor_revocations_prod_partition_digest_1_qs;
  logic vendor_secret_prod_partition_digest_0_re;
  logic [31:0] vendor_secret_prod_partition_digest_0_qs;
  logic vendor_secret_prod_partition_digest_1_re;
  logic [31:0] vendor_secret_prod_partition_digest_1_qs;
  logic vendor_non_secret_prod_partition_digest_0_re;
  logic [31:0] vendor_non_secret_prod_partition_digest_0_qs;
  logic vendor_non_secret_prod_partition_digest_1_re;
  logic [31:0] vendor_non_secret_prod_partition_digest_1_qs;
  logic cptra_ss_lock_hek_prod_0_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_0_digest_0_qs;
  logic cptra_ss_lock_hek_prod_0_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_0_digest_1_qs;
  logic cptra_ss_lock_hek_prod_1_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_1_digest_0_qs;
  logic cptra_ss_lock_hek_prod_1_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_1_digest_1_qs;
  logic cptra_ss_lock_hek_prod_2_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_2_digest_0_qs;
  logic cptra_ss_lock_hek_prod_2_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_2_digest_1_qs;
  logic cptra_ss_lock_hek_prod_3_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_3_digest_0_qs;
  logic cptra_ss_lock_hek_prod_3_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_3_digest_1_qs;
  logic cptra_ss_lock_hek_prod_4_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_4_digest_0_qs;
  logic cptra_ss_lock_hek_prod_4_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_4_digest_1_qs;
  logic cptra_ss_lock_hek_prod_5_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_5_digest_0_qs;
  logic cptra_ss_lock_hek_prod_5_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_5_digest_1_qs;
  logic cptra_ss_lock_hek_prod_6_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_6_digest_0_qs;
  logic cptra_ss_lock_hek_prod_6_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_6_digest_1_qs;
  logic cptra_ss_lock_hek_prod_7_digest_0_re;
  logic [31:0] cptra_ss_lock_hek_prod_7_digest_0_qs;
  logic cptra_ss_lock_hek_prod_7_digest_1_re;
  logic [31:0] cptra_ss_lock_hek_prod_7_digest_1_qs;

  // Register instances
  // R[intr_state]: V(False)
  //   F[otp_operation_done]: 0:0
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW1C),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_intr_state_otp_operation_done (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (intr_state_we),
    .wd     (intr_state_otp_operation_done_wd),

    // from internal hardware
    .de     (hw2reg.intr_state.otp_operation_done.de),
    .d      (hw2reg.intr_state.otp_operation_done.d),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.intr_state.otp_operation_done.q),
    .ds     (),

    // to register interface (read)
    .qs     (intr_state_otp_operation_done_qs)
  );

  //   F[otp_error]: 1:1
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW1C),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_intr_state_otp_error (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (intr_state_we),
    .wd     (intr_state_otp_error_wd),

    // from internal hardware
    .de     (hw2reg.intr_state.otp_error.de),
    .d      (hw2reg.intr_state.otp_error.d),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.intr_state.otp_error.q),
    .ds     (),

    // to register interface (read)
    .qs     (intr_state_otp_error_qs)
  );


  // R[intr_enable]: V(False)
  //   F[otp_operation_done]: 0:0
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_intr_enable_otp_operation_done (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (intr_enable_we),
    .wd     (intr_enable_otp_operation_done_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.intr_enable.otp_operation_done.q),
    .ds     (),

    // to register interface (read)
    .qs     (intr_enable_otp_operation_done_qs)
  );

  //   F[otp_error]: 1:1
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_intr_enable_otp_error (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (intr_enable_we),
    .wd     (intr_enable_otp_error_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.intr_enable.otp_error.q),
    .ds     (),

    // to register interface (read)
    .qs     (intr_enable_otp_error_qs)
  );


  // R[intr_test]: V(True)
  logic intr_test_qe;
  logic [1:0] intr_test_flds_we;
  assign intr_test_qe = &intr_test_flds_we;
  //   F[otp_operation_done]: 0:0
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_intr_test_otp_operation_done (
    .re     (1'b0),
    .we     (intr_test_we),
    .wd     (intr_test_otp_operation_done_wd),
    .d      ('0),
    .qre    (),
    .qe     (intr_test_flds_we[0]),
    .q      (reg2hw.intr_test.otp_operation_done.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.intr_test.otp_operation_done.qe = intr_test_qe;

  //   F[otp_error]: 1:1
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_intr_test_otp_error (
    .re     (1'b0),
    .we     (intr_test_we),
    .wd     (intr_test_otp_error_wd),
    .d      ('0),
    .qre    (),
    .qe     (intr_test_flds_we[1]),
    .q      (reg2hw.intr_test.otp_error.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.intr_test.otp_error.qe = intr_test_qe;


  // R[alert_test]: V(True)
  logic alert_test_qe;
  logic [4:0] alert_test_flds_we;
  assign alert_test_qe = &alert_test_flds_we;
  //   F[fatal_macro_error]: 0:0
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test_fatal_macro_error (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_fatal_macro_error_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[0]),
    .q      (reg2hw.alert_test.fatal_macro_error.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.alert_test.fatal_macro_error.qe = alert_test_qe;

  //   F[fatal_check_error]: 1:1
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test_fatal_check_error (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_fatal_check_error_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[1]),
    .q      (reg2hw.alert_test.fatal_check_error.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.alert_test.fatal_check_error.qe = alert_test_qe;

  //   F[fatal_bus_integ_error]: 2:2
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test_fatal_bus_integ_error (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_fatal_bus_integ_error_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[2]),
    .q      (reg2hw.alert_test.fatal_bus_integ_error.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.alert_test.fatal_bus_integ_error.qe = alert_test_qe;

  //   F[fatal_prim_otp_alert]: 3:3
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test_fatal_prim_otp_alert (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_fatal_prim_otp_alert_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[3]),
    .q      (reg2hw.alert_test.fatal_prim_otp_alert.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.alert_test.fatal_prim_otp_alert.qe = alert_test_qe;

  //   F[recov_prim_otp_alert]: 4:4
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_alert_test_recov_prim_otp_alert (
    .re     (1'b0),
    .we     (alert_test_we),
    .wd     (alert_test_recov_prim_otp_alert_wd),
    .d      ('0),
    .qre    (),
    .qe     (alert_test_flds_we[4]),
    .q      (reg2hw.alert_test.recov_prim_otp_alert.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.alert_test.recov_prim_otp_alert.qe = alert_test_qe;


  // R[status]: V(True)
  //   F[sw_test_unlock_partition_error]: 0:0
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_sw_test_unlock_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.sw_test_unlock_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_sw_test_unlock_partition_error_qs)
  );

  //   F[secret_manuf_partition_error]: 1:1
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_manuf_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_manuf_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_manuf_partition_error_qs)
  );

  //   F[secret_prod_partition_0_error]: 2:2
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_prod_partition_0_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_prod_partition_0_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_prod_partition_0_error_qs)
  );

  //   F[secret_prod_partition_1_error]: 3:3
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_prod_partition_1_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_prod_partition_1_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_prod_partition_1_error_qs)
  );

  //   F[secret_prod_partition_2_error]: 4:4
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_prod_partition_2_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_prod_partition_2_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_prod_partition_2_error_qs)
  );

  //   F[secret_prod_partition_3_error]: 5:5
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_prod_partition_3_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_prod_partition_3_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_prod_partition_3_error_qs)
  );

  //   F[sw_manuf_partition_error]: 6:6
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_sw_manuf_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.sw_manuf_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_sw_manuf_partition_error_qs)
  );

  //   F[secret_lc_transition_partition_error]: 7:7
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_secret_lc_transition_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.secret_lc_transition_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_secret_lc_transition_partition_error_qs)
  );

  //   F[svn_partition_error]: 8:8
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_svn_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.svn_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_svn_partition_error_qs)
  );

  //   F[vendor_test_partition_error]: 9:9
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_test_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_test_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_test_partition_error_qs)
  );

  //   F[vendor_hashes_manuf_partition_error]: 10:10
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_hashes_manuf_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_hashes_manuf_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_hashes_manuf_partition_error_qs)
  );

  //   F[vendor_hashes_prod_partition_error]: 11:11
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_hashes_prod_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_hashes_prod_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_hashes_prod_partition_error_qs)
  );

  //   F[vendor_revocations_prod_partition_error]: 12:12
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_revocations_prod_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_revocations_prod_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_revocations_prod_partition_error_qs)
  );

  //   F[vendor_secret_prod_partition_error]: 13:13
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_secret_prod_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_secret_prod_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_secret_prod_partition_error_qs)
  );

  //   F[vendor_non_secret_prod_partition_error]: 14:14
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_vendor_non_secret_prod_partition_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.vendor_non_secret_prod_partition_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_vendor_non_secret_prod_partition_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_0_error]: 15:15
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_0_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_0_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_0_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_1_error]: 16:16
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_1_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_1_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_1_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_2_error]: 17:17
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_2_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_2_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_2_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_3_error]: 18:18
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_3_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_3_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_3_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_4_error]: 19:19
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_4_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_4_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_4_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_5_error]: 20:20
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_5_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_5_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_5_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_6_error]: 21:21
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_6_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_6_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_6_error_qs)
  );

  //   F[cptra_ss_lock_hek_prod_7_error]: 22:22
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_cptra_ss_lock_hek_prod_7_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.cptra_ss_lock_hek_prod_7_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_cptra_ss_lock_hek_prod_7_error_qs)
  );

  //   F[life_cycle_error]: 23:23
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_life_cycle_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.life_cycle_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_life_cycle_error_qs)
  );

  //   F[dai_error]: 24:24
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_dai_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.dai_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_dai_error_qs)
  );

  //   F[lci_error]: 25:25
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_lci_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.lci_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_lci_error_qs)
  );

  //   F[timeout_error]: 26:26
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_timeout_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.timeout_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_timeout_error_qs)
  );

  //   F[lfsr_fsm_error]: 27:27
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_lfsr_fsm_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.lfsr_fsm_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_lfsr_fsm_error_qs)
  );

  //   F[scrambling_fsm_error]: 28:28
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_scrambling_fsm_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.scrambling_fsm_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_scrambling_fsm_error_qs)
  );

  //   F[bus_integ_error]: 29:29
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_bus_integ_error (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.bus_integ_error.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_bus_integ_error_qs)
  );

  //   F[dai_idle]: 30:30
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_dai_idle (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.dai_idle.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_dai_idle_qs)
  );

  //   F[check_pending]: 31:31
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_status_check_pending (
    .re     (status_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.status.check_pending.d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (status_check_pending_qs)
  );


  // Subregister 0 of Multireg err_code
  // R[err_code_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_0 (
    .re     (err_code_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_0_qs)
  );


  // Subregister 1 of Multireg err_code
  // R[err_code_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_1 (
    .re     (err_code_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_1_qs)
  );


  // Subregister 2 of Multireg err_code
  // R[err_code_2]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_2 (
    .re     (err_code_2_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[2].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_2_qs)
  );


  // Subregister 3 of Multireg err_code
  // R[err_code_3]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_3 (
    .re     (err_code_3_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[3].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_3_qs)
  );


  // Subregister 4 of Multireg err_code
  // R[err_code_4]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_4 (
    .re     (err_code_4_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[4].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_4_qs)
  );


  // Subregister 5 of Multireg err_code
  // R[err_code_5]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_5 (
    .re     (err_code_5_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[5].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_5_qs)
  );


  // Subregister 6 of Multireg err_code
  // R[err_code_6]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_6 (
    .re     (err_code_6_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[6].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_6_qs)
  );


  // Subregister 7 of Multireg err_code
  // R[err_code_7]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_7 (
    .re     (err_code_7_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[7].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_7_qs)
  );


  // Subregister 8 of Multireg err_code
  // R[err_code_8]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_8 (
    .re     (err_code_8_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[8].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_8_qs)
  );


  // Subregister 9 of Multireg err_code
  // R[err_code_9]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_9 (
    .re     (err_code_9_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[9].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_9_qs)
  );


  // Subregister 10 of Multireg err_code
  // R[err_code_10]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_10 (
    .re     (err_code_10_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[10].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_10_qs)
  );


  // Subregister 11 of Multireg err_code
  // R[err_code_11]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_11 (
    .re     (err_code_11_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[11].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_11_qs)
  );


  // Subregister 12 of Multireg err_code
  // R[err_code_12]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_12 (
    .re     (err_code_12_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[12].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_12_qs)
  );


  // Subregister 13 of Multireg err_code
  // R[err_code_13]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_13 (
    .re     (err_code_13_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[13].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_13_qs)
  );


  // Subregister 14 of Multireg err_code
  // R[err_code_14]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_14 (
    .re     (err_code_14_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[14].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_14_qs)
  );


  // Subregister 15 of Multireg err_code
  // R[err_code_15]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_15 (
    .re     (err_code_15_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[15].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_15_qs)
  );


  // Subregister 16 of Multireg err_code
  // R[err_code_16]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_16 (
    .re     (err_code_16_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[16].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_16_qs)
  );


  // Subregister 17 of Multireg err_code
  // R[err_code_17]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_17 (
    .re     (err_code_17_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[17].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_17_qs)
  );


  // Subregister 18 of Multireg err_code
  // R[err_code_18]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_18 (
    .re     (err_code_18_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[18].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_18_qs)
  );


  // Subregister 19 of Multireg err_code
  // R[err_code_19]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_19 (
    .re     (err_code_19_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[19].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_19_qs)
  );


  // Subregister 20 of Multireg err_code
  // R[err_code_20]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_20 (
    .re     (err_code_20_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[20].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_20_qs)
  );


  // Subregister 21 of Multireg err_code
  // R[err_code_21]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_21 (
    .re     (err_code_21_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[21].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_21_qs)
  );


  // Subregister 22 of Multireg err_code
  // R[err_code_22]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_22 (
    .re     (err_code_22_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[22].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_22_qs)
  );


  // Subregister 23 of Multireg err_code
  // R[err_code_23]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_23 (
    .re     (err_code_23_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[23].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_23_qs)
  );


  // Subregister 24 of Multireg err_code
  // R[err_code_24]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_24 (
    .re     (err_code_24_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[24].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_24_qs)
  );


  // Subregister 25 of Multireg err_code
  // R[err_code_25]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (3)
  ) u_err_code_25 (
    .re     (err_code_25_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.err_code[25].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (err_code_25_qs)
  );


  // R[direct_access_regwen]: V(True)
  logic direct_access_regwen_qe;
  logic [0:0] direct_access_regwen_flds_we;
  assign direct_access_regwen_qe = &direct_access_regwen_flds_we;
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_direct_access_regwen (
    .re     (direct_access_regwen_re),
    .we     (direct_access_regwen_we),
    .wd     (direct_access_regwen_wd),
    .d      (hw2reg.direct_access_regwen.d),
    .qre    (),
    .qe     (direct_access_regwen_flds_we[0]),
    .q      (reg2hw.direct_access_regwen.q),
    .ds     (),
    .qs     (direct_access_regwen_qs)
  );
  assign reg2hw.direct_access_regwen.qe = direct_access_regwen_qe;


  // R[direct_access_cmd]: V(True)
  logic direct_access_cmd_qe;
  logic [3:0] direct_access_cmd_flds_we;
  assign direct_access_cmd_qe = &direct_access_cmd_flds_we;
  // Create REGWEN-gated WE signal
  logic direct_access_cmd_gated_we;
  assign direct_access_cmd_gated_we = direct_access_cmd_we & direct_access_regwen_qs;
  //   F[rd]: 0:0
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_direct_access_cmd_rd (
    .re     (1'b0),
    .we     (direct_access_cmd_gated_we),
    .wd     (direct_access_cmd_rd_wd),
    .d      ('0),
    .qre    (),
    .qe     (direct_access_cmd_flds_we[0]),
    .q      (reg2hw.direct_access_cmd.rd.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.direct_access_cmd.rd.qe = direct_access_cmd_qe;

  //   F[wr]: 1:1
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_direct_access_cmd_wr (
    .re     (1'b0),
    .we     (direct_access_cmd_gated_we),
    .wd     (direct_access_cmd_wr_wd),
    .d      ('0),
    .qre    (),
    .qe     (direct_access_cmd_flds_we[1]),
    .q      (reg2hw.direct_access_cmd.wr.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.direct_access_cmd.wr.qe = direct_access_cmd_qe;

  //   F[digest]: 2:2
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_direct_access_cmd_digest (
    .re     (1'b0),
    .we     (direct_access_cmd_gated_we),
    .wd     (direct_access_cmd_digest_wd),
    .d      ('0),
    .qre    (),
    .qe     (direct_access_cmd_flds_we[2]),
    .q      (reg2hw.direct_access_cmd.digest.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.direct_access_cmd.digest.qe = direct_access_cmd_qe;

  //   F[zeroize]: 3:3
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_direct_access_cmd_zeroize (
    .re     (1'b0),
    .we     (direct_access_cmd_gated_we),
    .wd     (direct_access_cmd_zeroize_wd),
    .d      ('0),
    .qre    (),
    .qe     (direct_access_cmd_flds_we[3]),
    .q      (reg2hw.direct_access_cmd.zeroize.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.direct_access_cmd.zeroize.qe = direct_access_cmd_qe;


  // R[direct_access_address]: V(False)
  // Create REGWEN-gated WE signal
  logic direct_access_address_gated_we;
  assign direct_access_address_gated_we = direct_access_address_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (12),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (12'h0),
    .Mubi    (1'b0)
  ) u_direct_access_address (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (direct_access_address_gated_we),
    .wd     (direct_access_address_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.direct_access_address.q),
    .ds     (),

    // to register interface (read)
    .qs     (direct_access_address_qs)
  );


  // Subregister 0 of Multireg direct_access_wdata
  // R[direct_access_wdata_0]: V(False)
  // Create REGWEN-gated WE signal
  logic direct_access_wdata_0_gated_we;
  assign direct_access_wdata_0_gated_we = direct_access_wdata_0_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_direct_access_wdata_0 (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (direct_access_wdata_0_gated_we),
    .wd     (direct_access_wdata_0_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.direct_access_wdata[0].q),
    .ds     (),

    // to register interface (read)
    .qs     (direct_access_wdata_0_qs)
  );


  // Subregister 1 of Multireg direct_access_wdata
  // R[direct_access_wdata_1]: V(False)
  // Create REGWEN-gated WE signal
  logic direct_access_wdata_1_gated_we;
  assign direct_access_wdata_1_gated_we = direct_access_wdata_1_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_direct_access_wdata_1 (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (direct_access_wdata_1_gated_we),
    .wd     (direct_access_wdata_1_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.direct_access_wdata[1].q),
    .ds     (),

    // to register interface (read)
    .qs     (direct_access_wdata_1_qs)
  );


  // Subregister 0 of Multireg direct_access_rdata
  // R[direct_access_rdata_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_direct_access_rdata_0 (
    .re     (direct_access_rdata_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.direct_access_rdata[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (direct_access_rdata_0_qs)
  );


  // Subregister 1 of Multireg direct_access_rdata
  // R[direct_access_rdata_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_direct_access_rdata_1 (
    .re     (direct_access_rdata_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.direct_access_rdata[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (direct_access_rdata_1_qs)
  );


  // R[check_trigger_regwen]: V(False)
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_check_trigger_regwen (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (check_trigger_regwen_we),
    .wd     (check_trigger_regwen_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (),
    .ds     (),

    // to register interface (read)
    .qs     (check_trigger_regwen_qs)
  );


  // R[check_trigger]: V(True)
  logic check_trigger_qe;
  logic [1:0] check_trigger_flds_we;
  assign check_trigger_qe = &check_trigger_flds_we;
  // Create REGWEN-gated WE signal
  logic check_trigger_gated_we;
  assign check_trigger_gated_we = check_trigger_we & check_trigger_regwen_qs;
  //   F[integrity]: 0:0
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_check_trigger_integrity (
    .re     (1'b0),
    .we     (check_trigger_gated_we),
    .wd     (check_trigger_integrity_wd),
    .d      ('0),
    .qre    (),
    .qe     (check_trigger_flds_we[0]),
    .q      (reg2hw.check_trigger.integrity.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.check_trigger.integrity.qe = check_trigger_qe;

  //   F[consistency]: 1:1
  caliptra_prim_subreg_ext #(
    .DW    (1)
  ) u_check_trigger_consistency (
    .re     (1'b0),
    .we     (check_trigger_gated_we),
    .wd     (check_trigger_consistency_wd),
    .d      ('0),
    .qre    (),
    .qe     (check_trigger_flds_we[1]),
    .q      (reg2hw.check_trigger.consistency.q),
    .ds     (),
    .qs     ()
  );
  assign reg2hw.check_trigger.consistency.qe = check_trigger_qe;


  // R[check_regwen]: V(False)
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_check_regwen (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (check_regwen_we),
    .wd     (check_regwen_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (),
    .ds     (),

    // to register interface (read)
    .qs     (check_regwen_qs)
  );


  // R[check_timeout]: V(False)
  // Create REGWEN-gated WE signal
  logic check_timeout_gated_we;
  assign check_timeout_gated_we = check_timeout_we & check_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_check_timeout (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (check_timeout_gated_we),
    .wd     (check_timeout_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.check_timeout.q),
    .ds     (),

    // to register interface (read)
    .qs     (check_timeout_qs)
  );


  // R[integrity_check_period]: V(False)
  // Create REGWEN-gated WE signal
  logic integrity_check_period_gated_we;
  assign integrity_check_period_gated_we = integrity_check_period_we & check_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_integrity_check_period (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (integrity_check_period_gated_we),
    .wd     (integrity_check_period_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.integrity_check_period.q),
    .ds     (),

    // to register interface (read)
    .qs     (integrity_check_period_qs)
  );


  // R[consistency_check_period]: V(False)
  // Create REGWEN-gated WE signal
  logic consistency_check_period_gated_we;
  assign consistency_check_period_gated_we = consistency_check_period_we & check_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_consistency_check_period (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (consistency_check_period_gated_we),
    .wd     (consistency_check_period_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.consistency_check_period.q),
    .ds     (),

    // to register interface (read)
    .qs     (consistency_check_period_qs)
  );


  // R[sw_manuf_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic sw_manuf_partition_read_lock_gated_we;
  assign sw_manuf_partition_read_lock_gated_we =
    sw_manuf_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_sw_manuf_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (sw_manuf_partition_read_lock_gated_we),
    .wd     (sw_manuf_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.sw_manuf_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (sw_manuf_partition_read_lock_qs)
  );


  // R[svn_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic svn_partition_read_lock_gated_we;
  assign svn_partition_read_lock_gated_we = svn_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_svn_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (svn_partition_read_lock_gated_we),
    .wd     (svn_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.svn_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (svn_partition_read_lock_qs)
  );


  // R[vendor_test_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic vendor_test_partition_read_lock_gated_we;
  assign vendor_test_partition_read_lock_gated_we =
    vendor_test_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_vendor_test_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_test_partition_read_lock_gated_we),
    .wd     (vendor_test_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_test_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_test_partition_read_lock_qs)
  );


  // R[vendor_hashes_manuf_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic vendor_hashes_manuf_partition_read_lock_gated_we;
  assign vendor_hashes_manuf_partition_read_lock_gated_we =
    vendor_hashes_manuf_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_vendor_hashes_manuf_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_hashes_manuf_partition_read_lock_gated_we),
    .wd     (vendor_hashes_manuf_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_hashes_manuf_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_hashes_manuf_partition_read_lock_qs)
  );


  // R[vendor_hashes_prod_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic vendor_hashes_prod_partition_read_lock_gated_we;
  assign vendor_hashes_prod_partition_read_lock_gated_we =
    vendor_hashes_prod_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_vendor_hashes_prod_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_hashes_prod_partition_read_lock_gated_we),
    .wd     (vendor_hashes_prod_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_hashes_prod_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_hashes_prod_partition_read_lock_qs)
  );


  // R[vendor_revocations_prod_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic vendor_revocations_prod_partition_read_lock_gated_we;
  assign vendor_revocations_prod_partition_read_lock_gated_we =
    vendor_revocations_prod_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_vendor_revocations_prod_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_revocations_prod_partition_read_lock_gated_we),
    .wd     (vendor_revocations_prod_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_revocations_prod_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_revocations_prod_partition_read_lock_qs)
  );


  // R[vendor_non_secret_prod_partition_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic vendor_non_secret_prod_partition_read_lock_gated_we;
  assign vendor_non_secret_prod_partition_read_lock_gated_we =
    vendor_non_secret_prod_partition_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_vendor_non_secret_prod_partition_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_non_secret_prod_partition_read_lock_gated_we),
    .wd     (vendor_non_secret_prod_partition_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_non_secret_prod_partition_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_non_secret_prod_partition_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_0_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_0_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_0_read_lock_gated_we =
    cptra_ss_lock_hek_prod_0_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_0_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_0_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_0_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_0_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_0_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_1_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_1_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_1_read_lock_gated_we =
    cptra_ss_lock_hek_prod_1_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_1_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_1_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_1_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_1_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_1_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_2_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_2_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_2_read_lock_gated_we =
    cptra_ss_lock_hek_prod_2_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_2_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_2_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_2_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_2_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_2_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_3_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_3_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_3_read_lock_gated_we =
    cptra_ss_lock_hek_prod_3_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_3_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_3_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_3_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_3_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_3_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_4_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_4_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_4_read_lock_gated_we =
    cptra_ss_lock_hek_prod_4_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_4_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_4_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_4_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_4_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_4_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_5_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_5_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_5_read_lock_gated_we =
    cptra_ss_lock_hek_prod_5_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_5_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_5_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_5_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_5_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_5_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_6_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_6_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_6_read_lock_gated_we =
    cptra_ss_lock_hek_prod_6_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_6_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_6_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_6_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_6_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_6_read_lock_qs)
  );


  // R[cptra_ss_lock_hek_prod_7_read_lock]: V(False)
  // Create REGWEN-gated WE signal
  logic cptra_ss_lock_hek_prod_7_read_lock_gated_we;
  assign cptra_ss_lock_hek_prod_7_read_lock_gated_we =
    cptra_ss_lock_hek_prod_7_read_lock_we & direct_access_regwen_qs;
  caliptra_prim_subreg #(
    .DW      (1),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessW0C),
    .RESVAL  (1'h1),
    .Mubi    (1'b0)
  ) u_cptra_ss_lock_hek_prod_7_read_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (cptra_ss_lock_hek_prod_7_read_lock_gated_we),
    .wd     (cptra_ss_lock_hek_prod_7_read_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.cptra_ss_lock_hek_prod_7_read_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (cptra_ss_lock_hek_prod_7_read_lock_qs)
  );


  // R[vendor_pk_hash_volatile_lock]: V(False)
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_vendor_pk_hash_volatile_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (vendor_pk_hash_volatile_lock_we),
    .wd     (vendor_pk_hash_volatile_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.vendor_pk_hash_volatile_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (vendor_pk_hash_volatile_lock_qs)
  );


  // R[ratchet_seed_volatile_lock]: V(False)
  caliptra_prim_subreg #(
    .DW      (32),
    .SwAccess(caliptra_prim_subreg_pkg::SwAccessRW),
    .RESVAL  (32'h0),
    .Mubi    (1'b0)
  ) u_ratchet_seed_volatile_lock (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (ratchet_seed_volatile_lock_we),
    .wd     (ratchet_seed_volatile_lock_wd),

    // from internal hardware
    .de     (1'b0),
    .d      ('0),

    // to internal hardware
    .qe     (),
    .q      (reg2hw.ratchet_seed_volatile_lock.q),
    .ds     (),

    // to register interface (read)
    .qs     (ratchet_seed_volatile_lock_qs)
  );


  // Subregister 0 of Multireg sw_test_unlock_partition_digest
  // R[sw_test_unlock_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_sw_test_unlock_partition_digest_0 (
    .re     (sw_test_unlock_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.sw_test_unlock_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (sw_test_unlock_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg sw_test_unlock_partition_digest
  // R[sw_test_unlock_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_sw_test_unlock_partition_digest_1 (
    .re     (sw_test_unlock_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.sw_test_unlock_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (sw_test_unlock_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_manuf_partition_digest
  // R[secret_manuf_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_manuf_partition_digest_0 (
    .re     (secret_manuf_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_manuf_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_manuf_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_manuf_partition_digest
  // R[secret_manuf_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_manuf_partition_digest_1 (
    .re     (secret_manuf_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_manuf_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_manuf_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_prod_partition_0_digest
  // R[secret_prod_partition_0_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_0_digest_0 (
    .re     (secret_prod_partition_0_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_0_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_0_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_prod_partition_0_digest
  // R[secret_prod_partition_0_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_0_digest_1 (
    .re     (secret_prod_partition_0_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_0_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_0_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_prod_partition_1_digest
  // R[secret_prod_partition_1_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_1_digest_0 (
    .re     (secret_prod_partition_1_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_1_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_1_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_prod_partition_1_digest
  // R[secret_prod_partition_1_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_1_digest_1 (
    .re     (secret_prod_partition_1_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_1_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_1_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_prod_partition_2_digest
  // R[secret_prod_partition_2_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_2_digest_0 (
    .re     (secret_prod_partition_2_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_2_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_2_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_prod_partition_2_digest
  // R[secret_prod_partition_2_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_2_digest_1 (
    .re     (secret_prod_partition_2_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_2_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_2_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_prod_partition_3_digest
  // R[secret_prod_partition_3_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_3_digest_0 (
    .re     (secret_prod_partition_3_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_3_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_3_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_prod_partition_3_digest
  // R[secret_prod_partition_3_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_prod_partition_3_digest_1 (
    .re     (secret_prod_partition_3_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_prod_partition_3_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_prod_partition_3_digest_1_qs)
  );


  // Subregister 0 of Multireg sw_manuf_partition_digest
  // R[sw_manuf_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_sw_manuf_partition_digest_0 (
    .re     (sw_manuf_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.sw_manuf_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (sw_manuf_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg sw_manuf_partition_digest
  // R[sw_manuf_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_sw_manuf_partition_digest_1 (
    .re     (sw_manuf_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.sw_manuf_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (sw_manuf_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg secret_lc_transition_partition_digest
  // R[secret_lc_transition_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_lc_transition_partition_digest_0 (
    .re     (secret_lc_transition_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_lc_transition_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_lc_transition_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg secret_lc_transition_partition_digest
  // R[secret_lc_transition_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_secret_lc_transition_partition_digest_1 (
    .re     (secret_lc_transition_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.secret_lc_transition_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (secret_lc_transition_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_test_partition_digest
  // R[vendor_test_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_test_partition_digest_0 (
    .re     (vendor_test_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_test_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_test_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_test_partition_digest
  // R[vendor_test_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_test_partition_digest_1 (
    .re     (vendor_test_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_test_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_test_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_hashes_manuf_partition_digest
  // R[vendor_hashes_manuf_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_hashes_manuf_partition_digest_0 (
    .re     (vendor_hashes_manuf_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_hashes_manuf_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_hashes_manuf_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_hashes_manuf_partition_digest
  // R[vendor_hashes_manuf_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_hashes_manuf_partition_digest_1 (
    .re     (vendor_hashes_manuf_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_hashes_manuf_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_hashes_manuf_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_hashes_prod_partition_digest
  // R[vendor_hashes_prod_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_hashes_prod_partition_digest_0 (
    .re     (vendor_hashes_prod_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_hashes_prod_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_hashes_prod_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_hashes_prod_partition_digest
  // R[vendor_hashes_prod_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_hashes_prod_partition_digest_1 (
    .re     (vendor_hashes_prod_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_hashes_prod_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_hashes_prod_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_revocations_prod_partition_digest
  // R[vendor_revocations_prod_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_revocations_prod_partition_digest_0 (
    .re     (vendor_revocations_prod_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_revocations_prod_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_revocations_prod_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_revocations_prod_partition_digest
  // R[vendor_revocations_prod_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_revocations_prod_partition_digest_1 (
    .re     (vendor_revocations_prod_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_revocations_prod_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_revocations_prod_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_secret_prod_partition_digest
  // R[vendor_secret_prod_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_secret_prod_partition_digest_0 (
    .re     (vendor_secret_prod_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_secret_prod_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_secret_prod_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_secret_prod_partition_digest
  // R[vendor_secret_prod_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_secret_prod_partition_digest_1 (
    .re     (vendor_secret_prod_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_secret_prod_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_secret_prod_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg vendor_non_secret_prod_partition_digest
  // R[vendor_non_secret_prod_partition_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_non_secret_prod_partition_digest_0 (
    .re     (vendor_non_secret_prod_partition_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_non_secret_prod_partition_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_non_secret_prod_partition_digest_0_qs)
  );


  // Subregister 1 of Multireg vendor_non_secret_prod_partition_digest
  // R[vendor_non_secret_prod_partition_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_vendor_non_secret_prod_partition_digest_1 (
    .re     (vendor_non_secret_prod_partition_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.vendor_non_secret_prod_partition_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (vendor_non_secret_prod_partition_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_0_digest
  // R[cptra_ss_lock_hek_prod_0_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_0_digest_0 (
    .re     (cptra_ss_lock_hek_prod_0_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_0_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_0_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_0_digest
  // R[cptra_ss_lock_hek_prod_0_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_0_digest_1 (
    .re     (cptra_ss_lock_hek_prod_0_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_0_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_0_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_1_digest
  // R[cptra_ss_lock_hek_prod_1_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_1_digest_0 (
    .re     (cptra_ss_lock_hek_prod_1_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_1_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_1_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_1_digest
  // R[cptra_ss_lock_hek_prod_1_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_1_digest_1 (
    .re     (cptra_ss_lock_hek_prod_1_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_1_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_1_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_2_digest
  // R[cptra_ss_lock_hek_prod_2_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_2_digest_0 (
    .re     (cptra_ss_lock_hek_prod_2_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_2_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_2_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_2_digest
  // R[cptra_ss_lock_hek_prod_2_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_2_digest_1 (
    .re     (cptra_ss_lock_hek_prod_2_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_2_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_2_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_3_digest
  // R[cptra_ss_lock_hek_prod_3_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_3_digest_0 (
    .re     (cptra_ss_lock_hek_prod_3_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_3_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_3_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_3_digest
  // R[cptra_ss_lock_hek_prod_3_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_3_digest_1 (
    .re     (cptra_ss_lock_hek_prod_3_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_3_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_3_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_4_digest
  // R[cptra_ss_lock_hek_prod_4_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_4_digest_0 (
    .re     (cptra_ss_lock_hek_prod_4_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_4_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_4_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_4_digest
  // R[cptra_ss_lock_hek_prod_4_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_4_digest_1 (
    .re     (cptra_ss_lock_hek_prod_4_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_4_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_4_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_5_digest
  // R[cptra_ss_lock_hek_prod_5_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_5_digest_0 (
    .re     (cptra_ss_lock_hek_prod_5_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_5_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_5_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_5_digest
  // R[cptra_ss_lock_hek_prod_5_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_5_digest_1 (
    .re     (cptra_ss_lock_hek_prod_5_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_5_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_5_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_6_digest
  // R[cptra_ss_lock_hek_prod_6_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_6_digest_0 (
    .re     (cptra_ss_lock_hek_prod_6_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_6_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_6_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_6_digest
  // R[cptra_ss_lock_hek_prod_6_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_6_digest_1 (
    .re     (cptra_ss_lock_hek_prod_6_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_6_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_6_digest_1_qs)
  );


  // Subregister 0 of Multireg cptra_ss_lock_hek_prod_7_digest
  // R[cptra_ss_lock_hek_prod_7_digest_0]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_7_digest_0 (
    .re     (cptra_ss_lock_hek_prod_7_digest_0_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_7_digest[0].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_7_digest_0_qs)
  );


  // Subregister 1 of Multireg cptra_ss_lock_hek_prod_7_digest
  // R[cptra_ss_lock_hek_prod_7_digest_1]: V(True)
  caliptra_prim_subreg_ext #(
    .DW    (32)
  ) u_cptra_ss_lock_hek_prod_7_digest_1 (
    .re     (cptra_ss_lock_hek_prod_7_digest_1_re),
    .we     (1'b0),
    .wd     ('0),
    .d      (hw2reg.cptra_ss_lock_hek_prod_7_digest[1].d),
    .qre    (),
    .qe     (),
    .q      (),
    .ds     (),
    .qs     (cptra_ss_lock_hek_prod_7_digest_1_qs)
  );



  logic [104:0] addr_hit;
  always_comb begin
    addr_hit = '0;
    addr_hit[  0] = (reg_addr == OTP_CTRL_INTR_STATE_OFFSET);
    addr_hit[  1] = (reg_addr == OTP_CTRL_INTR_ENABLE_OFFSET);
    addr_hit[  2] = (reg_addr == OTP_CTRL_INTR_TEST_OFFSET);
    addr_hit[  3] = (reg_addr == OTP_CTRL_ALERT_TEST_OFFSET);
    addr_hit[  4] = (reg_addr == OTP_CTRL_STATUS_OFFSET);
    addr_hit[  5] = (reg_addr == OTP_CTRL_ERR_CODE_0_OFFSET);
    addr_hit[  6] = (reg_addr == OTP_CTRL_ERR_CODE_1_OFFSET);
    addr_hit[  7] = (reg_addr == OTP_CTRL_ERR_CODE_2_OFFSET);
    addr_hit[  8] = (reg_addr == OTP_CTRL_ERR_CODE_3_OFFSET);
    addr_hit[  9] = (reg_addr == OTP_CTRL_ERR_CODE_4_OFFSET);
    addr_hit[ 10] = (reg_addr == OTP_CTRL_ERR_CODE_5_OFFSET);
    addr_hit[ 11] = (reg_addr == OTP_CTRL_ERR_CODE_6_OFFSET);
    addr_hit[ 12] = (reg_addr == OTP_CTRL_ERR_CODE_7_OFFSET);
    addr_hit[ 13] = (reg_addr == OTP_CTRL_ERR_CODE_8_OFFSET);
    addr_hit[ 14] = (reg_addr == OTP_CTRL_ERR_CODE_9_OFFSET);
    addr_hit[ 15] = (reg_addr == OTP_CTRL_ERR_CODE_10_OFFSET);
    addr_hit[ 16] = (reg_addr == OTP_CTRL_ERR_CODE_11_OFFSET);
    addr_hit[ 17] = (reg_addr == OTP_CTRL_ERR_CODE_12_OFFSET);
    addr_hit[ 18] = (reg_addr == OTP_CTRL_ERR_CODE_13_OFFSET);
    addr_hit[ 19] = (reg_addr == OTP_CTRL_ERR_CODE_14_OFFSET);
    addr_hit[ 20] = (reg_addr == OTP_CTRL_ERR_CODE_15_OFFSET);
    addr_hit[ 21] = (reg_addr == OTP_CTRL_ERR_CODE_16_OFFSET);
    addr_hit[ 22] = (reg_addr == OTP_CTRL_ERR_CODE_17_OFFSET);
    addr_hit[ 23] = (reg_addr == OTP_CTRL_ERR_CODE_18_OFFSET);
    addr_hit[ 24] = (reg_addr == OTP_CTRL_ERR_CODE_19_OFFSET);
    addr_hit[ 25] = (reg_addr == OTP_CTRL_ERR_CODE_20_OFFSET);
    addr_hit[ 26] = (reg_addr == OTP_CTRL_ERR_CODE_21_OFFSET);
    addr_hit[ 27] = (reg_addr == OTP_CTRL_ERR_CODE_22_OFFSET);
    addr_hit[ 28] = (reg_addr == OTP_CTRL_ERR_CODE_23_OFFSET);
    addr_hit[ 29] = (reg_addr == OTP_CTRL_ERR_CODE_24_OFFSET);
    addr_hit[ 30] = (reg_addr == OTP_CTRL_ERR_CODE_25_OFFSET);
    addr_hit[ 31] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET);
    addr_hit[ 32] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET);
    addr_hit[ 33] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET);
    addr_hit[ 34] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET);
    addr_hit[ 35] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET);
    addr_hit[ 36] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET);
    addr_hit[ 37] = (reg_addr == OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET);
    addr_hit[ 38] = (reg_addr == OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET);
    addr_hit[ 39] = (reg_addr == OTP_CTRL_CHECK_TRIGGER_OFFSET);
    addr_hit[ 40] = (reg_addr == OTP_CTRL_CHECK_REGWEN_OFFSET);
    addr_hit[ 41] = (reg_addr == OTP_CTRL_CHECK_TIMEOUT_OFFSET);
    addr_hit[ 42] = (reg_addr == OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET);
    addr_hit[ 43] = (reg_addr == OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET);
    addr_hit[ 44] = (reg_addr == OTP_CTRL_SW_MANUF_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 45] = (reg_addr == OTP_CTRL_SVN_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 46] = (reg_addr == OTP_CTRL_VENDOR_TEST_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 47] = (reg_addr == OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 48] = (reg_addr == OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 49] = (reg_addr == OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 50] = (reg_addr == OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_READ_LOCK_OFFSET);
    addr_hit[ 51] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_READ_LOCK_OFFSET);
    addr_hit[ 52] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_READ_LOCK_OFFSET);
    addr_hit[ 53] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_READ_LOCK_OFFSET);
    addr_hit[ 54] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_READ_LOCK_OFFSET);
    addr_hit[ 55] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_READ_LOCK_OFFSET);
    addr_hit[ 56] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_READ_LOCK_OFFSET);
    addr_hit[ 57] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_READ_LOCK_OFFSET);
    addr_hit[ 58] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_READ_LOCK_OFFSET);
    addr_hit[ 59] = (reg_addr == OTP_CTRL_VENDOR_PK_HASH_VOLATILE_LOCK_OFFSET);
    addr_hit[ 60] = (reg_addr == OTP_CTRL_RATCHET_SEED_VOLATILE_LOCK_OFFSET);
    addr_hit[ 61] = (reg_addr == OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 62] = (reg_addr == OTP_CTRL_SW_TEST_UNLOCK_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 63] = (reg_addr == OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 64] = (reg_addr == OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 65] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_0_OFFSET);
    addr_hit[ 66] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_1_OFFSET);
    addr_hit[ 67] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_0_OFFSET);
    addr_hit[ 68] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_1_OFFSET);
    addr_hit[ 69] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_0_OFFSET);
    addr_hit[ 70] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_1_OFFSET);
    addr_hit[ 71] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_0_OFFSET);
    addr_hit[ 72] = (reg_addr == OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_1_OFFSET);
    addr_hit[ 73] = (reg_addr == OTP_CTRL_SW_MANUF_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 74] = (reg_addr == OTP_CTRL_SW_MANUF_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 75] = (reg_addr == OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 76] = (reg_addr == OTP_CTRL_SECRET_LC_TRANSITION_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 77] = (reg_addr == OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 78] = (reg_addr == OTP_CTRL_VENDOR_TEST_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 79] = (reg_addr == OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 80] = (reg_addr == OTP_CTRL_VENDOR_HASHES_MANUF_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 81] = (reg_addr == OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 82] = (reg_addr == OTP_CTRL_VENDOR_HASHES_PROD_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 83] = (reg_addr == OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 84] = (reg_addr == OTP_CTRL_VENDOR_REVOCATIONS_PROD_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 85] = (reg_addr == OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 86] = (reg_addr == OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 87] = (reg_addr == OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_0_OFFSET);
    addr_hit[ 88] = (reg_addr == OTP_CTRL_VENDOR_NON_SECRET_PROD_PARTITION_DIGEST_1_OFFSET);
    addr_hit[ 89] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_0_OFFSET);
    addr_hit[ 90] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_0_DIGEST_1_OFFSET);
    addr_hit[ 91] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_0_OFFSET);
    addr_hit[ 92] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_1_DIGEST_1_OFFSET);
    addr_hit[ 93] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_0_OFFSET);
    addr_hit[ 94] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_2_DIGEST_1_OFFSET);
    addr_hit[ 95] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_0_OFFSET);
    addr_hit[ 96] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_3_DIGEST_1_OFFSET);
    addr_hit[ 97] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_0_OFFSET);
    addr_hit[ 98] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_4_DIGEST_1_OFFSET);
    addr_hit[ 99] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_0_OFFSET);
    addr_hit[100] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_5_DIGEST_1_OFFSET);
    addr_hit[101] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_0_OFFSET);
    addr_hit[102] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_6_DIGEST_1_OFFSET);
    addr_hit[103] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_0_OFFSET);
    addr_hit[104] = (reg_addr == OTP_CTRL_CPTRA_SS_LOCK_HEK_PROD_7_DIGEST_1_OFFSET);
  end

  assign addrmiss = (reg_re || reg_we) ? ~|addr_hit : 1'b0 ;

  // Check sub-word write is permitted
  always_comb begin
    wr_err = (reg_we &
              ((addr_hit[  0] & (|(OTP_CTRL_CORE_PERMIT[  0] & ~reg_be))) |
               (addr_hit[  1] & (|(OTP_CTRL_CORE_PERMIT[  1] & ~reg_be))) |
               (addr_hit[  2] & (|(OTP_CTRL_CORE_PERMIT[  2] & ~reg_be))) |
               (addr_hit[  3] & (|(OTP_CTRL_CORE_PERMIT[  3] & ~reg_be))) |
               (addr_hit[  4] & (|(OTP_CTRL_CORE_PERMIT[  4] & ~reg_be))) |
               (addr_hit[  5] & (|(OTP_CTRL_CORE_PERMIT[  5] & ~reg_be))) |
               (addr_hit[  6] & (|(OTP_CTRL_CORE_PERMIT[  6] & ~reg_be))) |
               (addr_hit[  7] & (|(OTP_CTRL_CORE_PERMIT[  7] & ~reg_be))) |
               (addr_hit[  8] & (|(OTP_CTRL_CORE_PERMIT[  8] & ~reg_be))) |
               (addr_hit[  9] & (|(OTP_CTRL_CORE_PERMIT[  9] & ~reg_be))) |
               (addr_hit[ 10] & (|(OTP_CTRL_CORE_PERMIT[ 10] & ~reg_be))) |
               (addr_hit[ 11] & (|(OTP_CTRL_CORE_PERMIT[ 11] & ~reg_be))) |
               (addr_hit[ 12] & (|(OTP_CTRL_CORE_PERMIT[ 12] & ~reg_be))) |
               (addr_hit[ 13] & (|(OTP_CTRL_CORE_PERMIT[ 13] & ~reg_be))) |
               (addr_hit[ 14] & (|(OTP_CTRL_CORE_PERMIT[ 14] & ~reg_be))) |
               (addr_hit[ 15] & (|(OTP_CTRL_CORE_PERMIT[ 15] & ~reg_be))) |
               (addr_hit[ 16] & (|(OTP_CTRL_CORE_PERMIT[ 16] & ~reg_be))) |
               (addr_hit[ 17] & (|(OTP_CTRL_CORE_PERMIT[ 17] & ~reg_be))) |
               (addr_hit[ 18] & (|(OTP_CTRL_CORE_PERMIT[ 18] & ~reg_be))) |
               (addr_hit[ 19] & (|(OTP_CTRL_CORE_PERMIT[ 19] & ~reg_be))) |
               (addr_hit[ 20] & (|(OTP_CTRL_CORE_PERMIT[ 20] & ~reg_be))) |
               (addr_hit[ 21] & (|(OTP_CTRL_CORE_PERMIT[ 21] & ~reg_be))) |
               (addr_hit[ 22] & (|(OTP_CTRL_CORE_PERMIT[ 22] & ~reg_be))) |
               (addr_hit[ 23] & (|(OTP_CTRL_CORE_PERMIT[ 23] & ~reg_be))) |
               (addr_hit[ 24] & (|(OTP_CTRL_CORE_PERMIT[ 24] & ~reg_be))) |
               (addr_hit[ 25] & (|(OTP_CTRL_CORE_PERMIT[ 25] & ~reg_be))) |
               (addr_hit[ 26] & (|(OTP_CTRL_CORE_PERMIT[ 26] & ~reg_be))) |
               (addr_hit[ 27] & (|(OTP_CTRL_CORE_PERMIT[ 27] & ~reg_be))) |
               (addr_hit[ 28] & (|(OTP_CTRL_CORE_PERMIT[ 28] & ~reg_be))) |
               (addr_hit[ 29] & (|(OTP_CTRL_CORE_PERMIT[ 29] & ~reg_be))) |
               (addr_hit[ 30] & (|(OTP_CTRL_CORE_PERMIT[ 30] & ~reg_be))) |
               (addr_hit[ 31] & (|(OTP_CTRL_CORE_PERMIT[ 31] & ~reg_be))) |
               (addr_hit[ 32] & (|(OTP_CTRL_CORE_PERMIT[ 32] & ~reg_be))) |
               (addr_hit[ 33] & (|(OTP_CTRL_CORE_PERMIT[ 33] & ~reg_be))) |
               (addr_hit[ 34] & (|(OTP_CTRL_CORE_PERMIT[ 34] & ~reg_be))) |
               (addr_hit[ 35] & (|(OTP_CTRL_CORE_PERMIT[ 35] & ~reg_be))) |
               (addr_hit[ 36] & (|(OTP_CTRL_CORE_PERMIT[ 36] & ~reg_be))) |
               (addr_hit[ 37] & (|(OTP_CTRL_CORE_PERMIT[ 37] & ~reg_be))) |
               (addr_hit[ 38] & (|(OTP_CTRL_CORE_PERMIT[ 38] & ~reg_be))) |
               (addr_hit[ 39] & (|(OTP_CTRL_CORE_PERMIT[ 39] & ~reg_be))) |
               (addr_hit[ 40] & (|(OTP_CTRL_CORE_PERMIT[ 40] & ~reg_be))) |
               (addr_hit[ 41] & (|(OTP_CTRL_CORE_PERMIT[ 41] & ~reg_be))) |
               (addr_hit[ 42] & (|(OTP_CTRL_CORE_PERMIT[ 42] & ~reg_be))) |
               (addr_hit[ 43] & (|(OTP_CTRL_CORE_PERMIT[ 43] & ~reg_be))) |
               (addr_hit[ 44] & (|(OTP_CTRL_CORE_PERMIT[ 44] & ~reg_be))) |
               (addr_hit[ 45] & (|(OTP_CTRL_CORE_PERMIT[ 45] & ~reg_be))) |
               (addr_hit[ 46] & (|(OTP_CTRL_CORE_PERMIT[ 46] & ~reg_be))) |
               (addr_hit[ 47] & (|(OTP_CTRL_CORE_PERMIT[ 47] & ~reg_be))) |
               (addr_hit[ 48] & (|(OTP_CTRL_CORE_PERMIT[ 48] & ~reg_be))) |
               (addr_hit[ 49] & (|(OTP_CTRL_CORE_PERMIT[ 49] & ~reg_be))) |
               (addr_hit[ 50] & (|(OTP_CTRL_CORE_PERMIT[ 50] & ~reg_be))) |
               (addr_hit[ 51] & (|(OTP_CTRL_CORE_PERMIT[ 51] & ~reg_be))) |
               (addr_hit[ 52] & (|(OTP_CTRL_CORE_PERMIT[ 52] & ~reg_be))) |
               (addr_hit[ 53] & (|(OTP_CTRL_CORE_PERMIT[ 53] & ~reg_be))) |
               (addr_hit[ 54] & (|(OTP_CTRL_CORE_PERMIT[ 54] & ~reg_be))) |
               (addr_hit[ 55] & (|(OTP_CTRL_CORE_PERMIT[ 55] & ~reg_be))) |
               (addr_hit[ 56] & (|(OTP_CTRL_CORE_PERMIT[ 56] & ~reg_be))) |
               (addr_hit[ 57] & (|(OTP_CTRL_CORE_PERMIT[ 57] & ~reg_be))) |
               (addr_hit[ 58] & (|(OTP_CTRL_CORE_PERMIT[ 58] & ~reg_be))) |
               (addr_hit[ 59] & (|(OTP_CTRL_CORE_PERMIT[ 59] & ~reg_be))) |
               (addr_hit[ 60] & (|(OTP_CTRL_CORE_PERMIT[ 60] & ~reg_be))) |
               (addr_hit[ 61] & (|(OTP_CTRL_CORE_PERMIT[ 61] & ~reg_be))) |
               (addr_hit[ 62] & (|(OTP_CTRL_CORE_PERMIT[ 62] & ~reg_be))) |
               (addr_hit[ 63] & (|(OTP_CTRL_CORE_PERMIT[ 63] & ~reg_be))) |
               (addr_hit[ 64] & (|(OTP_CTRL_CORE_PERMIT[ 64] & ~reg_be))) |
               (addr_hit[ 65] & (|(OTP_CTRL_CORE_PERMIT[ 65] & ~reg_be))) |
               (addr_hit[ 66] & (|(OTP_CTRL_CORE_PERMIT[ 66] & ~reg_be))) |
               (addr_hit[ 67] & (|(OTP_CTRL_CORE_PERMIT[ 67] & ~reg_be))) |
               (addr_hit[ 68] & (|(OTP_CTRL_CORE_PERMIT[ 68] & ~reg_be))) |
               (addr_hit[ 69] & (|(OTP_CTRL_CORE_PERMIT[ 69] & ~reg_be))) |
               (addr_hit[ 70] & (|(OTP_CTRL_CORE_PERMIT[ 70] & ~reg_be))) |
               (addr_hit[ 71] & (|(OTP_CTRL_CORE_PERMIT[ 71] & ~reg_be))) |
               (addr_hit[ 72] & (|(OTP_CTRL_CORE_PERMIT[ 72] & ~reg_be))) |
               (addr_hit[ 73] & (|(OTP_CTRL_CORE_PERMIT[ 73] & ~reg_be))) |
               (addr_hit[ 74] & (|(OTP_CTRL_CORE_PERMIT[ 74] & ~reg_be))) |
               (addr_hit[ 75] & (|(OTP_CTRL_CORE_PERMIT[ 75] & ~reg_be))) |
               (addr_hit[ 76] & (|(OTP_CTRL_CORE_PERMIT[ 76] & ~reg_be))) |
               (addr_hit[ 77] & (|(OTP_CTRL_CORE_PERMIT[ 77] & ~reg_be))) |
               (addr_hit[ 78] & (|(OTP_CTRL_CORE_PERMIT[ 78] & ~reg_be))) |
               (addr_hit[ 79] & (|(OTP_CTRL_CORE_PERMIT[ 79] & ~reg_be))) |
               (addr_hit[ 80] & (|(OTP_CTRL_CORE_PERMIT[ 80] & ~reg_be))) |
               (addr_hit[ 81] & (|(OTP_CTRL_CORE_PERMIT[ 81] & ~reg_be))) |
               (addr_hit[ 82] & (|(OTP_CTRL_CORE_PERMIT[ 82] & ~reg_be))) |
               (addr_hit[ 83] & (|(OTP_CTRL_CORE_PERMIT[ 83] & ~reg_be))) |
               (addr_hit[ 84] & (|(OTP_CTRL_CORE_PERMIT[ 84] & ~reg_be))) |
               (addr_hit[ 85] & (|(OTP_CTRL_CORE_PERMIT[ 85] & ~reg_be))) |
               (addr_hit[ 86] & (|(OTP_CTRL_CORE_PERMIT[ 86] & ~reg_be))) |
               (addr_hit[ 87] & (|(OTP_CTRL_CORE_PERMIT[ 87] & ~reg_be))) |
               (addr_hit[ 88] & (|(OTP_CTRL_CORE_PERMIT[ 88] & ~reg_be))) |
               (addr_hit[ 89] & (|(OTP_CTRL_CORE_PERMIT[ 89] & ~reg_be))) |
               (addr_hit[ 90] & (|(OTP_CTRL_CORE_PERMIT[ 90] & ~reg_be))) |
               (addr_hit[ 91] & (|(OTP_CTRL_CORE_PERMIT[ 91] & ~reg_be))) |
               (addr_hit[ 92] & (|(OTP_CTRL_CORE_PERMIT[ 92] & ~reg_be))) |
               (addr_hit[ 93] & (|(OTP_CTRL_CORE_PERMIT[ 93] & ~reg_be))) |
               (addr_hit[ 94] & (|(OTP_CTRL_CORE_PERMIT[ 94] & ~reg_be))) |
               (addr_hit[ 95] & (|(OTP_CTRL_CORE_PERMIT[ 95] & ~reg_be))) |
               (addr_hit[ 96] & (|(OTP_CTRL_CORE_PERMIT[ 96] & ~reg_be))) |
               (addr_hit[ 97] & (|(OTP_CTRL_CORE_PERMIT[ 97] & ~reg_be))) |
               (addr_hit[ 98] & (|(OTP_CTRL_CORE_PERMIT[ 98] & ~reg_be))) |
               (addr_hit[ 99] & (|(OTP_CTRL_CORE_PERMIT[ 99] & ~reg_be))) |
               (addr_hit[100] & (|(OTP_CTRL_CORE_PERMIT[100] & ~reg_be))) |
               (addr_hit[101] & (|(OTP_CTRL_CORE_PERMIT[101] & ~reg_be))) |
               (addr_hit[102] & (|(OTP_CTRL_CORE_PERMIT[102] & ~reg_be))) |
               (addr_hit[103] & (|(OTP_CTRL_CORE_PERMIT[103] & ~reg_be))) |
               (addr_hit[104] & (|(OTP_CTRL_CORE_PERMIT[104] & ~reg_be)))));
  end

  // Generate write-enables
  assign intr_state_we = addr_hit[0] & reg_we & !reg_error;

  assign intr_state_otp_operation_done_wd = reg_wdata[0];

  assign intr_state_otp_error_wd = reg_wdata[1];
  assign intr_enable_we = addr_hit[1] & reg_we & !reg_error;

  assign intr_enable_otp_operation_done_wd = reg_wdata[0];

  assign intr_enable_otp_error_wd = reg_wdata[1];
  assign intr_test_we = addr_hit[2] & reg_we & !reg_error;

  assign intr_test_otp_operation_done_wd = reg_wdata[0];

  assign intr_test_otp_error_wd = reg_wdata[1];
  assign alert_test_we = addr_hit[3] & reg_we & !reg_error;

  assign alert_test_fatal_macro_error_wd = reg_wdata[0];

  assign alert_test_fatal_check_error_wd = reg_wdata[1];

  assign alert_test_fatal_bus_integ_error_wd = reg_wdata[2];

  assign alert_test_fatal_prim_otp_alert_wd = reg_wdata[3];

  assign alert_test_recov_prim_otp_alert_wd = reg_wdata[4];
  assign status_re = addr_hit[4] & reg_re & !reg_error;
  assign err_code_0_re = addr_hit[5] & reg_re & !reg_error;
  assign err_code_1_re = addr_hit[6] & reg_re & !reg_error;
  assign err_code_2_re = addr_hit[7] & reg_re & !reg_error;
  assign err_code_3_re = addr_hit[8] & reg_re & !reg_error;
  assign err_code_4_re = addr_hit[9] & reg_re & !reg_error;
  assign err_code_5_re = addr_hit[10] & reg_re & !reg_error;
  assign err_code_6_re = addr_hit[11] & reg_re & !reg_error;
  assign err_code_7_re = addr_hit[12] & reg_re & !reg_error;
  assign err_code_8_re = addr_hit[13] & reg_re & !reg_error;
  assign err_code_9_re = addr_hit[14] & reg_re & !reg_error;
  assign err_code_10_re = addr_hit[15] & reg_re & !reg_error;
  assign err_code_11_re = addr_hit[16] & reg_re & !reg_error;
  assign err_code_12_re = addr_hit[17] & reg_re & !reg_error;
  assign err_code_13_re = addr_hit[18] & reg_re & !reg_error;
  assign err_code_14_re = addr_hit[19] & reg_re & !reg_error;
  assign err_code_15_re = addr_hit[20] & reg_re & !reg_error;
  assign err_code_16_re = addr_hit[21] & reg_re & !reg_error;
  assign err_code_17_re = addr_hit[22] & reg_re & !reg_error;
  assign err_code_18_re = addr_hit[23] & reg_re & !reg_error;
  assign err_code_19_re = addr_hit[24] & reg_re & !reg_error;
  assign err_code_20_re = addr_hit[25] & reg_re & !reg_error;
  assign err_code_21_re = addr_hit[26] & reg_re & !reg_error;
  assign err_code_22_re = addr_hit[27] & reg_re & !reg_error;
  assign err_code_23_re = addr_hit[28] & reg_re & !reg_error;
  assign err_code_24_re = addr_hit[29] & reg_re & !reg_error;
  assign err_code_25_re = addr_hit[30] & reg_re & !reg_error;
  assign direct_access_regwen_re = addr_hit[31] & reg_re & !reg_error;
  assign direct_access_regwen_we = addr_hit[31] & reg_we & !reg_error;

  assign direct_access_regwen_wd = reg_wdata[0];
  assign direct_access_cmd_we = addr_hit[32] & reg_we & !reg_error;

  assign direct_access_cmd_rd_wd = reg_wdata[0];

  assign direct_access_cmd_wr_wd = reg_wdata[1];

  assign direct_access_cmd_digest_wd = reg_wdata[2];

  assign direct_access_cmd_zeroize_wd = reg_wdata[3];
  assign direct_access_address_we = addr_hit[33] & reg_we & !reg_error;

  assign direct_access_address_wd = reg_wdata[11:0];
  assign direct_access_wdata_0_we = addr_hit[34] & reg_we & !reg_error;

  assign direct_access_wdata_0_wd = reg_wdata[31:0];
  assign direct_access_wdata_1_we = addr_hit[35] & reg_we & !reg_error;

  assign direct_access_wdata_1_wd = reg_wdata[31:0];
  assign direct_access_rdata_0_re = addr_hit[36] & reg_re & !reg_error;
  assign direct_access_rdata_1_re = addr_hit[37] & reg_re & !reg_error;
  assign check_trigger_regwen_we = addr_hit[38] & reg_we & !reg_error;

  assign check_trigger_regwen_wd = reg_wdata[0];
  assign check_trigger_we = addr_hit[39] & reg_we & !reg_error;

  assign check_trigger_integrity_wd = reg_wdata[0];

  assign check_trigger_consistency_wd = reg_wdata[1];
  assign check_regwen_we = addr_hit[40] & reg_we & !reg_error;

  assign check_regwen_wd = reg_wdata[0];
  assign check_timeout_we = addr_hit[41] & reg_we & !reg_error;

  assign check_timeout_wd = reg_wdata[31:0];
  assign integrity_check_period_we = addr_hit[42] & reg_we & !reg_error;

  assign integrity_check_period_wd = reg_wdata[31:0];
  assign consistency_check_period_we = addr_hit[43] & reg_we & !reg_error;

  assign consistency_check_period_wd = reg_wdata[31:0];
  assign sw_manuf_partition_read_lock_we = addr_hit[44] & reg_we & !reg_error;

  assign sw_manuf_partition_read_lock_wd = reg_wdata[0];
  assign svn_partition_read_lock_we = addr_hit[45] & reg_we & !reg_error;

  assign svn_partition_read_lock_wd = reg_wdata[0];
  assign vendor_test_partition_read_lock_we = addr_hit[46] & reg_we & !reg_error;

  assign vendor_test_partition_read_lock_wd = reg_wdata[0];
  assign vendor_hashes_manuf_partition_read_lock_we = addr_hit[47] & reg_we & !reg_error;

  assign vendor_hashes_manuf_partition_read_lock_wd = reg_wdata[0];
  assign vendor_hashes_prod_partition_read_lock_we = addr_hit[48] & reg_we & !reg_error;

  assign vendor_hashes_prod_partition_read_lock_wd = reg_wdata[0];
  assign vendor_revocations_prod_partition_read_lock_we = addr_hit[49] & reg_we & !reg_error;

  assign vendor_revocations_prod_partition_read_lock_wd = reg_wdata[0];
  assign vendor_non_secret_prod_partition_read_lock_we = addr_hit[50] & reg_we & !reg_error;

  assign vendor_non_secret_prod_partition_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_0_read_lock_we = addr_hit[51] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_0_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_1_read_lock_we = addr_hit[52] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_1_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_2_read_lock_we = addr_hit[53] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_2_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_3_read_lock_we = addr_hit[54] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_3_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_4_read_lock_we = addr_hit[55] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_4_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_5_read_lock_we = addr_hit[56] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_5_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_6_read_lock_we = addr_hit[57] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_6_read_lock_wd = reg_wdata[0];
  assign cptra_ss_lock_hek_prod_7_read_lock_we = addr_hit[58] & reg_we & !reg_error;

  assign cptra_ss_lock_hek_prod_7_read_lock_wd = reg_wdata[0];
  assign vendor_pk_hash_volatile_lock_we = addr_hit[59] & reg_we & !reg_error;

  assign vendor_pk_hash_volatile_lock_wd = reg_wdata[31:0];
  assign ratchet_seed_volatile_lock_we = addr_hit[60] & reg_we & !reg_error;

  assign ratchet_seed_volatile_lock_wd = reg_wdata[31:0];
  assign sw_test_unlock_partition_digest_0_re = addr_hit[61] & reg_re & !reg_error;
  assign sw_test_unlock_partition_digest_1_re = addr_hit[62] & reg_re & !reg_error;
  assign secret_manuf_partition_digest_0_re = addr_hit[63] & reg_re & !reg_error;
  assign secret_manuf_partition_digest_1_re = addr_hit[64] & reg_re & !reg_error;
  assign secret_prod_partition_0_digest_0_re = addr_hit[65] & reg_re & !reg_error;
  assign secret_prod_partition_0_digest_1_re = addr_hit[66] & reg_re & !reg_error;
  assign secret_prod_partition_1_digest_0_re = addr_hit[67] & reg_re & !reg_error;
  assign secret_prod_partition_1_digest_1_re = addr_hit[68] & reg_re & !reg_error;
  assign secret_prod_partition_2_digest_0_re = addr_hit[69] & reg_re & !reg_error;
  assign secret_prod_partition_2_digest_1_re = addr_hit[70] & reg_re & !reg_error;
  assign secret_prod_partition_3_digest_0_re = addr_hit[71] & reg_re & !reg_error;
  assign secret_prod_partition_3_digest_1_re = addr_hit[72] & reg_re & !reg_error;
  assign sw_manuf_partition_digest_0_re = addr_hit[73] & reg_re & !reg_error;
  assign sw_manuf_partition_digest_1_re = addr_hit[74] & reg_re & !reg_error;
  assign secret_lc_transition_partition_digest_0_re = addr_hit[75] & reg_re & !reg_error;
  assign secret_lc_transition_partition_digest_1_re = addr_hit[76] & reg_re & !reg_error;
  assign vendor_test_partition_digest_0_re = addr_hit[77] & reg_re & !reg_error;
  assign vendor_test_partition_digest_1_re = addr_hit[78] & reg_re & !reg_error;
  assign vendor_hashes_manuf_partition_digest_0_re = addr_hit[79] & reg_re & !reg_error;
  assign vendor_hashes_manuf_partition_digest_1_re = addr_hit[80] & reg_re & !reg_error;
  assign vendor_hashes_prod_partition_digest_0_re = addr_hit[81] & reg_re & !reg_error;
  assign vendor_hashes_prod_partition_digest_1_re = addr_hit[82] & reg_re & !reg_error;
  assign vendor_revocations_prod_partition_digest_0_re = addr_hit[83] & reg_re & !reg_error;
  assign vendor_revocations_prod_partition_digest_1_re = addr_hit[84] & reg_re & !reg_error;
  assign vendor_secret_prod_partition_digest_0_re = addr_hit[85] & reg_re & !reg_error;
  assign vendor_secret_prod_partition_digest_1_re = addr_hit[86] & reg_re & !reg_error;
  assign vendor_non_secret_prod_partition_digest_0_re = addr_hit[87] & reg_re & !reg_error;
  assign vendor_non_secret_prod_partition_digest_1_re = addr_hit[88] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_0_digest_0_re = addr_hit[89] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_0_digest_1_re = addr_hit[90] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_1_digest_0_re = addr_hit[91] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_1_digest_1_re = addr_hit[92] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_2_digest_0_re = addr_hit[93] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_2_digest_1_re = addr_hit[94] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_3_digest_0_re = addr_hit[95] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_3_digest_1_re = addr_hit[96] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_4_digest_0_re = addr_hit[97] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_4_digest_1_re = addr_hit[98] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_5_digest_0_re = addr_hit[99] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_5_digest_1_re = addr_hit[100] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_6_digest_0_re = addr_hit[101] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_6_digest_1_re = addr_hit[102] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_7_digest_0_re = addr_hit[103] & reg_re & !reg_error;
  assign cptra_ss_lock_hek_prod_7_digest_1_re = addr_hit[104] & reg_re & !reg_error;

  // Assign write-enables to checker logic vector.
  always_comb begin
    reg_we_check = '0;
    reg_we_check[0] = intr_state_we;
    reg_we_check[1] = intr_enable_we;
    reg_we_check[2] = intr_test_we;
    reg_we_check[3] = alert_test_we;
    reg_we_check[4] = 1'b0;
    reg_we_check[5] = 1'b0;
    reg_we_check[6] = 1'b0;
    reg_we_check[7] = 1'b0;
    reg_we_check[8] = 1'b0;
    reg_we_check[9] = 1'b0;
    reg_we_check[10] = 1'b0;
    reg_we_check[11] = 1'b0;
    reg_we_check[12] = 1'b0;
    reg_we_check[13] = 1'b0;
    reg_we_check[14] = 1'b0;
    reg_we_check[15] = 1'b0;
    reg_we_check[16] = 1'b0;
    reg_we_check[17] = 1'b0;
    reg_we_check[18] = 1'b0;
    reg_we_check[19] = 1'b0;
    reg_we_check[20] = 1'b0;
    reg_we_check[21] = 1'b0;
    reg_we_check[22] = 1'b0;
    reg_we_check[23] = 1'b0;
    reg_we_check[24] = 1'b0;
    reg_we_check[25] = 1'b0;
    reg_we_check[26] = 1'b0;
    reg_we_check[27] = 1'b0;
    reg_we_check[28] = 1'b0;
    reg_we_check[29] = 1'b0;
    reg_we_check[30] = 1'b0;
    reg_we_check[31] = direct_access_regwen_we;
    reg_we_check[32] = direct_access_cmd_gated_we;
    reg_we_check[33] = direct_access_address_gated_we;
    reg_we_check[34] = direct_access_wdata_0_gated_we;
    reg_we_check[35] = direct_access_wdata_1_gated_we;
    reg_we_check[36] = 1'b0;
    reg_we_check[37] = 1'b0;
    reg_we_check[38] = check_trigger_regwen_we;
    reg_we_check[39] = check_trigger_gated_we;
    reg_we_check[40] = check_regwen_we;
    reg_we_check[41] = check_timeout_gated_we;
    reg_we_check[42] = integrity_check_period_gated_we;
    reg_we_check[43] = consistency_check_period_gated_we;
    reg_we_check[44] = sw_manuf_partition_read_lock_gated_we;
    reg_we_check[45] = svn_partition_read_lock_gated_we;
    reg_we_check[46] = vendor_test_partition_read_lock_gated_we;
    reg_we_check[47] = vendor_hashes_manuf_partition_read_lock_gated_we;
    reg_we_check[48] = vendor_hashes_prod_partition_read_lock_gated_we;
    reg_we_check[49] = vendor_revocations_prod_partition_read_lock_gated_we;
    reg_we_check[50] = vendor_non_secret_prod_partition_read_lock_gated_we;
    reg_we_check[51] = cptra_ss_lock_hek_prod_0_read_lock_gated_we;
    reg_we_check[52] = cptra_ss_lock_hek_prod_1_read_lock_gated_we;
    reg_we_check[53] = cptra_ss_lock_hek_prod_2_read_lock_gated_we;
    reg_we_check[54] = cptra_ss_lock_hek_prod_3_read_lock_gated_we;
    reg_we_check[55] = cptra_ss_lock_hek_prod_4_read_lock_gated_we;
    reg_we_check[56] = cptra_ss_lock_hek_prod_5_read_lock_gated_we;
    reg_we_check[57] = cptra_ss_lock_hek_prod_6_read_lock_gated_we;
    reg_we_check[58] = cptra_ss_lock_hek_prod_7_read_lock_gated_we;
    reg_we_check[59] = vendor_pk_hash_volatile_lock_we;
    reg_we_check[60] = ratchet_seed_volatile_lock_we;
    reg_we_check[61] = 1'b0;
    reg_we_check[62] = 1'b0;
    reg_we_check[63] = 1'b0;
    reg_we_check[64] = 1'b0;
    reg_we_check[65] = 1'b0;
    reg_we_check[66] = 1'b0;
    reg_we_check[67] = 1'b0;
    reg_we_check[68] = 1'b0;
    reg_we_check[69] = 1'b0;
    reg_we_check[70] = 1'b0;
    reg_we_check[71] = 1'b0;
    reg_we_check[72] = 1'b0;
    reg_we_check[73] = 1'b0;
    reg_we_check[74] = 1'b0;
    reg_we_check[75] = 1'b0;
    reg_we_check[76] = 1'b0;
    reg_we_check[77] = 1'b0;
    reg_we_check[78] = 1'b0;
    reg_we_check[79] = 1'b0;
    reg_we_check[80] = 1'b0;
    reg_we_check[81] = 1'b0;
    reg_we_check[82] = 1'b0;
    reg_we_check[83] = 1'b0;
    reg_we_check[84] = 1'b0;
    reg_we_check[85] = 1'b0;
    reg_we_check[86] = 1'b0;
    reg_we_check[87] = 1'b0;
    reg_we_check[88] = 1'b0;
    reg_we_check[89] = 1'b0;
    reg_we_check[90] = 1'b0;
    reg_we_check[91] = 1'b0;
    reg_we_check[92] = 1'b0;
    reg_we_check[93] = 1'b0;
    reg_we_check[94] = 1'b0;
    reg_we_check[95] = 1'b0;
    reg_we_check[96] = 1'b0;
    reg_we_check[97] = 1'b0;
    reg_we_check[98] = 1'b0;
    reg_we_check[99] = 1'b0;
    reg_we_check[100] = 1'b0;
    reg_we_check[101] = 1'b0;
    reg_we_check[102] = 1'b0;
    reg_we_check[103] = 1'b0;
    reg_we_check[104] = 1'b0;
  end

  // Read data return
  always_comb begin
    reg_rdata_next = '0;
    unique case (1'b1)
      addr_hit[0]: begin
        reg_rdata_next[0] = intr_state_otp_operation_done_qs;
        reg_rdata_next[1] = intr_state_otp_error_qs;
      end

      addr_hit[1]: begin
        reg_rdata_next[0] = intr_enable_otp_operation_done_qs;
        reg_rdata_next[1] = intr_enable_otp_error_qs;
      end

      addr_hit[2]: begin
        reg_rdata_next[0] = '0;
        reg_rdata_next[1] = '0;
      end

      addr_hit[3]: begin
        reg_rdata_next[0] = '0;
        reg_rdata_next[1] = '0;
        reg_rdata_next[2] = '0;
        reg_rdata_next[3] = '0;
        reg_rdata_next[4] = '0;
      end

      addr_hit[4]: begin
        reg_rdata_next[0] = status_sw_test_unlock_partition_error_qs;
        reg_rdata_next[1] = status_secret_manuf_partition_error_qs;
        reg_rdata_next[2] = status_secret_prod_partition_0_error_qs;
        reg_rdata_next[3] = status_secret_prod_partition_1_error_qs;
        reg_rdata_next[4] = status_secret_prod_partition_2_error_qs;
        reg_rdata_next[5] = status_secret_prod_partition_3_error_qs;
        reg_rdata_next[6] = status_sw_manuf_partition_error_qs;
        reg_rdata_next[7] = status_secret_lc_transition_partition_error_qs;
        reg_rdata_next[8] = status_svn_partition_error_qs;
        reg_rdata_next[9] = status_vendor_test_partition_error_qs;
        reg_rdata_next[10] = status_vendor_hashes_manuf_partition_error_qs;
        reg_rdata_next[11] = status_vendor_hashes_prod_partition_error_qs;
        reg_rdata_next[12] = status_vendor_revocations_prod_partition_error_qs;
        reg_rdata_next[13] = status_vendor_secret_prod_partition_error_qs;
        reg_rdata_next[14] = status_vendor_non_secret_prod_partition_error_qs;
        reg_rdata_next[15] = status_cptra_ss_lock_hek_prod_0_error_qs;
        reg_rdata_next[16] = status_cptra_ss_lock_hek_prod_1_error_qs;
        reg_rdata_next[17] = status_cptra_ss_lock_hek_prod_2_error_qs;
        reg_rdata_next[18] = status_cptra_ss_lock_hek_prod_3_error_qs;
        reg_rdata_next[19] = status_cptra_ss_lock_hek_prod_4_error_qs;
        reg_rdata_next[20] = status_cptra_ss_lock_hek_prod_5_error_qs;
        reg_rdata_next[21] = status_cptra_ss_lock_hek_prod_6_error_qs;
        reg_rdata_next[22] = status_cptra_ss_lock_hek_prod_7_error_qs;
        reg_rdata_next[23] = status_life_cycle_error_qs;
        reg_rdata_next[24] = status_dai_error_qs;
        reg_rdata_next[25] = status_lci_error_qs;
        reg_rdata_next[26] = status_timeout_error_qs;
        reg_rdata_next[27] = status_lfsr_fsm_error_qs;
        reg_rdata_next[28] = status_scrambling_fsm_error_qs;
        reg_rdata_next[29] = status_bus_integ_error_qs;
        reg_rdata_next[30] = status_dai_idle_qs;
        reg_rdata_next[31] = status_check_pending_qs;
      end

      addr_hit[5]: begin
        reg_rdata_next[2:0] = err_code_0_qs;
      end

      addr_hit[6]: begin
        reg_rdata_next[2:0] = err_code_1_qs;
      end

      addr_hit[7]: begin
        reg_rdata_next[2:0] = err_code_2_qs;
      end

      addr_hit[8]: begin
        reg_rdata_next[2:0] = err_code_3_qs;
      end

      addr_hit[9]: begin
        reg_rdata_next[2:0] = err_code_4_qs;
      end

      addr_hit[10]: begin
        reg_rdata_next[2:0] = err_code_5_qs;
      end

      addr_hit[11]: begin
        reg_rdata_next[2:0] = err_code_6_qs;
      end

      addr_hit[12]: begin
        reg_rdata_next[2:0] = err_code_7_qs;
      end

      addr_hit[13]: begin
        reg_rdata_next[2:0] = err_code_8_qs;
      end

      addr_hit[14]: begin
        reg_rdata_next[2:0] = err_code_9_qs;
      end

      addr_hit[15]: begin
        reg_rdata_next[2:0] = err_code_10_qs;
      end

      addr_hit[16]: begin
        reg_rdata_next[2:0] = err_code_11_qs;
      end

      addr_hit[17]: begin
        reg_rdata_next[2:0] = err_code_12_qs;
      end

      addr_hit[18]: begin
        reg_rdata_next[2:0] = err_code_13_qs;
      end

      addr_hit[19]: begin
        reg_rdata_next[2:0] = err_code_14_qs;
      end

      addr_hit[20]: begin
        reg_rdata_next[2:0] = err_code_15_qs;
      end

      addr_hit[21]: begin
        reg_rdata_next[2:0] = err_code_16_qs;
      end

      addr_hit[22]: begin
        reg_rdata_next[2:0] = err_code_17_qs;
      end

      addr_hit[23]: begin
        reg_rdata_next[2:0] = err_code_18_qs;
      end

      addr_hit[24]: begin
        reg_rdata_next[2:0] = err_code_19_qs;
      end

      addr_hit[25]: begin
        reg_rdata_next[2:0] = err_code_20_qs;
      end

      addr_hit[26]: begin
        reg_rdata_next[2:0] = err_code_21_qs;
      end

      addr_hit[27]: begin
        reg_rdata_next[2:0] = err_code_22_qs;
      end

      addr_hit[28]: begin
        reg_rdata_next[2:0] = err_code_23_qs;
      end

      addr_hit[29]: begin
        reg_rdata_next[2:0] = err_code_24_qs;
      end

      addr_hit[30]: begin
        reg_rdata_next[2:0] = err_code_25_qs;
      end

      addr_hit[31]: begin
        reg_rdata_next[0] = direct_access_regwen_qs;
      end

      addr_hit[32]: begin
        reg_rdata_next[0] = '0;
        reg_rdata_next[1] = '0;
        reg_rdata_next[2] = '0;
        reg_rdata_next[3] = '0;
      end

      addr_hit[33]: begin
        reg_rdata_next[11:0] = direct_access_address_qs;
      end

      addr_hit[34]: begin
        reg_rdata_next[31:0] = direct_access_wdata_0_qs;
      end

      addr_hit[35]: begin
        reg_rdata_next[31:0] = direct_access_wdata_1_qs;
      end

      addr_hit[36]: begin
        reg_rdata_next[31:0] = direct_access_rdata_0_qs;
      end

      addr_hit[37]: begin
        reg_rdata_next[31:0] = direct_access_rdata_1_qs;
      end

      addr_hit[38]: begin
        reg_rdata_next[0] = check_trigger_regwen_qs;
      end

      addr_hit[39]: begin
        reg_rdata_next[0] = '0;
        reg_rdata_next[1] = '0;
      end

      addr_hit[40]: begin
        reg_rdata_next[0] = check_regwen_qs;
      end

      addr_hit[41]: begin
        reg_rdata_next[31:0] = check_timeout_qs;
      end

      addr_hit[42]: begin
        reg_rdata_next[31:0] = integrity_check_period_qs;
      end

      addr_hit[43]: begin
        reg_rdata_next[31:0] = consistency_check_period_qs;
      end

      addr_hit[44]: begin
        reg_rdata_next[0] = sw_manuf_partition_read_lock_qs;
      end

      addr_hit[45]: begin
        reg_rdata_next[0] = svn_partition_read_lock_qs;
      end

      addr_hit[46]: begin
        reg_rdata_next[0] = vendor_test_partition_read_lock_qs;
      end

      addr_hit[47]: begin
        reg_rdata_next[0] = vendor_hashes_manuf_partition_read_lock_qs;
      end

      addr_hit[48]: begin
        reg_rdata_next[0] = vendor_hashes_prod_partition_read_lock_qs;
      end

      addr_hit[49]: begin
        reg_rdata_next[0] = vendor_revocations_prod_partition_read_lock_qs;
      end

      addr_hit[50]: begin
        reg_rdata_next[0] = vendor_non_secret_prod_partition_read_lock_qs;
      end

      addr_hit[51]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_0_read_lock_qs;
      end

      addr_hit[52]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_1_read_lock_qs;
      end

      addr_hit[53]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_2_read_lock_qs;
      end

      addr_hit[54]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_3_read_lock_qs;
      end

      addr_hit[55]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_4_read_lock_qs;
      end

      addr_hit[56]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_5_read_lock_qs;
      end

      addr_hit[57]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_6_read_lock_qs;
      end

      addr_hit[58]: begin
        reg_rdata_next[0] = cptra_ss_lock_hek_prod_7_read_lock_qs;
      end

      addr_hit[59]: begin
        reg_rdata_next[31:0] = vendor_pk_hash_volatile_lock_qs;
      end

      addr_hit[60]: begin
        reg_rdata_next[31:0] = ratchet_seed_volatile_lock_qs;
      end

      addr_hit[61]: begin
        reg_rdata_next[31:0] = sw_test_unlock_partition_digest_0_qs;
      end

      addr_hit[62]: begin
        reg_rdata_next[31:0] = sw_test_unlock_partition_digest_1_qs;
      end

      addr_hit[63]: begin
        reg_rdata_next[31:0] = secret_manuf_partition_digest_0_qs;
      end

      addr_hit[64]: begin
        reg_rdata_next[31:0] = secret_manuf_partition_digest_1_qs;
      end

      addr_hit[65]: begin
        reg_rdata_next[31:0] = secret_prod_partition_0_digest_0_qs;
      end

      addr_hit[66]: begin
        reg_rdata_next[31:0] = secret_prod_partition_0_digest_1_qs;
      end

      addr_hit[67]: begin
        reg_rdata_next[31:0] = secret_prod_partition_1_digest_0_qs;
      end

      addr_hit[68]: begin
        reg_rdata_next[31:0] = secret_prod_partition_1_digest_1_qs;
      end

      addr_hit[69]: begin
        reg_rdata_next[31:0] = secret_prod_partition_2_digest_0_qs;
      end

      addr_hit[70]: begin
        reg_rdata_next[31:0] = secret_prod_partition_2_digest_1_qs;
      end

      addr_hit[71]: begin
        reg_rdata_next[31:0] = secret_prod_partition_3_digest_0_qs;
      end

      addr_hit[72]: begin
        reg_rdata_next[31:0] = secret_prod_partition_3_digest_1_qs;
      end

      addr_hit[73]: begin
        reg_rdata_next[31:0] = sw_manuf_partition_digest_0_qs;
      end

      addr_hit[74]: begin
        reg_rdata_next[31:0] = sw_manuf_partition_digest_1_qs;
      end

      addr_hit[75]: begin
        reg_rdata_next[31:0] = secret_lc_transition_partition_digest_0_qs;
      end

      addr_hit[76]: begin
        reg_rdata_next[31:0] = secret_lc_transition_partition_digest_1_qs;
      end

      addr_hit[77]: begin
        reg_rdata_next[31:0] = vendor_test_partition_digest_0_qs;
      end

      addr_hit[78]: begin
        reg_rdata_next[31:0] = vendor_test_partition_digest_1_qs;
      end

      addr_hit[79]: begin
        reg_rdata_next[31:0] = vendor_hashes_manuf_partition_digest_0_qs;
      end

      addr_hit[80]: begin
        reg_rdata_next[31:0] = vendor_hashes_manuf_partition_digest_1_qs;
      end

      addr_hit[81]: begin
        reg_rdata_next[31:0] = vendor_hashes_prod_partition_digest_0_qs;
      end

      addr_hit[82]: begin
        reg_rdata_next[31:0] = vendor_hashes_prod_partition_digest_1_qs;
      end

      addr_hit[83]: begin
        reg_rdata_next[31:0] = vendor_revocations_prod_partition_digest_0_qs;
      end

      addr_hit[84]: begin
        reg_rdata_next[31:0] = vendor_revocations_prod_partition_digest_1_qs;
      end

      addr_hit[85]: begin
        reg_rdata_next[31:0] = vendor_secret_prod_partition_digest_0_qs;
      end

      addr_hit[86]: begin
        reg_rdata_next[31:0] = vendor_secret_prod_partition_digest_1_qs;
      end

      addr_hit[87]: begin
        reg_rdata_next[31:0] = vendor_non_secret_prod_partition_digest_0_qs;
      end

      addr_hit[88]: begin
        reg_rdata_next[31:0] = vendor_non_secret_prod_partition_digest_1_qs;
      end

      addr_hit[89]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_0_digest_0_qs;
      end

      addr_hit[90]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_0_digest_1_qs;
      end

      addr_hit[91]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_1_digest_0_qs;
      end

      addr_hit[92]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_1_digest_1_qs;
      end

      addr_hit[93]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_2_digest_0_qs;
      end

      addr_hit[94]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_2_digest_1_qs;
      end

      addr_hit[95]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_3_digest_0_qs;
      end

      addr_hit[96]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_3_digest_1_qs;
      end

      addr_hit[97]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_4_digest_0_qs;
      end

      addr_hit[98]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_4_digest_1_qs;
      end

      addr_hit[99]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_5_digest_0_qs;
      end

      addr_hit[100]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_5_digest_1_qs;
      end

      addr_hit[101]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_6_digest_0_qs;
      end

      addr_hit[102]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_6_digest_1_qs;
      end

      addr_hit[103]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_7_digest_0_qs;
      end

      addr_hit[104]: begin
        reg_rdata_next[31:0] = cptra_ss_lock_hek_prod_7_digest_1_qs;
      end

      default: begin
        reg_rdata_next = '1;
      end
    endcase
  end

  // shadow busy
  logic shadow_busy;
  assign shadow_busy = 1'b0;

  // register busy
  assign reg_busy = shadow_busy;

  // Unused signal tieoff

  // wdata / byte enable are not always fully used
  // add a blanket unused statement to handle lint waivers
  logic unused_wdata;
  logic unused_be;
  assign unused_wdata = ^reg_wdata;
  assign unused_be = ^reg_be;

  // Assertions for Register Interface
  `CALIPTRA_ASSERT_PULSE(wePulse, reg_we, clk_i, !rst_ni)
  `CALIPTRA_ASSERT_PULSE(rePulse, reg_re, clk_i, !rst_ni)

  `CALIPTRA_ASSERT(reAfterRv, $rose(reg_re || reg_we) |=> tl_o_pre.d_valid, clk_i, !rst_ni)

  `CALIPTRA_ASSERT(en2addrHit, (reg_we || reg_re) |-> $onehot0(addr_hit), clk_i, !rst_ni)

  // this is formulated as an assumption such that the FPV testbenches do disprove this
  // property by mistake
  //`ASSUME(reqParity, tl_reg_h2d.a_valid |-> tl_reg_h2d.a_user.chk_en == tlul_pkg::CheckDis)

endmodule
