// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle controller top.
//

`include "caliptra_prim_assert.sv"

module lc_ctrl
  import lc_ctrl_pkg::*;
  import lc_ctrl_reg_pkg::*;
  import lc_ctrl_state_pkg::*;
  import axi_pkg::*;
  import kmac_pkg::*;
#(
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Hardware revision numbers exposed in the CSRs.
  parameter logic [SiliconCreatorIdWidth-1:0] SiliconCreatorId = '0,
  parameter logic [ProductIdWidth-1:0]        ProductId        = '0,
  parameter logic [RevisionIdWidth-1:0]       RevisionId       = '0,
  // Idcode value for the JTAG.
  parameter logic [31:0] IdcodeValue = 32'h00000001,
  // Random netlist constants
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid      = LcKeymgrDivWidth'(0),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestUnlocked = LcKeymgrDivWidth'(1),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivDev          = LcKeymgrDivWidth'(2),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction   = LcKeymgrDivWidth'(3),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivRma          = LcKeymgrDivWidth'(4),
  parameter lc_token_mux_t  RndCnstInvalidTokens           = {TokenMuxBits{1'b1}},
  parameter bit             SecVolatileRawUnlockEn         = 1
) (
  // Life cycle controller clock
  input                                              clk_i,
  input                                              rst_ni,
  input                                              Allow_RMA_or_SCRAP_on_PPD, // Note: Addded another condition to RMA and SCRAP transition with Physical presence Detect
                                                                       // This is GPIO strap pin. This pin should be high until LC completes its state
                                                                       // transition to RMA or SCRAP.  
  // Clock for KMAC interface
  // input                                              clk_kmac_i,
  // input                                              rst_kmac_ni,
  // // Bus Interface (device)
  // input  tlul_pkg::tl_h2d_t                          tl_i,
  // output tlul_pkg::tl_d2h_t                          tl_o,

  input  axi_struct_pkg::axi_wr_req_t                        axi_wr_req,
  output axi_struct_pkg::axi_wr_rsp_t                        axi_wr_rsp,
  input  axi_struct_pkg::axi_rd_req_t                        axi_rd_req,
  output axi_struct_pkg::axi_rd_rsp_t                        axi_rd_rsp,

  // input  tlul_pkg::tl_h2d_t                          dmi_tl_i,
  // output tlul_pkg::tl_d2h_t                          dmi_tl_o,

  // // AXI interface (device)
  // axi_if.w_sub                                       s_lc_axi_w_if,
  // axi_if.r_sub                                       s_lc_axi_r_if,

  // JTAG TAP.
  input  jtag_pkg::jtag_req_t                        jtag_i,
  output jtag_pkg::jtag_rsp_t                        jtag_o,
  // This bypasses the clock inverter inside the JTAG TAP for scanmmode.
  input                                              scan_rst_ni,
  input  caliptra_prim_mubi_pkg::mubi4_t                      scanmode_i,


  // Alert outputs.
  //----------------------------------------------------------------------------------
  // NOTE: Caliptra-SS removed these differential alert sender signals. Caliptra-SS 
  // uses "alerts" signal  instead of these pair signal set. SoC should take action if 
  // there is at leastone of the error signals: fatal_bus_integ_error_q,
  // fatal_state_error_q, or fatal_prog_error_q

  output [NumAlerts-1:0] alerts,
  // input  caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  // output caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,

  //-----------------------------------------------------------------------------------

  //----------------------------------------------------------------------------------
  // NOTE: Caliptra-SS removed these differential escalation signals. Instead of
  // generating esc_scrap_state0 and esc_scrap_state1 with prim_esc_receiver, 
  // Caliptra-SS delivers these signals to LC_CTRL

  input esc_scrap_state0,
  input esc_scrap_state1,
  // // Escalation inputs (severity 1 and 2).
  // // These need not be synchronized since the alert handler is
  // // in the same clock domain as the LC controller.
  // input  caliptra_prim_esc_pkg::esc_rx_t                      esc_scrap_state0_tx_i,
  // output caliptra_prim_esc_pkg::esc_tx_t                      esc_scrap_state0_rx_o,
  // input  caliptra_prim_esc_pkg::esc_rx_t                      esc_scrap_state1_tx_i,
  // output caliptra_prim_esc_pkg::esc_tx_t                      esc_scrap_state1_rx_o,
  //-----------------------------------------------------------------------------------


  // Power manager interface (inputs are synced to lifecycle clock domain).
  input  pwrmgr_pkg::pwr_lc_req_t                    pwr_lc_i,
  output pwrmgr_pkg::pwr_lc_rsp_t                    pwr_lc_o,
  // Strap sampling override that is only used when SecVolatileRawUnlockEn = 1,
  // Otherwise this output is tied off to 0.
  // output logic                                       strap_en_override_o,
  // Strap override - this is only used when
  // Macro-specific test registers going to lifecycle TAP
  output otp_ctrl_pkg::lc_otp_vendor_test_req_t      lc_otp_vendor_test_o,
  input  otp_ctrl_pkg::lc_otp_vendor_test_rsp_t      lc_otp_vendor_test_i,
  // Life cycle transition command interface.
  // No sync required since LC and OTP are in the same clock domain.
  output otp_ctrl_pkg::lc_otp_program_req_t          lc_otp_program_o,
  input  otp_ctrl_pkg::lc_otp_program_rsp_t          lc_otp_program_i,
  // Life cycle hashing interface for raw unlock
  // Synchronized in the life cycle controller.
  // SEC_CM: TOKEN.DIGEST
  //-- input  kmac_pkg::app_rsp_t                         kmac_data_i,
  //-- output kmac_pkg::app_req_t                         kmac_data_o,
  // OTP broadcast outputs
  // No sync required since LC and OTP are in the same clock domain.
  // SEC_CM: TOKEN_VALID.CTRL.MUBI
  input  otp_ctrl_pkg::otp_lc_data_t                 otp_lc_data_i,
  // Life cycle broadcast outputs (all of them are registered).
  // SEC_CM: INTERSIG.MUBI
  output lc_tx_t                                     lc_dft_en_o,
  // output lc_tx_t                                     lc_nvm_debug_en_o,
  output lc_tx_t                                     lc_hw_debug_en_o,
  
  output lc_tx_t                                     lc_creator_seed_sw_rw_en_o, // TODO: remove them when they are removed from otp ctrl
  output lc_tx_t                                     lc_owner_seed_sw_rw_en_o,  // TODO: remove them when they are removed from otp ctrl
  // output lc_tx_t                                     lc_iso_part_sw_rd_en_o,
  // output lc_tx_t                                     lc_iso_part_sw_wr_en_o,
  output lc_tx_t                                     lc_seed_hw_rd_en_o,  // TODO: remove them when they are removed from otp ctrl
  // output lc_tx_t                                     lc_keymgr_en_o,
  output lc_tx_t                                     lc_escalate_en_o,
  output lc_tx_t                                     lc_check_byp_en_o,
  // Request and feedback to/from clock manager and AST.
  // The ack is synced to the lc clock domain using prim_lc_sync.
  // SEC_CM: INTERSIG.MUBI
  output lc_tx_t                                     lc_clk_byp_req_o,
  input  lc_tx_t                                     lc_clk_byp_ack_i,
  // Request and feedback to/from flash controller.
  // The ack is synced to the lc clock domain using prim_lc_sync.
  // output lc_flash_rma_seed_t                         lc_flash_rma_seed_o,
  // SEC_CM: INTERSIG.MUBI
  // output lc_tx_t                                     lc_flash_rma_req_o,
  // input  lc_tx_t [NumRmaAckSigs-1:0]                 lc_flash_rma_ack_i,
  // State group diversification value for keymgr.
  // output lc_keymgr_div_t                             lc_keymgr_div_o,
  // Hardware config input, needed for the DEVICE_ID field.
  input  otp_ctrl_pkg::otp_device_id_t               otp_device_id_i,
  // Hardware config input, needed for the MANUF_STATE field.
  input  otp_ctrl_pkg::otp_device_id_t               otp_manuf_state_i,
  // Hardware revision output (static)
  output lc_hw_rev_t                                 hw_rev_o
);
  //Unused signals
  lc_tx_t                                     lc_cpu_en_o;
  // Short-cut assignments since Caliptra-SS does not use this ports
  lc_tx_t                                     lc_nvm_debug_en_o;
  lc_tx_t                                     lc_iso_part_sw_rd_en_o;
  lc_tx_t                                     lc_iso_part_sw_wr_en_o;
  lc_tx_t                                     lc_keymgr_en_o;
  lc_flash_rma_seed_t                         lc_flash_rma_seed_o;
  lc_keymgr_div_t                             lc_keymgr_div_o;
  lc_tx_t                                     lc_flash_rma_req_o;
  lc_tx_t[NumRmaAckSigs-1:0]                  lc_flash_rma_ack_i;
  assign lc_flash_rma_ack_i = (lc_tx_test_true_strict(lc_flash_rma_req_o)) ? {NumRmaAckSigs{lc_ctrl_pkg::On}} : {NumRmaAckSigs{lc_ctrl_pkg::Off}};

  import caliptra_prim_mubi_pkg::mubi8_t;
  import caliptra_prim_mubi_pkg::MuBi8False;
  import caliptra_prim_mubi_pkg::mubi8_test_true_strict;
  import caliptra_prim_mubi_pkg::mubi8_test_false_loose;

  // AXI2TLUL interface signals
  tlul_pkg::tl_h2d_t      regs_tl_i;
  tlul_pkg::tl_d2h_t      regs_tl_o;

  axi_if #(
    .AW(axi_struct_pkg::TLUL_AXI_STRUCT_ADDR_WIDTH),
    .DW(32                                        ),
    .UW(axi_struct_pkg::TLUL_AXI_STRUCT_USER_WIDTH),
    .IW(axi_struct_pkg::TLUL_AXI_STRUCT_ID_WIDTH  )
  ) axi_if (
    .clk(clk_i),
    .rst_n(rst_ni)
  );

  assign axi_if.awaddr      = axi_wr_req.awaddr;
  assign axi_if.awburst     = axi_wr_req.awburst;
  assign axi_if.awsize      = axi_wr_req.awsize;
  assign axi_if.awlen       = axi_wr_req.awlen;
  assign axi_if.awuser      = axi_wr_req.awuser;
  assign axi_if.awid        = axi_wr_req.awid;
  assign axi_if.awlock      = axi_wr_req.awlock;
  assign axi_if.awvalid     = axi_wr_req.awvalid;
  assign axi_wr_rsp.awready = axi_if.awready;
  
  assign axi_if.wdata       = axi_wr_req.wdata;
  assign axi_if.wuser       = '0; // FIXME
  assign axi_if.wstrb       = axi_wr_req.wstrb;
  assign axi_if.wlast       = axi_wr_req.wlast;
  assign axi_if.wvalid      = axi_wr_req.wvalid;
  assign axi_wr_rsp.wready  = axi_if.wready;
  
  assign axi_wr_rsp.bresp   = axi_if.bresp;
  assign axi_wr_rsp.bid     = axi_if.bid;
  assign axi_wr_rsp.bvalid  = axi_if.bvalid;
  assign axi_if.bready      = axi_wr_req.bready;
  
  assign axi_if.araddr      = axi_rd_req.araddr;
  assign axi_if.arburst     = axi_rd_req.arburst;
  assign axi_if.arsize      = axi_rd_req.arsize;
  assign axi_if.arlen       = axi_rd_req.arlen;
  assign axi_if.aruser      = axi_rd_req.aruser;
  assign axi_if.arid        = axi_rd_req.arid;
  assign axi_if.arlock      = axi_rd_req.arlock;
  assign axi_if.arvalid     = axi_rd_req.arvalid;
  assign axi_rd_rsp.arready = axi_if.arready;
  
  assign axi_rd_rsp.rdata   = axi_if.rdata;
  assign axi_rd_rsp.rresp   = axi_if.rresp;
  assign axi_rd_rsp.rid     = axi_if.rid;
  assign axi_rd_rsp.rlast   = axi_if.rlast;
  assign axi_rd_rsp.rvalid  = axi_if.rvalid;
  assign axi_if.rready      = axi_rd_req.rready;

  // AXI2TLUL instance
  axi2tlul #(
      .AW     (axi_struct_pkg::TLUL_AXI_STRUCT_ADDR_WIDTH),
      .DW     (32                                        ),
      .UW     (axi_struct_pkg::TLUL_AXI_STRUCT_USER_WIDTH),
      .IW     (axi_struct_pkg::TLUL_AXI_STRUCT_ID_WIDTH  )
  ) u_lc_axi2tlul (
      .clk            (clk_i),
      .rst_n          (rst_ni),
      .s_axi_w_if     (axi_if.w_sub),
      .s_axi_r_if     (axi_if.r_sub),
      .tl_o           (regs_tl_i),
      .tl_i           (regs_tl_o)
  );
  
  ////////////////////////
  // Integration Checks //
  ////////////////////////

  // Check that the CSR parameters correspond with the ones used in the design.
  `CALIPTRA_ASSERT_INIT(DecLcStateWidthCheck_A, CsrLcStateWidth == ExtDecLcStateWidth)
  `CALIPTRA_ASSERT_INIT(DecLcCountWidthCheck_A, CsrLcCountWidth == DecLcCountWidth)
  `CALIPTRA_ASSERT_INIT(DecLcIdStateWidthCheck_A, CsrLcIdStateWidth == ExtDecLcIdStateWidth)
  `CALIPTRA_ASSERT_INIT(NumTokenWordsCheck_A, NumTokenWords == LcTokenWidth/32)
  `CALIPTRA_ASSERT_INIT(OtpTestCtrlWidth_A, otp_ctrl_pkg::OtpTestCtrlWidth == CsrOtpTestCtrlWidth)

  /////////////
  // Regfile //
  /////////////

  lc_ctrl_reg_pkg::lc_ctrl_reg2hw_t reg2hw;
  lc_ctrl_reg_pkg::lc_ctrl_hw2reg_t hw2reg;

  // SEC_CM: TRANSITION.CONFIG.REGWEN, STATE.CONFIG.SPARSE
  logic fatal_bus_integ_error_q, fatal_bus_integ_error_csr_d, fatal_bus_integ_error_tap_d;
  lc_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i      ( regs_tl_i                   ),
    .tl_o      ( regs_tl_o                   ),
    .reg2hw    ( reg2hw                      ),
    .hw2reg    ( hw2reg                      ),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o( fatal_bus_integ_error_csr_d )
  );

  ////////////////////
  // Life Cycle TAP //
  ////////////////////

  tlul_pkg::tl_h2d_t tap_tl_h2d;
  tlul_pkg::tl_d2h_t tap_tl_d2h;
  lc_ctrl_reg_pkg::lc_ctrl_reg2hw_t tap_reg2hw;
  lc_ctrl_reg_pkg::lc_ctrl_hw2reg_t tap_hw2reg;

  lc_ctrl_reg_top u_reg_tap (
    .clk_i,
    .rst_ni,
    .tl_i      ( tap_tl_h2d                  ),
    .tl_o      ( tap_tl_d2h                  ),
    .reg2hw    ( tap_reg2hw                  ),
    .hw2reg    ( tap_hw2reg                  ),
    // SEC_CM: BUS.INTEGRITY
    // While the TAP does not have bus integrity, it does have a WE checker
    // that feeds into intg_err_o - hence this is wired up to the fatal_bus_integ_error.
    .intg_err_o( fatal_bus_integ_error_tap_d )
  );


  // This reuses the JTAG DTM and DMI from the RISC-V external
  // debug v0.13 specification to read and write the lc_ctrl CSRs:
  // https://github.com/riscv/riscv-debug-spec/blob/release/riscv-debug-release.pdf
  // The register addresses correspond to the byte offsets of the lc_ctrl CSRs, divided by 4.
  // Note that the DMI reset does not affect the LC controller in any way.
  dm::dmi_req_t dmi_req;
  logic dmi_req_valid;
  logic dmi_req_ready;
  dm::dmi_resp_t dmi_resp;
  logic dmi_resp_ready;
  logic dmi_resp_valid;

  logic scanmode;
  caliptra_prim_mubi4_dec u_prim_mubi4_dec (
    .mubi_i(scanmode_i),
    .mubi_dec_o(scanmode)
  );

    logic tck_muxed;
    logic trst_n_muxed;
    caliptra_prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_prim_clock_mux2 (
      .clk0_i(jtag_i.tck),
      .clk1_i(clk_i),
      .sel_i (scanmode),
      .clk_o (tck_muxed)
    );

    caliptra_prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_prim_rst_n_mux2 (
      .clk0_i(jtag_i.trst_n),
      .clk1_i(scan_rst_ni),
      .sel_i (scanmode),
      .clk_o (trst_n_muxed)
    );

    logic req_ready;
    assign req_ready = dmi_req_ready & dmi_resp_ready;
    dmi_jtag #(
      .IdcodeValue(IdcodeValue),
      .NumDmiWordAbits(7)
    ) u_dmi_jtag (
      .clk_i,
      .rst_ni,
      .testmode_i       ( scanmode          ),
      .test_rst_ni      ( scan_rst_ni       ),
      .dmi_rst_no       (                   ), // unused
      .dmi_req_o        ( dmi_req           ),
      .dmi_req_valid_o  ( dmi_req_valid     ),
      // unless there is room for response, stall
      .dmi_req_ready_i  ( req_ready         ),
      .dmi_resp_i       ( dmi_resp          ),
      .dmi_resp_ready_o ( dmi_resp_ready    ),
      .dmi_resp_valid_i ( dmi_resp_valid    ),
      .tck_i            ( tck_muxed         ),
      .tms_i            ( jtag_i.tms        ),
      .trst_ni          ( trst_n_muxed      ),
      .td_i             ( jtag_i.tdi        ),
      .td_o             ( jtag_o.tdo        ),
      .tdo_oe_o         ( jtag_o.tdo_oe     )
    );

    // DMI to TL-UL transducing
    tlul_adapter_host #(
      .EnableDataIntgGen(1)
    ) u_tap_tlul_host (
      .clk_i,
      .rst_ni,
      // do not make a request unless there is room for the response
      .req_i        ( dmi_req_valid & dmi_resp_ready         ),
      .gnt_o        ( dmi_req_ready                          ),
      .addr_i       ( top_pkg::TL_AW'({dmi_req.addr, 2'b00}) ),
      .we_i         ( dmi_req.op == dm::DTM_WRITE            ),
      .wdata_i      ( dmi_req.data                           ),
      .wdata_intg_i ('0                                      ),
      .be_i         ( {top_pkg::TL_DBW{1'b1}}                ),
      .instr_type_i ( caliptra_prim_mubi_pkg::MuBi4False              ),
      .valid_o      ( dmi_resp_valid                         ),
      .rdata_o      ( dmi_resp.data                          ),
      .rdata_intg_o (                                        ),
      .err_o        (                                        ),
      .intg_err_o   (                                        ),
      .tl_o         ( tap_tl_h2d                             ),
      .tl_i         ( tap_tl_d2h                             )
    );

    // TL-UL to DMI transducing
    assign dmi_resp.resp = '0; // unused inside dmi_jtag

    // These signals are unused
    logic unused_tap_tl_d2h;
    assign unused_tap_tl_d2h = ^{
      dmi_req.addr[31:30],
      tap_tl_d2h.d_opcode,
      tap_tl_d2h.d_param,
      tap_tl_d2h.d_size,
      tap_tl_d2h.d_source,
      tap_tl_d2h.d_sink,
      tap_tl_d2h.d_user,
      tap_tl_d2h.d_error
    };


  ///////////////////////////////////////
  // Transition Interface and HW Mutex //
  ///////////////////////////////////////

  // All registers are HWext
  logic          trans_success_d, trans_success_q;
  logic          trans_cnt_oflw_error_d, trans_cnt_oflw_error_q;
  logic          trans_invalid_error_d, trans_invalid_error_q;
  logic          token_invalid_error_d, token_invalid_error_q;
  logic          flash_rma_error_d, flash_rma_error_q;
  logic          otp_prog_error_d, fatal_prog_error_q;
  logic          state_invalid_error_d, fatal_state_error_q;
  logic          otp_part_error_q;
  mubi8_t        sw_claim_transition_if_d, sw_claim_transition_if_q;
  mubi8_t        tap_claim_transition_if_d, tap_claim_transition_if_q;
  logic          transition_cmd;
  lc_token_t     transition_token_d, transition_token_q;
  ext_dec_lc_state_t transition_target_d, transition_target_q;
  // No need to register these.
  ext_dec_lc_state_t dec_lc_state;
  dec_lc_cnt_t       dec_lc_cnt;
  dec_lc_id_state_e  dec_lc_id_state;

  logic lc_idle_d, lc_done_d;

  // Assign hardware revision output
  assign hw_rev_o = '{silicon_creator_id: SiliconCreatorId,
                      product_id:         ProductId,
                      revision_id:        RevisionId,
                      reserved:           '0};

  // OTP Vendor control bits
  logic ext_clock_switched;
  logic use_ext_clock_d, use_ext_clock_q;
  logic volatile_raw_unlock_d, volatile_raw_unlock_q;
  logic [CsrOtpTestCtrlWidth-1:0] otp_vendor_test_ctrl_d, otp_vendor_test_ctrl_q;
  logic [CsrOtpTestStatusWidth-1:0] otp_vendor_test_status;

  always_comb begin : p_csr_assign_outputs
    hw2reg = '0;
    hw2reg.status.initialized            = lc_done_d;
    hw2reg.status.ready                  = lc_idle_d;
    hw2reg.status.ext_clock_switched     = ext_clock_switched;
    hw2reg.status.transition_successful  = trans_success_q;
    hw2reg.status.transition_count_error = trans_cnt_oflw_error_q;
    hw2reg.status.transition_error       = trans_invalid_error_q;
    hw2reg.status.token_error            = token_invalid_error_q;
    hw2reg.status.flash_rma_error        = flash_rma_error_q;
    hw2reg.status.otp_error              = fatal_prog_error_q;
    hw2reg.status.state_error            = fatal_state_error_q;
    hw2reg.status.otp_partition_error    = otp_part_error_q;
    hw2reg.status.bus_integ_error        = fatal_bus_integ_error_q;
    hw2reg.lc_state                      = dec_lc_state;
    hw2reg.lc_transition_cnt             = dec_lc_cnt;
    hw2reg.lc_id_state                   = {DecLcIdStateNumRep{dec_lc_id_state}};
    hw2reg.device_id                     = otp_device_id_i;
    hw2reg.manuf_state                   = otp_manuf_state_i;
    hw2reg.hw_revision0.silicon_creator_id = hw_rev_o.silicon_creator_id;
    hw2reg.hw_revision0.product_id         = hw_rev_o.product_id;
    hw2reg.hw_revision1.revision_id        = hw_rev_o.revision_id;
    hw2reg.hw_revision1.reserved           = '0;

    // The assignments above are identical for the TAP.
    tap_hw2reg = hw2reg;

    // Assignments gated by mutex. Again, the TAP has priority.
    tap_hw2reg.claim_transition_if = tap_claim_transition_if_q;
    hw2reg.claim_transition_if = sw_claim_transition_if_q;
    if (mubi8_test_true_strict(tap_claim_transition_if_q)) begin
      tap_hw2reg.transition_ctrl.ext_clock_en = use_ext_clock_q;
      tap_hw2reg.transition_ctrl.volatile_raw_unlock = volatile_raw_unlock_q;
      tap_hw2reg.transition_token  = transition_token_q;
      tap_hw2reg.transition_target = transition_target_q;
      // SEC_CM: TRANSITION.CONFIG.REGWEN
      tap_hw2reg.transition_regwen = lc_idle_d;
      tap_hw2reg.otp_vendor_test_ctrl     = otp_vendor_test_ctrl_q;
      tap_hw2reg.otp_vendor_test_status   = otp_vendor_test_status;
    end else if (mubi8_test_true_strict(sw_claim_transition_if_q)) begin
      hw2reg.transition_ctrl.ext_clock_en = use_ext_clock_q;
      hw2reg.transition_ctrl.volatile_raw_unlock = volatile_raw_unlock_q;
      hw2reg.transition_token  = transition_token_q;
      hw2reg.transition_target = transition_target_q;
      // SEC_CM: TRANSITION.CONFIG.REGWEN
      hw2reg.transition_regwen = lc_idle_d;
      hw2reg.otp_vendor_test_ctrl     = otp_vendor_test_ctrl_q;
      hw2reg.otp_vendor_test_status   = otp_vendor_test_status;
    end
  end

  always_comb begin : p_csr_assign_inputs
    sw_claim_transition_if_d  = sw_claim_transition_if_q;
    tap_claim_transition_if_d = tap_claim_transition_if_q;
    transition_token_d        = transition_token_q;
    transition_target_d       = transition_target_q;
    transition_cmd            = 1'b0;
    otp_vendor_test_ctrl_d    = otp_vendor_test_ctrl_q;
    use_ext_clock_d           = use_ext_clock_q;
    volatile_raw_unlock_d     = volatile_raw_unlock_q;

    // Note that the mutex claims from the TAP and SW side could arrive within the same cycle.
    // In that case we give priority to the TAP mutex claim in order to avoid a race condition.
    // TAP mutex claim.
    if (mubi8_test_false_loose(sw_claim_transition_if_q) &&
        tap_reg2hw.claim_transition_if.qe) begin
      tap_claim_transition_if_d = mubi8_t'(tap_reg2hw.claim_transition_if.q);
    // SW mutex claim.
    end else if (mubi8_test_false_loose(tap_claim_transition_if_q) &&
        reg2hw.claim_transition_if.qe) begin
      sw_claim_transition_if_d = mubi8_t'(reg2hw.claim_transition_if.q);
    end


    // The idle signal serves as the REGWEN in this case.
    if (lc_idle_d) begin
      // The TAP has priority.
      if (mubi8_test_true_strict(tap_claim_transition_if_q)) begin
        transition_cmd = tap_reg2hw.transition_cmd.q &
                         tap_reg2hw.transition_cmd.qe;

        if (tap_reg2hw.transition_ctrl.ext_clock_en.qe) begin
          use_ext_clock_d |= tap_reg2hw.transition_ctrl.ext_clock_en.q;
        end

        // ---------- VOLATILE_TEST_UNLOCKED CODE SECTION START ----------
        // NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
        // THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED VIA
        // SecVolatileRawUnlockEn AT COMPILETIME FOR PRODUCTION DEVICES.
        // ---------------------------------------------------------------
        if (tap_reg2hw.transition_ctrl.volatile_raw_unlock.qe) begin
          volatile_raw_unlock_d = tap_reg2hw.transition_ctrl.volatile_raw_unlock.q;
        end
        // ----------- VOLATILE_TEST_UNLOCKED CODE SECTION END -----------

        for (int k = 0; k < LcTokenWidth/32; k++) begin
          if (tap_reg2hw.transition_token[k].qe) begin
            transition_token_d[k*32 +: 32] = tap_reg2hw.transition_token[k].q;
          end
        end

        if (tap_reg2hw.transition_target.qe) begin
          for (int k = 0; k < DecLcStateNumRep; k++) begin
            transition_target_d[k] = dec_lc_state_e'(
                tap_reg2hw.transition_target.q[k*DecLcStateWidth +: DecLcStateWidth]);
          end
        end

        if (tap_reg2hw.otp_vendor_test_ctrl.qe) begin
          otp_vendor_test_ctrl_d = tap_reg2hw.otp_vendor_test_ctrl.q;
        end
      end else if (mubi8_test_true_strict(sw_claim_transition_if_q)) begin
        transition_cmd = reg2hw.transition_cmd.q &
                         reg2hw.transition_cmd.qe;

        if (reg2hw.transition_ctrl.ext_clock_en.qe) begin
          use_ext_clock_d |= reg2hw.transition_ctrl.ext_clock_en.q;
        end

        // ---------- VOLATILE_TEST_UNLOCKED CODE SECTION START ----------
        // NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
        // THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED VIA
        // SecVolatileRawUnlockEn AT COMPILETIME FOR PRODUCTION DEVICES.
        // ---------------------------------------------------------------
        if (reg2hw.transition_ctrl.volatile_raw_unlock.qe) begin
          volatile_raw_unlock_d = reg2hw.transition_ctrl.volatile_raw_unlock.q;
        end
        // ----------- VOLATILE_TEST_UNLOCKED CODE SECTION END -----------

        for (int k = 0; k < LcTokenWidth/32; k++) begin
          if (reg2hw.transition_token[k].qe) begin
            transition_token_d[k*32 +: 32] = reg2hw.transition_token[k].q;
          end
        end

        if (reg2hw.transition_target.qe) begin
          for (int k = 0; k < DecLcStateNumRep; k++) begin
            transition_target_d[k] = dec_lc_state_e'(
                reg2hw.transition_target.q[k*DecLcStateWidth +: DecLcStateWidth]);
          end
        end

        if (reg2hw.otp_vendor_test_ctrl.qe) begin
          otp_vendor_test_ctrl_d = reg2hw.otp_vendor_test_ctrl.q;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_csrs
    if (!rst_ni) begin
      trans_success_q           <= 1'b0;
      trans_cnt_oflw_error_q    <= 1'b0;
      trans_invalid_error_q     <= 1'b0;
      token_invalid_error_q     <= 1'b0;
      flash_rma_error_q         <= 1'b0;
      fatal_prog_error_q        <= 1'b0;
      fatal_state_error_q       <= 1'b0;
      sw_claim_transition_if_q  <= MuBi8False;
      tap_claim_transition_if_q <= MuBi8False;
      transition_token_q        <= '0;
      transition_target_q       <= {DecLcStateNumRep{DecLcStRaw}};
      otp_part_error_q          <= 1'b0;
      fatal_bus_integ_error_q   <= 1'b0;
      otp_vendor_test_ctrl_q    <= '0;
      use_ext_clock_q           <= 1'b0;
    end else begin
      // ---------- VOLATILE_TEST_UNLOCKED CODE SECTION START ----------
      // NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
      // THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED VIA
      // SecVolatileRawUnlockEn AT COMPILETIME FOR PRODUCTION DEVICES.
      // ---------------------------------------------------------------
      // In case of a volatile RAW unlock, this bit has to be cleared when the volatile
      // unlock is followed by a real transition.
      // ----------- VOLATILE_TEST_UNLOCKED CODE SECTION END -----------
      if (SecVolatileRawUnlockEn && transition_cmd && !volatile_raw_unlock_q) begin
        trans_success_q <= 1'b0;
      end else begin
        trans_success_q <= trans_success_d | trans_success_q;
      end
      // All other status and error bits are terminal and require a reset cycle.
      trans_cnt_oflw_error_q    <= trans_cnt_oflw_error_d  | trans_cnt_oflw_error_q;
      trans_invalid_error_q     <= trans_invalid_error_d   | trans_invalid_error_q;
      token_invalid_error_q     <= token_invalid_error_d   | token_invalid_error_q;
      flash_rma_error_q         <= flash_rma_error_d       | flash_rma_error_q;
      fatal_prog_error_q        <= otp_prog_error_d        | fatal_prog_error_q;
      fatal_state_error_q       <= state_invalid_error_d   | fatal_state_error_q;
      otp_part_error_q          <= otp_lc_data_i.error     | otp_part_error_q;
      fatal_bus_integ_error_q   <= fatal_bus_integ_error_csr_d |
                                   fatal_bus_integ_error_tap_d |
                                   fatal_bus_integ_error_q;
      // Other regs, gated by mutex further below.
      sw_claim_transition_if_q  <= sw_claim_transition_if_d;
      tap_claim_transition_if_q <= tap_claim_transition_if_d;
      transition_token_q        <= transition_token_d;
      transition_target_q       <= transition_target_d;
      otp_vendor_test_ctrl_q    <= otp_vendor_test_ctrl_d;
      use_ext_clock_q           <= use_ext_clock_d;
    end
  end

  // ---------- VOLATILE_TEST_UNLOCKED CODE SECTION START ----------
  // NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
  // THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED VIA
  // SecVolatileRawUnlockEn AT COMPILETIME FOR PRODUCTION DEVICES.
  // ---------------------------------------------------------------
  // If not enabled, this register will become a constant.
  if (SecVolatileRawUnlockEn) begin : gen_volatile_raw_unlock_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : p_volatile_raw_unlock_reg
      if (!rst_ni) begin
        volatile_raw_unlock_q     <= 1'b0;
      end else begin
        volatile_raw_unlock_q     <= volatile_raw_unlock_d;
      end
    end
  end else begin : gen_volatile_raw_unlock_const
    logic unused_volatile_raw_unlock;
    assign unused_volatile_raw_unlock = ^volatile_raw_unlock_d;
    assign volatile_raw_unlock_q = 1'b0;
  end
  // ----------- VOLATILE_TEST_UNLOCKED CODE SECTION END -----------

  assign lc_flash_rma_seed_o = transition_token_q[RmaSeedWidth-1:0];

  // Gate the vendor specific test ctrl/status bits to zero in production states.
  // Buffer the enable signal to prevent optimization of the multibit signal.
  lc_tx_t lc_raw_test_rma;
  lc_tx_t [1:0] lc_raw_test_rma_buf;
  caliptra_prim_lc_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_raw_test_rma),
    .lc_en_o(lc_raw_test_rma_buf)
  );

  assign lc_otp_vendor_test_o.ctrl = (lc_tx_test_true_strict(lc_raw_test_rma_buf[0])) ?
                                     otp_vendor_test_ctrl_q                           : '0;
  assign otp_vendor_test_status    = (lc_tx_test_true_strict(lc_raw_test_rma_buf[1])) ?
                                     lc_otp_vendor_test_i.status                      : '0;

  //////////////////
  // Alert Sender //
  //////////////////

  // logic [NumAlerts-1:0] alerts;
  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] tap_alert_test;

  assign alerts = {
    fatal_bus_integ_error_q,
    fatal_state_error_q,
    fatal_prog_error_q
  };

  assign alert_test = {
    reg2hw.alert_test.fatal_bus_integ_error.q &
    reg2hw.alert_test.fatal_bus_integ_error.qe,
    reg2hw.alert_test.fatal_state_error.q &
    reg2hw.alert_test.fatal_state_error.qe,
    reg2hw.alert_test.fatal_prog_error.q &
    reg2hw.alert_test.fatal_prog_error.qe
  };

   assign tap_alert_test = {
    tap_reg2hw.alert_test.fatal_bus_integ_error.q &
    tap_reg2hw.alert_test.fatal_bus_integ_error.qe,
    tap_reg2hw.alert_test.fatal_state_error.q &
    tap_reg2hw.alert_test.fatal_state_error.qe,
    tap_reg2hw.alert_test.fatal_prog_error.q &
    tap_reg2hw.alert_test.fatal_prog_error.qe
  };

// ------------------------Removing Alert sender module----------------------------
// NOTE: Caliptra-SS wires out alerts[k] signals and makes them output of LC_CTRL
// This action also removes the functionallity of alert test that can be done with
// alert_test and tap_dmi_alert_test.
  
  // for (genvar k = 0; k < NumAlerts; k++) begin : gen_alert_tx
  //   caliptra_prim_alert_sender #(
  //     .AsyncOn(AlertAsyncOn[k]),
  //     .IsFatal(1)
  //   ) u_prim_alert_sender (
  //     .clk_i,
  //     .rst_ni,
  //     .alert_test_i  ( alert_test[k] |
  //                      tap_dmi_alert_test[k] ),
  //     .alert_req_i   ( alerts[k]             ),
  //     .alert_ack_o   (                       ),
  //     .alert_state_o (                       ),
  //     .alert_rx_i    ( alert_rx_i[k]         ),
  //     .alert_tx_o    ( alert_tx_o[k]         )
  //   );
  // end

//------------------------------------------------------------------------------------


  ///////////////////////////////
  // KMAC design Instance
  ///////////////////////////////

  kmac_pkg::app_rsp_t                         kmac_data_i;
  kmac_pkg::app_req_t                         kmac_data_o;
  wire lc_tx_t                                lc_escalate_en_int;
  wire app_req_t  [2:0]            app_req;
  wire app_rsp_t  [2:0]            app_rsp;

  assign lc_escalate_en_int = lc_escalate_en_o;

  assign app_req[0] = '0;
  assign app_req[1] = kmac_data_o;
  assign app_req[2] = '0;

  assign kmac_data_i = app_rsp[1];

  kmac #(
    .EnMasking(0),
    .SwKeyMasked(0),
    .NumAppIntf(3)
  ) kmac (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni (rst_ni),
    // TLUL interface
    .tl_i               ('0),
    .tl_o               (  ),
    // alert interface
    .alert_rx_i         ('0),
    .alert_tx_o         (  ),

    // escalate en
    .lc_escalate_en_i   (lc_escalate_en_int),

    // KeyMgr sideload key interface
    .keymgr_key_i       ('0),

    // KeyMgr KDF datapath
    .app_i              ( app_req ),
    .app_o              ( app_rsp ),

    // Interrupts
    .intr_kmac_done_o   ( ),
    .intr_fifo_empty_o  ( ),
    .intr_kmac_err_o    ( ),

    // Idle interface
    .idle_o             ( ),
    .en_masking_o       ( ),

    // EDN interface
    .clk_edn_i          (clk_i),
    .rst_edn_ni         (rst_ni),
    .entropy_o          (  ),
    .entropy_i          ('0)
  );

//----------------------------------------------------------------------------------
// NOTE: Caliptra-SS removed these differential esc_receiver signals and module. 

  // //////////////////////////
  // // Escalation Receivers //
  // //////////////////////////

  // // SEC_CM: MAIN.FSM.GLOBAL_ESC
  // // We still have two escalation receivers here for historical reasons.
  // // The two actions "wipe secrets" and "scrap lifecycle state" have been
  // // combined in order to simplify both DV and the design, as otherwise
  // // this separation of very intertwined actions would have caused too many
  // // unnecessary corner cases. The escalation receivers are now redundant and
  // // trigger both actions at once.

  // // This escalation action moves the life cycle
  // // state into a temporary "SCRAP" state named "ESCALATE",
  // // and asserts the lc_escalate_en life cycle control signal.
  // logic esc_scrap_state0;
  // caliptra_prim_esc_receiver #(
  //   .N_ESC_SEV   (alert_handler_reg_pkg::N_ESC_SEV),
  //   .PING_CNT_DW (alert_handler_reg_pkg::PING_CNT_DW)
  // ) u_prim_esc_receiver0 (
  //   .clk_i,
  //   .rst_ni,
  //   .esc_req_o (esc_scrap_state0),
  //   .esc_rx_o  (esc_scrap_state0_rx_o),
  //   .esc_tx_i  (esc_scrap_state0_tx_i)
  // );

  // // This escalation action moves the life cycle
  // // state into a temporary "SCRAP" state named "ESCALATE".
  // logic esc_scrap_state1;
  // caliptra_prim_esc_receiver #(
  //   .N_ESC_SEV   (alert_handler_reg_pkg::N_ESC_SEV),
  //   .PING_CNT_DW (alert_handler_reg_pkg::PING_CNT_DW)
  // ) u_prim_esc_receiver1 (
  //   .clk_i,
  //   .rst_ni,
  //   .esc_req_o (esc_scrap_state1),
  //   .esc_rx_o  (esc_scrap_state1_rx_o),
  //   .esc_tx_i  (esc_scrap_state1_tx_i)
  // );
//----------------------------------------------------------------------------------


  ////////////////////////////
  // Synchronization of IOs //
  ////////////////////////////

  // Signals going to and coming from power manager.
  logic lc_init;
  caliptra_prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync_init (
    .clk_i,
    .rst_ni,
    .d_i(pwr_lc_i.lc_init),
    .q_o(lc_init)
  );

  logic lc_done_q;
  logic lc_idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_sync_regs
    if (!rst_ni) begin
      lc_done_q <= 1'b0;
      lc_idle_q <= 1'b0;
    end else begin
      lc_done_q <= lc_done_d;
      lc_idle_q <= lc_idle_d;
    end
  end

  assign pwr_lc_o.lc_done = lc_done_q;
  assign pwr_lc_o.lc_idle = lc_idle_q;

  ////////////////////
  // KMAC Interface //
  ////////////////////

  logic token_hash_req, token_hash_req_chk, token_hash_ack, token_hash_err, token_if_fsm_err;
  lc_token_t hashed_token;
  lc_ctrl_kmac_if u_lc_ctrl_kmac_if (
    .clk_i,
    .rst_ni,
    .clk_kmac_i           (clk_i),
    .rst_kmac_ni          (rst_ni),
    .kmac_data_i,
    .kmac_data_o,
    .transition_token_i   ( transition_token_q ),
    .token_hash_req_i     ( token_hash_req     ),
    .token_hash_req_chk_i ( token_hash_req_chk ),
    .token_hash_ack_o     ( token_hash_ack     ),
    .token_hash_err_o     ( token_hash_err     ),
    .token_if_fsm_err_o   ( token_if_fsm_err   ),
    .hashed_token_o       ( hashed_token       )
  );

  ////////////
  // LC FSM //
  ////////////

  lc_ctrl_fsm #(
    .RndCnstLcKeymgrDivInvalid     ( RndCnstLcKeymgrDivInvalid      ),
    .RndCnstLcKeymgrDivTestUnlocked( RndCnstLcKeymgrDivTestUnlocked ),
    .RndCnstLcKeymgrDivDev         ( RndCnstLcKeymgrDivDev          ),
    .RndCnstLcKeymgrDivProduction  ( RndCnstLcKeymgrDivProduction   ),
    .RndCnstLcKeymgrDivRma         ( RndCnstLcKeymgrDivRma          ),
    .RndCnstInvalidTokens          ( RndCnstInvalidTokens           ),
    .SecVolatileRawUnlockEn        ( SecVolatileRawUnlockEn         )
  ) u_lc_ctrl_fsm (
    .clk_i,
    .rst_ni,
    .Allow_RMA_or_SCRAP_on_PPD,
    .init_req_i             ( lc_init                          ),
    .init_done_o            ( lc_done_d                        ),
    .idle_o                 ( lc_idle_d                        ),
    .esc_scrap_state0_i     ( esc_scrap_state0                 ),
    .esc_scrap_state1_i     ( esc_scrap_state1                 ),
    .lc_state_valid_i       ( otp_lc_data_i.valid              ),
    .lc_state_i             ( lc_state_e'(otp_lc_data_i.state) ),
    .secrets_valid_i        ( otp_lc_data_i.secrets_valid      ),
    .lc_cnt_i               ( lc_cnt_e'(otp_lc_data_i.count)   ),
    .use_ext_clock_i        ( use_ext_clock_q                  ),
    .ext_clock_switched_o   ( ext_clock_switched               ),
    .volatile_raw_unlock_i  ( volatile_raw_unlock_q            ),
    // .strap_en_override_o,
    .test_unlock_token_i    ( otp_lc_data_i.test_unlock_token  ),
    .test_exit_dev_token_i      ( otp_lc_data_i.test_exit_dev_token    ),
    .dev_exit_prod_token_i      ( otp_lc_data_i.dev_exit_prod_token    ),
    .prod_exit_prodend_token_i      ( otp_lc_data_i.prod_exit_prodend_token    ),
    .test_tokens_valid_i    ( otp_lc_data_i.test_tokens_valid  ),
    .rma_token_i            ( otp_lc_data_i.rma_token          ),
    .rma_token_valid_i      ( otp_lc_data_i.rma_token_valid    ),
    .trans_cmd_i            ( transition_cmd                   ),
    .trans_target_i         ( transition_target_q              ),
    .dec_lc_state_o         ( dec_lc_state                     ),
    .dec_lc_cnt_o           ( dec_lc_cnt                       ),
    .dec_lc_id_state_o      ( dec_lc_id_state                  ),
    .token_hash_req_o       ( token_hash_req                   ),
    .token_hash_req_chk_o   ( token_hash_req_chk               ),
    .token_hash_ack_i       ( token_hash_ack                   ),
    .token_hash_err_i       ( token_hash_err                   ),
    .token_if_fsm_err_i     ( token_if_fsm_err                 ),
    .hashed_token_i         ( hashed_token                     ),
    .unhashed_token_i       ( transition_token_q               ),
    .otp_prog_req_o         ( lc_otp_program_o.req             ),
    .otp_prog_lc_state_o    ( lc_otp_program_o.state           ),
    .otp_prog_lc_cnt_o      ( lc_otp_program_o.count           ),
    .otp_prog_ack_i         ( lc_otp_program_i.ack             ),
    .otp_prog_err_i         ( lc_otp_program_i.err             ),
    .trans_success_o        ( trans_success_d                  ),
    .trans_cnt_oflw_error_o ( trans_cnt_oflw_error_d           ),
    .trans_invalid_error_o  ( trans_invalid_error_d            ),
    .token_invalid_error_o  ( token_invalid_error_d            ),
    .flash_rma_error_o      ( flash_rma_error_d                ),
    .otp_prog_error_o       ( otp_prog_error_d                 ),
    .state_invalid_error_o  ( state_invalid_error_d            ),
    .lc_raw_test_rma_o      ( lc_raw_test_rma                  ),
    .lc_dft_en_o,
    .lc_nvm_debug_en_o,
    .lc_hw_debug_en_o,
    .lc_cpu_en_o,
    .lc_creator_seed_sw_rw_en_o,
    .lc_owner_seed_sw_rw_en_o,
    .lc_iso_part_sw_rd_en_o,
    .lc_iso_part_sw_wr_en_o,
    .lc_seed_hw_rd_en_o,
    .lc_keymgr_en_o,
    .lc_escalate_en_o,
    .lc_check_byp_en_o,
    .lc_clk_byp_req_o,
    .lc_clk_byp_ack_i,
    .lc_flash_rma_req_o,
    .lc_flash_rma_ack_i,
    .lc_keymgr_div_o
  );

  ////////////////
  // Assertions //
  ////////////////

  //`CALIPTRA_ASSERT_KNOWN(AlertTxKnown_A,         alert_tx_o                 ) // -> NOTE: Removed since we do not use this port anymore
  `CALIPTRA_ASSERT_KNOWN(PwrLcKnown_A,           pwr_lc_o                   )
  `CALIPTRA_ASSERT_KNOWN(LcOtpProgramKnown_A,    lc_otp_program_o           )
  `CALIPTRA_ASSERT_KNOWN(LcOtpTokenKnown_A,      kmac_data_o                )
  `CALIPTRA_ASSERT_KNOWN(LcDftEnKnown_A,         lc_dft_en_o                )
  `CALIPTRA_ASSERT_KNOWN(LcNvmDebugEnKnown_A,    lc_nvm_debug_en_o          )
  `CALIPTRA_ASSERT_KNOWN(LcHwDebugEnKnown_A,     lc_hw_debug_en_o           )
  `CALIPTRA_ASSERT_KNOWN(LcCpuEnKnown_A,         lc_cpu_en_o                )
  `CALIPTRA_ASSERT_KNOWN(LcCreatorSwRwEn_A,      lc_creator_seed_sw_rw_en_o )
  `CALIPTRA_ASSERT_KNOWN(LcOwnerSwRwEn_A,        lc_owner_seed_sw_rw_en_o   )
  `CALIPTRA_ASSERT_KNOWN(LcIsoSwRwEn_A,          lc_iso_part_sw_rd_en_o     )
  `CALIPTRA_ASSERT_KNOWN(LcIsoSwWrEn_A,          lc_iso_part_sw_wr_en_o     )
  `CALIPTRA_ASSERT_KNOWN(LcSeedHwRdEn_A,         lc_seed_hw_rd_en_o         )
  `CALIPTRA_ASSERT_KNOWN(LcKeymgrEnKnown_A,      lc_keymgr_en_o             )
  `CALIPTRA_ASSERT_KNOWN(LcEscalateEnKnown_A,    lc_escalate_en_o           )
  `CALIPTRA_ASSERT_KNOWN(LcCheckBypassEnKnown_A, lc_check_byp_en_o          )
  `CALIPTRA_ASSERT_KNOWN(LcClkBypReqKnown_A,     lc_clk_byp_req_o           )
  `CALIPTRA_ASSERT_KNOWN(LcFlashRmaSeedKnown_A,  lc_flash_rma_seed_o        )
  `CALIPTRA_ASSERT_KNOWN(LcFlashRmaReqKnown_A,   lc_flash_rma_req_o         )
  `CALIPTRA_ASSERT_KNOWN(LcKeymgrDiv_A,          lc_keymgr_div_o            )

  
  
// ------------------------------------------------------------------------------------------
// NOTE: Assertions have been updated since Caliptra-SS changed the alert and escalation
// signals
  
  caliptra_prim_alert_pkg::alert_tx_t state_alert;
  caliptra_prim_alert_pkg::alert_tx_t program_alert;

  always_comb begin
    if (fatal_state_error_q) begin
      state_alert.alert_p = 1'b1;
      state_alert.alert_n = 1'b0;
    end else begin
      state_alert.alert_p = 1'b0;
      state_alert.alert_n = 1'b1;
    end
    if (fatal_prog_error_q) begin
      program_alert.alert_p = 1'b1;
      program_alert.alert_n = 1'b0;
    end else begin
      program_alert.alert_p = 1'b0;
      program_alert.alert_n = 1'b1;
    end
  end

  // Alert assertions for sparse FSMs.
  // `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcFsmCheck_A,
  //     u_lc_ctrl_fsm.u_fsm_state_regs, alert_tx_o[1])
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcFsmCheck_A,
      u_lc_ctrl_fsm.u_fsm_state_regs, state_alert)
  // `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcStateCheck_A,
  //     u_lc_ctrl_fsm.u_state_regs, alert_tx_o[1],
  //     !$past(otp_lc_data_i.valid) ||
  //     u_lc_ctrl_fsm.fsm_state_q inside {ResetSt, EscalateSt, PostTransSt, InvalidSt, ScrapSt} ||
  //     u_lc_ctrl_fsm.esc_scrap_state0_i ||
  //     u_lc_ctrl_fsm.esc_scrap_state1_i)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcStateCheck_A,
      u_lc_ctrl_fsm.u_state_regs, state_alert,
      !$past(otp_lc_data_i.valid) ||
      u_lc_ctrl_fsm.fsm_state_q inside {ResetSt, EscalateSt, PostTransSt, InvalidSt, ScrapSt} ||
      u_lc_ctrl_fsm.esc_scrap_state0_i ||
      u_lc_ctrl_fsm.esc_scrap_state1_i)
  // `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcCntCheck_A,
  //     u_lc_ctrl_fsm.u_cnt_regs, alert_tx_o[1],
  //      !$past(otp_lc_data_i.valid) ||
  //     u_lc_ctrl_fsm.fsm_state_q inside {ResetSt, EscalateSt, PostTransSt, InvalidSt, ScrapSt} ||
  //     u_lc_ctrl_fsm.esc_scrap_state0_i ||
  //     u_lc_ctrl_fsm.esc_scrap_state1_i)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlLcCntCheck_A,
      u_lc_ctrl_fsm.u_cnt_regs, state_alert,
       !$past(otp_lc_data_i.valid) ||
      u_lc_ctrl_fsm.fsm_state_q inside {ResetSt, EscalateSt, PostTransSt, InvalidSt, ScrapSt} ||
      u_lc_ctrl_fsm.esc_scrap_state0_i ||
      u_lc_ctrl_fsm.esc_scrap_state1_i)
  //  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlKmacIfFsmCheck_A,
  //       u_lc_ctrl_kmac_if.u_state_regs, alert_tx_o[1],
  //       u_lc_ctrl_fsm.fsm_state_q inside {EscalateSt} ||
  //       u_lc_ctrl_fsm.esc_scrap_state0_i ||
  //       u_lc_ctrl_fsm.esc_scrap_state1_i)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(CtrlKmacIfFsmCheck_A,
      u_lc_ctrl_kmac_if.u_state_regs, state_alert,
      u_lc_ctrl_fsm.fsm_state_q inside {EscalateSt} ||
      u_lc_ctrl_fsm.esc_scrap_state0_i ||
      u_lc_ctrl_fsm.esc_scrap_state1_i)

  // Alert assertions for reg_we onehot check
  // `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A, u_reg, alert_tx_o[2])
  // `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(TapDmiWeOnehotCheck_A,
  //                                                u_reg_tap_dmi, alert_tx_o[2], 0)
  `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A, u_reg, program_alert)
  `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(TapDmiWeOnehotCheck_A,
                                                 u_reg_tap, program_alert, 0)

// ------------------------------------------------------------------------------------------
  
endmodule : lc_ctrl
