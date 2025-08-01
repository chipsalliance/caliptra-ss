// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// OTP Controller top.
//

`include "caliptra_prim_assert.sv"
`include "caliptra_ss_prim_assert_sec_cm.svh"

module otp_ctrl
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
  import axi_pkg::*;
#(
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Compile time random constants, to be overriden by topgen.
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter scrmbl_key_init_t RndCnstScrmblKeyInit = RndCnstScrmblKeyInitDefault,
  // Hexfile file to initialize the OTP macro.
  // Note that the hexdump needs to account for ECC.
  parameter MemInitFile = ""
) (
  // OTP clock
  input                                              clk_i,
  input                                              rst_ni,
  // This is a command to zeroize the secrets in run-time
  input                                              FIPS_ZEROIZATION_CMD_i,
  input logic [31:0] cptra_ss_strap_mcu_lsu_axi_user_i,
  input logic [31:0] cptra_ss_strap_cptra_axi_user_i,
  input axi_struct_pkg::axi_wr_req_t                  core_axi_wr_req,
  output axi_struct_pkg::axi_wr_rsp_t                 core_axi_wr_rsp,
  input axi_struct_pkg::axi_rd_req_t                  core_axi_rd_req,
  output axi_struct_pkg::axi_rd_rsp_t                 core_axi_rd_rsp,

  input  tlul_pkg::tl_h2d_t                          prim_tl_i,
  output tlul_pkg::tl_d2h_t                          prim_tl_o,

  input prim_generic_otp_outputs_t                  prim_generic_otp_outputs_i,
  output prim_generic_otp_inputs_t                  prim_generic_otp_inputs_o,

  // Interrupt Requests
  output logic                                       intr_otp_operation_done_o,
  output logic                                       intr_otp_error_o,
  // Alerts
  // input  caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  // output caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
  // Caliptra-SS does not use alert sender. It directs alerts to MCI.
  output  [NumAlerts-1:0] alerts,
  // Power manager interface (inputs are synced to OTP clock domain)
  input  pwrmgr_pkg::pwr_otp_req_t                   pwr_otp_i,
  output pwrmgr_pkg::pwr_otp_rsp_t                   pwr_otp_o,
  // Macro-specific test registers going to lifecycle TAP
  input  lc_otp_vendor_test_req_t                    lc_otp_vendor_test_i,
  output lc_otp_vendor_test_rsp_t                    lc_otp_vendor_test_o,
  // Lifecycle transition command interface
  input  lc_otp_program_req_t                        lc_otp_program_i,
  output lc_otp_program_rsp_t                        lc_otp_program_o,
  // Lifecycle broadcast inputs
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input  lc_ctrl_pkg::lc_tx_t                        lc_creator_seed_sw_rw_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_owner_seed_sw_rw_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_seed_hw_rd_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_check_byp_en_i,
  // OTP broadcast outputs
  // SEC_CM: TOKEN_VALID.CTRL.MUBI
  output otp_lc_data_t                               otp_lc_data_o,

  // Hardware config bits
  output otp_broadcast_t                             otp_broadcast_o,
  // Scan
  input caliptra_prim_mubi_pkg::mubi4_t                       scanmode_i,
  // Test-related GPIO output
  output logic [OtpTestVectWidth-1:0]                cio_test_o,
  output logic [OtpTestVectWidth-1:0]                cio_test_en_o
);

  import caliptra_prim_mubi_pkg::*;
  import caliptra_prim_util_pkg::vbits;

  // Core AXI2TLUL interface signals
  tlul_pkg::tl_h2d_t      core_tl_i;
  tlul_pkg::tl_d2h_t      core_tl_o;

  axi_if #(
    .AW(axi_struct_pkg::TLUL_AXI_STRUCT_ADDR_WIDTH),
    .DW(32                                        ),
    .UW(axi_struct_pkg::TLUL_AXI_STRUCT_USER_WIDTH),
    .IW(axi_struct_pkg::TLUL_AXI_STRUCT_ID_WIDTH  )
  ) core_axi_if(
    .clk(clk_i),
    .rst_n(rst_ni)
  );

  assign core_axi_if.awaddr      = core_axi_wr_req.awaddr;
  assign core_axi_if.awburst     = core_axi_wr_req.awburst;
  assign core_axi_if.awsize      = core_axi_wr_req.awsize;
  assign core_axi_if.awlen       = core_axi_wr_req.awlen;
  assign core_axi_if.awuser      = core_axi_wr_req.awuser;
  assign core_axi_if.awid        = core_axi_wr_req.awid;
  assign core_axi_if.awlock      = core_axi_wr_req.awlock;
  assign core_axi_if.awvalid     = core_axi_wr_req.awvalid;
  assign core_axi_wr_rsp.awready = core_axi_if.awready;

  assign core_axi_if.wdata       = core_axi_wr_req.wdata;
  assign core_axi_if.wuser       = '0; 
  assign core_axi_if.wstrb       = core_axi_wr_req.wstrb;
  assign core_axi_if.wlast       = core_axi_wr_req.wlast;
  assign core_axi_if.wvalid      = core_axi_wr_req.wvalid;
  assign core_axi_wr_rsp.wready  = core_axi_if.wready;

  assign core_axi_wr_rsp.bresp   = core_axi_if.bresp;
  assign core_axi_wr_rsp.bid     = core_axi_if.bid;
  assign core_axi_wr_rsp.bvalid  = core_axi_if.bvalid;
  assign core_axi_if.bready      = core_axi_wr_req.bready;

  assign core_axi_if.araddr      = core_axi_rd_req.araddr;
  assign core_axi_if.arburst     = core_axi_rd_req.arburst;
  assign core_axi_if.arsize      = core_axi_rd_req.arsize;
  assign core_axi_if.arlen       = core_axi_rd_req.arlen;
  assign core_axi_if.aruser      = core_axi_rd_req.aruser;
  assign core_axi_if.arid        = core_axi_rd_req.arid;
  assign core_axi_if.arlock      = core_axi_rd_req.arlock;
  assign core_axi_if.arvalid     = core_axi_rd_req.arvalid;
  assign core_axi_rd_rsp.arready      = core_axi_if.arready;

  assign core_axi_rd_rsp.rdata   = core_axi_if.rdata;
  assign core_axi_rd_rsp.rresp   = core_axi_if.rresp;
  assign core_axi_rd_rsp.rid     = core_axi_if.rid;
  assign core_axi_rd_rsp.rlast   = core_axi_if.rlast;
  assign core_axi_rd_rsp.rvalid  = core_axi_if.rvalid;
  assign core_axi_if.rready      = core_axi_rd_req.rready;

  // Core AXI2TLUL instance
  axi2tlul #(
      .AW     (axi_struct_pkg::TLUL_AXI_STRUCT_ADDR_WIDTH),
      .DW     (32                                        ),
      .UW     (axi_struct_pkg::TLUL_AXI_STRUCT_USER_WIDTH),
      .IW     (axi_struct_pkg::TLUL_AXI_STRUCT_ID_WIDTH  )
  ) u_core_axi2tlul (
      .clk            (clk_i),
      .rst_n          (rst_ni),
      .s_axi_w_if     (core_axi_if.w_sub),
      .s_axi_r_if     (core_axi_if.r_sub),
      .tl_o           (core_tl_i),
      .tl_i           (core_tl_o)
  );

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  // This ensures that we can transfer scrambler data blocks in and out of OTP atomically.
  `CALIPTRA_ASSERT_INIT(OtpIfWidth_A, OtpIfWidth == ScrmblBlockWidth)

  // These error codes need to be identical.
  `CALIPTRA_ASSERT_INIT(ErrorCodeWidth_A, OtpErrWidth == caliptra_prim_otp_pkg::ErrWidth)
  `CALIPTRA_ASSERT_INIT(OtpErrorCode0_A,  int'(NoError) == int'(caliptra_prim_otp_pkg::NoError))
  `CALIPTRA_ASSERT_INIT(OtpErrorCode1_A,  int'(MacroError) == int'(caliptra_prim_otp_pkg::MacroError))
  `CALIPTRA_ASSERT_INIT(OtpErrorCode2_A,  int'(MacroEccCorrError) == int'(caliptra_prim_otp_pkg::MacroEccCorrError))
  `CALIPTRA_ASSERT_INIT(OtpErrorCode3_A,
               int'(MacroEccUncorrError) == int'(caliptra_prim_otp_pkg::MacroEccUncorrError))
  `CALIPTRA_ASSERT_INIT(OtpErrorCode4_A,
               int'(MacroWriteBlankError) == int'(caliptra_prim_otp_pkg::MacroWriteBlankError))

  /////////////
  // Regfile //
  /////////////

  // We have one CSR node, one functional TL-UL window and a gate module for that window
  logic [2:0] intg_error;

  tlul_pkg::tl_h2d_t tl_win_h2d;
  tlul_pkg::tl_d2h_t tl_win_d2h;

  otp_ctrl_reg_pkg::otp_ctrl_core_reg2hw_t reg2hw;
  otp_ctrl_reg_pkg::otp_ctrl_core_hw2reg_t hw2reg;

  // SEC_CM: DIRECT_ACCESS.CONFIG.REGWEN, CHECK_TRIGGER.CONFIG.REGWEN, CHECK.CONFIG.REGWEN
  otp_ctrl_core_reg_top u_reg_core (
    .clk_i,
    .rst_ni,
    .tl_i      ( core_tl_i     ),
    .tl_o      ( core_tl_o     ),
    .tl_win_o  ( tl_win_h2d    ),
    .tl_win_i  ( tl_win_d2h    ),
    .reg2hw    ( reg2hw        ),
    .hw2reg    ( hw2reg        ),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o( intg_error[0] )
  );

  ///////////////////////////////////////
  // Life Cycle Signal Synchronization //
  ///////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t       lc_creator_seed_sw_rw_en, lc_owner_seed_sw_rw_en,
                             lc_seed_hw_rd_en, lc_check_byp_en;
  lc_ctrl_pkg::lc_tx_t [2:0] lc_dft_en;
  // NumAgents + lfsr timer and scrambling datapath.
  lc_ctrl_pkg::lc_tx_t [NumAgentsIdx+1:0] lc_escalate_en, lc_escalate_en_synced;
  // Single wire for gating assertions in arbitration and CDC primitives.
  logic lc_escalate_en_any;

  caliptra_prim_lc_sync #(
    .NumCopies(NumAgentsIdx+2)
  ) u_prim_lc_sync_escalate_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en_i),
    .lc_en_o(lc_escalate_en_synced)
  );

  caliptra_prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_creator_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_creator_seed_sw_rw_en_i),
    .lc_en_o({lc_creator_seed_sw_rw_en})
  );

  caliptra_prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_owner_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_owner_seed_sw_rw_en_i),
    .lc_en_o({lc_owner_seed_sw_rw_en})
  );

  caliptra_prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_seed_hw_rd_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_seed_hw_rd_en_i),
    .lc_en_o({lc_seed_hw_rd_en})
  );

  caliptra_prim_lc_sync #(
    .NumCopies(3)
  ) u_prim_lc_sync_dft_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_dft_en_i),
    .lc_en_o(lc_dft_en)
  );

  caliptra_prim_lc_sync #(
    .NumCopies(1)
  ) u_prim_lc_sync_check_byp_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_check_byp_en_i),
    .lc_en_o({lc_check_byp_en})
  );

  /////////////////////////////////////
  // TL-UL SW partition select logic //
  /////////////////////////////////////

  // The SW partitions share the same TL-UL adapter.
  logic tlul_req, tlul_gnt, tlul_rvalid;
  logic [SwWindowAddrWidth-1:0] tlul_addr;
  logic [1:0]  tlul_rerror;
  logic [31:0] tlul_rdata;

  import caliptra_prim_mubi_pkg::MuBi4False;
  tlul_adapter_sram #(
    .SramAw      ( SwWindowAddrWidth ),
    .SramDw      ( 32 ),
    .Outstanding ( 1  ),
    .ByteAccess  ( 0  ),
    .ErrOnWrite  ( 1  ) // No write accesses allowed here.
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .en_ifetch_i                ( MuBi4False         ),
    .tl_i                       ( tl_win_h2d         ),
    .tl_o                       ( tl_win_d2h         ),
    .req_o                      (  tlul_req          ),
    .gnt_i                      (  tlul_gnt          ),
    .we_o                       (                    ), // unused
    .addr_o                     (  tlul_addr         ),
    .wdata_o                    (                    ), // unused
    .wmask_o                    (                    ), // unused
    // SEC_CM: BUS.INTEGRITY
    .intg_error_o               (  intg_error[1]     ),
    .rdata_i                    (  tlul_rdata        ),
    .rvalid_i                   (  tlul_rvalid       ),
    .rerror_i                   (  tlul_rerror       ),
    .req_type_o                 (                    ),
    .compound_txn_in_progress_o (                    ),
    .readback_en_i              ( MuBi4False         ),
    .readback_error_o           (                    ),
    .wr_collision_i             ( 1'b0               ),
    .write_pending_i            ( 1'b0               )
  );

  logic [NumPart-1:0] tlul_part_sel_oh;
  for (genvar k = 0; k < NumPart; k++) begin : gen_part_sel
    localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(PartInfo[k].offset) +
                                                    (OtpByteAddrWidth+1)'(PartInfo[k].size);
    if (PartInfo[k].offset == 0) begin : gen_zero_offset
      assign tlul_part_sel_oh[k] = ({1'b0, {tlul_addr, 2'b00}} < PartEnd);
    end else begin : gen_nonzero_offset
      assign tlul_part_sel_oh[k] = ({tlul_addr, 2'b00} >= PartInfo[k].offset) &
                                   ({1'b0, {tlul_addr, 2'b00}} < PartEnd);
    end
  end

  `CALIPTRA_ASSERT(PartSelMustBeOnehot_A, $onehot0(tlul_part_sel_oh))

  logic [NumPartWidth-1:0] tlul_part_idx;
  caliptra_prim_arbiter_fixed #(
    .N(NumPart),
    .EnDataPort(0)
  ) u_part_sel_idx (
    .clk_i,
    .rst_ni,
    .req_i   ( tlul_part_sel_oh  ),
    .data_i  ( '{default: '0}    ),
    .gnt_o   (                   ), // unused
    .idx_o   ( tlul_part_idx     ),
    .valid_o (                   ), // unused
    .data_o  (                   ), // unused
    .ready_i ( 1'b0              )
  );

  logic tlul_oob_err_d, tlul_oob_err_q;
  logic [NumPart-1:0] part_tlul_req, part_tlul_gnt, part_tlul_rvalid;
  logic [SwWindowAddrWidth-1:0] part_tlul_addr;
  logic [NumPart-1:0][1:0]  part_tlul_rerror;
  logic [NumPart-1:0][31:0] part_tlul_rdata;

  always_comb begin : p_tlul_assign
    // Send request to the correct partition.
    part_tlul_addr   = tlul_addr;
    part_tlul_req    = '0;
    tlul_oob_err_d   = 1'b0;
    if (tlul_req) begin
      if (tlul_part_sel_oh != '0) begin
        part_tlul_req[tlul_part_idx] = 1'b1;
      end else begin
        // Error out in the next cycle if address was out of bounds.
        tlul_oob_err_d = 1'b1;
      end
    end

    // aggregate TL-UL responses
    tlul_gnt         = |part_tlul_gnt    | tlul_oob_err_q;
    tlul_rvalid      = |part_tlul_rvalid | tlul_oob_err_q;
    tlul_rerror      = '0;
    tlul_rdata       = '0;
    for (int k = 0; k < NumPart; k++) begin
      tlul_rerror |= part_tlul_rerror[k];
      tlul_rdata  |= part_tlul_rdata[k];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlul_reg
    if (!rst_ni) begin
      tlul_oob_err_q <= 1'b0;
    end else begin
      tlul_oob_err_q <= tlul_oob_err_d;
    end
  end

  //////////////////////////////
  // Access Defaults and CSRs //
  //////////////////////////////

  dai_cmd_e                     dai_cmd;
  logic [OtpByteAddrWidth-1:0]  dai_addr;

  logic [lc_ctrl_state_pkg::DecLcStateWidth-1:0] lc_state_idx;

  // SEC_CM: ACCESS.CTRL.MUBI
  part_access_t [NumPart-1:0] part_access_pre, part_access;
  always_comb begin : p_access_control
    // Assigns default and extracts named CSR read enables for SW_CFG partitions.
    // SEC_CM: PART.MEM.REGREN
    part_access_pre = named_part_access_pre(reg2hw);

    // Permanently lock DAI write and read access to the life cycle partition.
    // The LC partition can only be read from and written to via the LC controller.
    // SEC_CM: LC_PART.MEM.SW_NOACCESS
    part_access_pre[LifeCycleIdx].write_lock = MuBi8True;
    part_access_pre[LifeCycleIdx].read_lock = MuBi8True;

    // Intercept write requests to the `VENDOR_HASHES_PROD` partition and verify
    // the write is allowed by the volatile lock of the `VENDOR_PK_HASH_VOLATILE LOCK` register.
    if (NumVendorPkFuses > 1) begin
      if (dai_cmd == DaiWrite && reg2hw.vendor_pk_hash_volatile_lock != '0 &&
          dai_addr >= ProdVendorHashStart &&
          dai_addr < ProdVendorHashEnd) begin
        if (32'(dai_addr) >= (ProdVendorHashStart + ((reg2hw.vendor_pk_hash_volatile_lock-1) * ProdVendorHashSize))) begin
          part_access_pre[VendorHashesProdPartitionIdx].write_lock = MuBi8True;
        end
      end
    end

    // XXX: Maybe encode the LC state index directly into the LC partition
    // instead of decoding it on-the-fly.
    unique case (otp_lc_data_o.state)
      lc_ctrl_state_pkg::LcStRaw:           lc_state_idx = 0;
      lc_ctrl_state_pkg::LcStTestUnlocked0: lc_state_idx = 1;
      lc_ctrl_state_pkg::LcStTestLocked0:   lc_state_idx = 2;
      lc_ctrl_state_pkg::LcStTestUnlocked1: lc_state_idx = 3;
      lc_ctrl_state_pkg::LcStTestLocked1:   lc_state_idx = 4;
      lc_ctrl_state_pkg::LcStTestUnlocked2: lc_state_idx = 5;
      lc_ctrl_state_pkg::LcStTestLocked2:   lc_state_idx = 6;
      lc_ctrl_state_pkg::LcStTestUnlocked3: lc_state_idx = 7;
      lc_ctrl_state_pkg::LcStTestLocked3:   lc_state_idx = 8;
      lc_ctrl_state_pkg::LcStTestUnlocked4: lc_state_idx = 9;
      lc_ctrl_state_pkg::LcStTestLocked4:   lc_state_idx = 10;
      lc_ctrl_state_pkg::LcStTestUnlocked5: lc_state_idx = 11;
      lc_ctrl_state_pkg::LcStTestLocked5:   lc_state_idx = 12;
      lc_ctrl_state_pkg::LcStTestUnlocked6: lc_state_idx = 13;
      lc_ctrl_state_pkg::LcStTestLocked6:   lc_state_idx = 14;
      lc_ctrl_state_pkg::LcStTestUnlocked7: lc_state_idx = 15;
      lc_ctrl_state_pkg::LcStDev:           lc_state_idx = 16;
      lc_ctrl_state_pkg::LcStProd:          lc_state_idx = 17;
      lc_ctrl_state_pkg::LcStProdEnd:       lc_state_idx = 18;
      lc_ctrl_state_pkg::LcStRma:           lc_state_idx = 19;
      default:                              lc_state_idx = 20;
    endcase

    // Write-lock partitions whose LC phase has expired.
    for (int k = 0; k < NumPart-1; k++) begin
      if ((lc_state_idx == 0) || (lc_state_idx > PartInfo[k].lc_phase)) begin
        part_access_pre[k].write_lock = MuBi8True;
      end
    end

  end

  // This prevents the synthesis tool from optimizing the multibit signals.
  for (genvar k = 0; k < NumPart; k++) begin : gen_bufs
    caliptra_prim_mubi8_sender #(
      .AsyncOn(0)
    ) u_prim_mubi8_sender_write_lock (
      .clk_i,
      .rst_ni,
      .mubi_i(part_access_pre[k].write_lock),
      .mubi_o(part_access[k].write_lock)
    );
    caliptra_prim_mubi8_sender #(
      .AsyncOn(0)
    ) u_prim_mubi8_sender_read_lock (
      .clk_i,
      .rst_ni,
      .mubi_i(part_access_pre[k].read_lock),
      .mubi_o(part_access[k].read_lock)
    );
  end

  //////////////////////
  // DAI-related CSRs //
  //////////////////////

  logic                         dai_idle;
  logic                         dai_req;


  logic [NumDaiWords-1:0][31:0] dai_wdata, dai_rdata;
  logic direct_access_regwen_d, direct_access_regwen_q;

  // This is the HWEXT implementation of a RW0C regwen bit.
  assign direct_access_regwen_d = (reg2hw.direct_access_regwen.qe &&
                                   !reg2hw.direct_access_regwen.q) ? 1'b0 : direct_access_regwen_q;

  // Any write to this register triggers a DAI command.
  assign dai_req = reg2hw.direct_access_cmd.digest.qe |
                   reg2hw.direct_access_cmd.wr.qe  |
                   reg2hw.direct_access_cmd.rd.qe;

  assign dai_cmd = dai_cmd_e'({reg2hw.direct_access_cmd.digest.q,
                               reg2hw.direct_access_cmd.wr.q,
                               reg2hw.direct_access_cmd.rd.q});

  assign dai_addr  = reg2hw.direct_access_address.q;
  assign dai_wdata = reg2hw.direct_access_wdata;

  // The DAI and the LCI can initiate write transactions, which
  // are critical and we must not power down if such transactions
  // are pending. Hence, we signal the LCI/DAI idle state to the
  // power manager. This signal is flopped here as it has to
  // cross a clock boundary to the power manager.
  logic dai_prog_idle, lci_prog_idle, otp_idle_d, otp_idle_q;
  assign otp_idle_d = lci_prog_idle & dai_prog_idle;
  assign pwr_otp_o.otp_idle = otp_idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_idle_regwen_regs
    if (!rst_ni) begin
      otp_idle_q <= 1'b0;
      // The regwen bit has to reset to 1 so that CSR accesses are enabled by default.
      direct_access_regwen_q  <= 1'b1;
    end else begin
      otp_idle_q <= otp_idle_d;
      direct_access_regwen_q <= direct_access_regwen_d;
    end
  end

  //////////////////////////////////////
  // Ctrl/Status CSRs, Errors, Alerts //
  //////////////////////////////////////

  // Status and error reporting CSRs, error interrupt generation and alerts.
  otp_err_e [NumPart+1:0] part_error;
  logic [NumAgents-1:0] part_fsm_err;
  logic [NumPart+1:0] part_errors_reduced;
  logic otp_operation_done, otp_error;
  logic fatal_macro_error_d, fatal_macro_error_q;
  logic fatal_check_error_d, fatal_check_error_q;
  logic fatal_bus_integ_error_d, fatal_bus_integ_error_q;
  logic chk_pending, chk_timeout;
  logic lfsr_fsm_err, scrmbl_fsm_err;
  always_comb begin : p_errors_alerts
    // Note: since these are all fatal alert events, we latch them and keep on sending
    // alert events via the alert senders. These regs can only be cleared via a system reset.
    fatal_macro_error_d = fatal_macro_error_q;
    fatal_check_error_d = fatal_check_error_q;
    fatal_bus_integ_error_d = fatal_bus_integ_error_q | (|intg_error);
    // These are the per-partition buffered escalation inputs
    lc_escalate_en = lc_escalate_en_synced;
    // Need a single wire for gating assertions in arbitration and CDC primitives.
    lc_escalate_en_any = 1'b0;

    // Aggregate all the macro alerts from the partitions
    for (int k = 0; k < NumPart; k++) begin
      // Filter for critical error codes that should not occur in the field.
      fatal_macro_error_d |= part_error[k] == MacroError;
      // While uncorrectable ECC errors are always reported, they do not trigger a fatal alert
      // event in some partitions like the VENDOR_TEST partition.
      if (PartInfo[k].integrity) begin
        fatal_macro_error_d |= part_error[k] == MacroEccUncorrError;
      end
    end
    // Aggregate all the macro alerts from the DAI/LCI
    for (int k = NumPart; k < NumPart+2; k++) begin
      // Filter for critical error codes that should not occur in the field.
      fatal_macro_error_d |= part_error[k] inside {MacroError, MacroEccUncorrError};
    end

    // Aggregate all the remaining errors / alerts from the partitions and the DAI/LCI
    for (int k = 0; k < NumPart+2; k++) begin
      // Set the error bit if the error status of the corresponding partition is nonzero.
      // Need to reverse the order here since the field enumeration in hw2reg.status is reversed.
      part_errors_reduced[NumPart+1-k] = |part_error[k];
      // Filter for integrity and consistency check failures.
      fatal_check_error_d |= part_error[k] inside {CheckFailError, FsmStateError};

      // If a fatal alert has been observed in any of the partitions/FSMs,
      // we locally trigger escalation within OTP, which moves all FSMs
      // to a terminal error state.
      if (fatal_macro_error_q || fatal_check_error_q) begin
        lc_escalate_en[k] = lc_ctrl_pkg::On;
      end
      if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_escalate_en[k])) begin
        lc_escalate_en_any = 1'b1;
      end
    end

    // Errors from other non-partition FSMs.
    fatal_check_error_d |= chk_timeout       |
                           lfsr_fsm_err      |
                           scrmbl_fsm_err    |
                           (|part_fsm_err);
  end

  // If we got an error, we trigger an interrupt.
  logic [$bits(part_errors_reduced)+4-1:0] interrupt_triggers_d, interrupt_triggers_q;

  // This makes sure that interrupts are not sticky.
  assign interrupt_triggers_d = {
    part_errors_reduced,
    chk_timeout,
    lfsr_fsm_err,
    scrmbl_fsm_err,
    |part_fsm_err
  };

  assign otp_error = |(interrupt_triggers_d & ~interrupt_triggers_q);

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_alert_regs
    if (!rst_ni) begin
      fatal_macro_error_q     <= '0;
      fatal_check_error_q     <= '0;
      fatal_bus_integ_error_q <= '0;
      interrupt_triggers_q    <= '0;
    end else begin
      fatal_macro_error_q     <= fatal_macro_error_d;
      fatal_check_error_q     <= fatal_check_error_d;
      fatal_bus_integ_error_q <= fatal_bus_integ_error_d;
      interrupt_triggers_q    <= interrupt_triggers_d;
    end
  end

  // CSR assignments are done in one combo process so that we can use
  // the parameterized digest_assign task below without multiple driver issues.
  logic unused_part_digest;
  logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest;
  logic intr_state_otp_operation_done_d, intr_state_otp_operation_done_de;
  logic intr_state_otp_error_d, intr_state_otp_error_de;
  always_comb begin : p_csr_assign
    // Not all partition digests are consumed, and assigning them to an unused_* signal in the
    // function below does not seem to work for some linters.
    unused_part_digest = ^part_digest;
    // Assign named CSRs (like digests).
    hw2reg = named_reg_assign(part_digest);
    // DAI related CSRs
    hw2reg.direct_access_rdata = dai_rdata;
    // ANDing this state with dai_idle write-protects all DAI regs during pending operations.
    hw2reg.direct_access_regwen.d = direct_access_regwen_q & dai_idle;
    // Assign these to the status register.
    hw2reg.status = {part_errors_reduced,
                     chk_timeout,
                     lfsr_fsm_err,
                     scrmbl_fsm_err,
                    //  part_fsm_err[KdiIdx], //TODO: Removed this KdiIdx
                     fatal_bus_integ_error_q,
                     dai_idle,
                     chk_pending};
    // Error code registers.
    hw2reg.err_code = part_error;
    // Interrupt signals
    hw2reg.intr_state.otp_operation_done.de = intr_state_otp_operation_done_de;
    hw2reg.intr_state.otp_operation_done.d  = intr_state_otp_operation_done_d;
    hw2reg.intr_state.otp_error.de = intr_state_otp_error_de;
    hw2reg.intr_state.otp_error.d  = intr_state_otp_error_d;
end


  //////////////////////////////////
  // Interrupts and Alert Senders //
  //////////////////////////////////

  caliptra_prim_intr_hw #(
    .Width(1)
  ) u_intr_operation_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           ( otp_operation_done                      ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.otp_operation_done.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.otp_operation_done.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.otp_operation_done.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.otp_operation_done.q  ),
    .hw2reg_intr_state_de_o ( intr_state_otp_operation_done_de        ),
    .hw2reg_intr_state_d_o  ( intr_state_otp_operation_done_d         ),
    .intr_o                 ( intr_otp_operation_done_o               )
  );

  caliptra_prim_intr_hw #(
    .Width(1)
  ) u_intr_error (
    .clk_i,
    .rst_ni,
    .event_intr_i           ( otp_error                      ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.otp_error.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.otp_error.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.otp_error.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.otp_error.q  ),
    .hw2reg_intr_state_de_o ( intr_state_otp_error_de        ),
    .hw2reg_intr_state_d_o  ( intr_state_otp_error_d         ),
    .intr_o                 ( intr_otp_error_o               )
  );

  // logic [NumAlerts-1:0] alerts;
  logic [NumAlerts-1:0] alert_test;
  logic fatal_prim_otp_alert, recov_prim_otp_alert;

  assign alerts = {
    recov_prim_otp_alert,
    fatal_prim_otp_alert,
    fatal_bus_integ_error_q,
    fatal_check_error_q,
    fatal_macro_error_q
  };

  assign alert_test = {
    reg2hw.alert_test.recov_prim_otp_alert.q &
    reg2hw.alert_test.recov_prim_otp_alert.qe,
    reg2hw.alert_test.fatal_prim_otp_alert.q &
    reg2hw.alert_test.fatal_prim_otp_alert.qe,
    reg2hw.alert_test.fatal_bus_integ_error.q &
    reg2hw.alert_test.fatal_bus_integ_error.qe,
    reg2hw.alert_test.fatal_check_error.q &
    reg2hw.alert_test.fatal_check_error.qe,
    reg2hw.alert_test.fatal_macro_error.q &
    reg2hw.alert_test.fatal_macro_error.qe
  };

  localparam logic [NumAlerts-1:0] AlertIsFatal = {
    1'b0, // recov_prim_otp_alert
    1'b1, // fatal_prim_otp_alert
    1'b1, // fatal_bus_integ_error_q
    1'b1, // fatal_check_error_q
    1'b1  // fatal_macro_error_q
  };

  ////////////////////////////////
  // LFSR Timer and CSR mapping //
  ////////////////////////////////

  logic integ_chk_trig, cnsty_chk_trig;
  logic [NumPart-1:0] integ_chk_req, integ_chk_ack;
  logic [NumPart-1:0] cnsty_chk_req, cnsty_chk_ack;

  assign integ_chk_trig   = reg2hw.check_trigger.integrity.q &
                            reg2hw.check_trigger.integrity.qe;
  assign cnsty_chk_trig   = reg2hw.check_trigger.consistency.q &
                            reg2hw.check_trigger.consistency.qe;

  // SEC_CM: PART.DATA_REG.BKGN_CHK
  otp_ctrl_lfsr_timer #(
    .RndCnstLfsrSeed(RndCnstLfsrSeed),
    .RndCnstLfsrPerm(RndCnstLfsrPerm)
  ) u_otp_ctrl_lfsr_timer (
    .clk_i,
    .rst_ni,
    .edn_req_o          (                          ), 
    .edn_ack_i          ( '0                       ),
    .edn_data_i         ( '0                       ), 
    // We can enable the timer once OTP has initialized.
    // Note that this is only the initial release that gets
    // the timer FSM into an operational state.
    // Whether or not the timers / background checks are
    // activated depends on the CSR configuration (by default
    // they are switched off).
    .timer_en_i         ( pwr_otp_o.otp_done        ),
    // This idle signal is the same that is output to the power
    // manager, and indicates whether there is an ongoing OTP programming
    // operation. It is used to pause the consistency check timeout
    // counter in order to prevent spurious timeouts (OTP programming
    // operations are very slow compared to readout operations and can
    // hence interfere with the timeout mechanism).
    .otp_prog_busy_i    ( ~otp_idle_d               ),
    .integ_chk_trig_i   ( integ_chk_trig            ),
    .cnsty_chk_trig_i   ( cnsty_chk_trig            ),
    .chk_pending_o      ( chk_pending               ),
    .timeout_i          ( reg2hw.check_timeout.q    ),
    .integ_period_msk_i ( reg2hw.integrity_check_period.q   ),
    .cnsty_period_msk_i ( reg2hw.consistency_check_period.q ),
    .integ_chk_req_o    ( integ_chk_req             ),
    .cnsty_chk_req_o    ( cnsty_chk_req             ),
    .integ_chk_ack_i    ( integ_chk_ack             ),
    .cnsty_chk_ack_i    ( cnsty_chk_ack             ),
    .escalate_en_i      ( lc_escalate_en[NumAgents] ),
    .chk_timeout_o      ( chk_timeout               ),
    .fsm_err_o          ( lfsr_fsm_err              )
  );

  ///////////////////////////////
  // OTP Macro and Arbitration //
  ///////////////////////////////

  typedef struct packed {
    caliptra_prim_otp_pkg::cmd_e          cmd;
    logic [OtpSizeWidth-1:0]     size; // Number of native words to write.
    logic [OtpIfWidth-1:0]       wdata;
    logic [OtpAddrWidth-1:0]     addr; // Halfword address.
  } otp_bundle_t;

  logic [NumAgents-1:0]        part_otp_arb_req, part_otp_arb_gnt;
  otp_bundle_t                 part_otp_arb_bundle [NumAgents];
  logic                        otp_arb_valid, otp_arb_ready;
  logic                        otp_prim_valid, otp_prim_ready;
  logic                        otp_rsp_fifo_valid, otp_rsp_fifo_ready;
  logic [vbits(NumAgents)-1:0] otp_arb_idx;
  otp_bundle_t                 otp_arb_bundle;

  // The OTP interface is arbitrated on a per-cycle basis, meaning that back-to-back
  // transactions can be completely independent.
  caliptra_prim_arbiter_tree #(
    .N(NumAgents),
    .DW($bits(otp_bundle_t))
  ) u_otp_arb (
    .clk_i,
    .rst_ni,
    .req_chk_i ( ~lc_escalate_en_any ),
    .req_i     ( part_otp_arb_req    ),
    .data_i    ( part_otp_arb_bundle ),
    .gnt_o     ( part_otp_arb_gnt    ),
    .idx_o     ( otp_arb_idx         ),
    .valid_o   ( otp_arb_valid       ),
    .data_o    ( otp_arb_bundle      ),
    .ready_i   ( otp_arb_ready       )
  );

  // Don't issue more transactions than what the rsp_fifo can keep track of.
  assign otp_arb_ready      = otp_prim_ready & otp_rsp_fifo_ready;
  assign otp_prim_valid     = otp_arb_valid & otp_rsp_fifo_ready;
  assign otp_rsp_fifo_valid = otp_prim_ready & otp_prim_valid;

  caliptra_prim_otp_pkg::err_e          part_otp_err;
  logic [OtpIfWidth-1:0]       part_otp_rdata;
  logic                        otp_rvalid;
  tlul_pkg::tl_h2d_t           prim_tl_h2d_gated;
  tlul_pkg::tl_d2h_t           prim_tl_d2h_gated;

  // Life cycle qualification of TL-UL test interface.
  // SEC_CM: TEST.BUS.LC_GATED
  // SEC_CM: TEST_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate #(
    .NumGatesPerDirection(2)
  ) u_tlul_lc_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(prim_tl_i),
    .tl_d2h_o(prim_tl_o),
    .tl_h2d_o(prim_tl_h2d_gated),
    .tl_d2h_i(prim_tl_d2h_gated),
    .lc_en_i (lc_dft_en[0]),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o(),
    .err_o   (intg_error[2])
  );




  always_comb begin : FCM_port_assignment
    // Clock, reset and observability
    prim_generic_otp_inputs_o.clk_i      = clk_i;
    prim_generic_otp_inputs_o.rst_ni     = rst_ni;
    prim_generic_otp_inputs_o.obs_ctrl_i = '0;
    
    // Power sequencing signals
    prim_generic_otp_inputs_o.pwr_seq_h_i = '0;
    
    // Test interface signals
    lc_otp_vendor_test_o.status          = '0;
    prim_tl_d2h_gated                    = '0;
    
    // Other DFT signals
    prim_generic_otp_inputs_o.scanmode_i  = scanmode_i;
    prim_generic_otp_inputs_o.scan_en_i   = '0;
    prim_generic_otp_inputs_o.scan_rst_ni = '0;
    
    // Command interface (read/write)
    prim_generic_otp_inputs_o.valid_i  = otp_prim_valid;
    prim_generic_otp_inputs_o.size_i   = otp_arb_bundle.size;
    prim_generic_otp_inputs_o.cmd_i    = otp_arb_bundle.cmd;
    prim_generic_otp_inputs_o.addr_i   = otp_arb_bundle.addr;
    prim_generic_otp_inputs_o.wdata_i  = otp_arb_bundle.wdata;
    
    // Ready/Response signals
    otp_prim_ready      = prim_generic_otp_outputs_i.ready_o;
    otp_rvalid          = prim_generic_otp_outputs_i.valid_o;
    part_otp_rdata      = prim_generic_otp_outputs_i.rdata_o;
    part_otp_err        = prim_generic_otp_outputs_i.err_o;
    
    // Alert signals
    fatal_prim_otp_alert = prim_generic_otp_outputs_i.fatal_alert_o;
    recov_prim_otp_alert = prim_generic_otp_outputs_i.recov_alert_o;
  end
  


  logic otp_fifo_valid;
  logic [vbits(NumAgents)-1:0] otp_part_idx;
  logic [NumAgents-1:0] part_otp_rvalid;

  // We can have up to two OTP commands in flight, hence we size this to be 2 deep.
  // The partitions can unconditionally sink requested data.
  caliptra_prim_fifo_sync #(
    .Width(vbits(NumAgents)),
    .Depth(2)
  ) u_otp_rsp_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    ( 1'b0               ),
    .wvalid_i ( otp_rsp_fifo_valid ),
    .wready_o ( otp_rsp_fifo_ready ),
    .wdata_i  ( otp_arb_idx        ),
    .rvalid_o ( otp_fifo_valid     ),
    .rready_i ( otp_rvalid         ),
    .rdata_o  ( otp_part_idx       ),
    .depth_o  (                    ),
    .full_o   (                    ),
    .err_o    (                    )
  );

  // Steer response back to the partition where this request originated.
  always_comb begin : p_rvalid
    part_otp_rvalid = '0;
    part_otp_rvalid[otp_part_idx] = otp_rvalid & otp_fifo_valid;
  end

  // Note that this must be true by construction.
  `CALIPTRA_ASSERT(OtpRespFifoUnderflow_A, otp_rvalid |-> otp_fifo_valid)

  /////////////////////////////////////////
  // Scrambling Datapath and Arbitration //
  /////////////////////////////////////////

  // Note: as opposed to the OTP arbitration above, we do not perform cycle-wise arbitration, but
  // transaction-wise arbitration. This is implemented using a RR arbiter that acts as a mutex.
  // I.e., each agent (e.g. the DAI or a partition) can request a lock on the mutex. Once granted,
  // the partition can keep the lock as long as needed for the transaction to complete. The
  // partition must yield its lock by deasserting the request signal for the arbiter to proceed.
  // Since this scheme does not have built-in preemtion, it must be ensured that the agents
  // eventually release their locks for this to be fair.
  //
  // See also https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#block-diagram for details.
  typedef struct packed {
    otp_scrmbl_cmd_e             cmd;
    digest_mode_e                mode;
    logic [ConstSelWidth-1:0]    sel;
    logic [ScrmblBlockWidth-1:0] data;
    logic                        valid;
  } scrmbl_bundle_t;

  logic [NumAgents-1:0]        part_scrmbl_mtx_req, part_scrmbl_mtx_gnt;
  scrmbl_bundle_t              part_scrmbl_req_bundle [NumAgents];
  scrmbl_bundle_t              scrmbl_req_bundle;
  logic [vbits(NumAgents)-1:0] scrmbl_mtx_idx;
  logic                        scrmbl_mtx_valid;

  // Note that arbiter decisions do not change when backpressured.
  // Hence, the idx_o signal is guaranteed to remain stable until ack'ed.
  caliptra_prim_arbiter_tree #(
    .N(NumAgents),
    .DW($bits(scrmbl_bundle_t))
  ) u_scrmbl_mtx (
    .clk_i,
    .rst_ni,
    .req_chk_i ( 1'b0                   ), // REQ is allowed to go low again without ACK even
                                           // during normal operation.
    .req_i     ( part_scrmbl_mtx_req    ),
    .data_i    ( part_scrmbl_req_bundle ),
    .gnt_o     (                        ),
    .idx_o     ( scrmbl_mtx_idx         ),
    .valid_o   ( scrmbl_mtx_valid       ),
    .data_o    ( scrmbl_req_bundle      ),
    .ready_i   ( 1'b0                   )
  );

  // Since the ready_i signal of the arbiter is statically set to 1'b0 above, we are always in a
  // "backpressure" situation, where the RR arbiter will automatically advance the internal RR state
  // to give the current winner max priority in subsequent cycles in order to keep the decision
  // stable. Rearbitration occurs once the winning agent deasserts its request.
  always_comb begin : p_mutex
    part_scrmbl_mtx_gnt = '0;
    part_scrmbl_mtx_gnt[scrmbl_mtx_idx] = scrmbl_mtx_valid;
  end

  logic [ScrmblBlockWidth-1:0] part_scrmbl_rsp_data;
  logic scrmbl_arb_req_ready, scrmbl_arb_rsp_valid;
  logic [NumAgents-1:0] part_scrmbl_req_ready, part_scrmbl_rsp_valid;

  // SEC_CM: SECRET.MEM.SCRAMBLE
  // SEC_CM: PART.MEM.DIGEST
  otp_ctrl_scrmbl u_otp_ctrl_scrmbl (
    .clk_i,
    .rst_ni,
    .cmd_i         ( scrmbl_req_bundle.cmd       ),
    .mode_i        ( scrmbl_req_bundle.mode      ),
    .sel_i         ( scrmbl_req_bundle.sel       ),
    .data_i        ( scrmbl_req_bundle.data      ),
    .valid_i       ( scrmbl_req_bundle.valid     ),
    .ready_o       ( scrmbl_arb_req_ready        ),
    .data_o        ( part_scrmbl_rsp_data        ),
    .valid_o       ( scrmbl_arb_rsp_valid        ),
    .escalate_en_i ( lc_escalate_en[NumAgents+1] ),
    .fsm_err_o     ( scrmbl_fsm_err              )
  );

  // steer back responses
  always_comb begin : p_scmrbl_resp
    part_scrmbl_req_ready = '0;
    part_scrmbl_rsp_valid = '0;
    part_scrmbl_req_ready[scrmbl_mtx_idx] = scrmbl_arb_req_ready;
    part_scrmbl_rsp_valid[scrmbl_mtx_idx] = scrmbl_arb_rsp_valid;
  end

  /////////////////////////////
  // Direct Access Interface //
  /////////////////////////////

  logic                           part_init_req;
  logic [NumPart-1:0]             part_init_done;
  part_access_t [NumPart-1:0]     part_access_dai;

  // The init request comes from the power manager, which lives in the AON clock domain.
  logic pwr_otp_req_synced;
  caliptra_prim_flop_2sync #(
    .Width(1)
  ) u_otp_init_sync (
    .clk_i,
    .rst_ni,
    .d_i ( pwr_otp_i.otp_init ),
    .q_o ( pwr_otp_req_synced )
  );

  // Register this signal as it has to cross a clock boundary.
  logic pwr_otp_rsp_d, pwr_otp_rsp_q;
  assign pwr_otp_o.otp_done = pwr_otp_rsp_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_init_reg
    if (!rst_ni) begin
      pwr_otp_rsp_q <= 1'b0;
    end else begin
      pwr_otp_rsp_q <= pwr_otp_rsp_d;
    end
  end

  wire discarded_fuse_write, discard_fuse_write;

  fuse_ctrl_filter u_fuse_ctrl_filter (
    .clk_i                              (clk_i),
    .rst_n_i                            (rst_ni),
    .cptra_ss_strap_mcu_lsu_axi_user_i  (cptra_ss_strap_mcu_lsu_axi_user_i),
    .cptra_ss_strap_cptra_axi_user_i    (cptra_ss_strap_cptra_axi_user_i),
    .fc_init_done            (pwr_otp_rsp_d),
    .core_axi_wr_req         (core_axi_wr_req),
    .core_axi_wr_rsp         (core_axi_wr_rsp),
    .discarded_fuse_write_i  (discarded_fuse_write),
    .discard_fuse_write_o    (discard_fuse_write)
  );

  otp_ctrl_dai u_otp_ctrl_dai (
    .clk_i,
    .rst_ni,
    .discarded_fuse_write_o(discarded_fuse_write),
    .discard_fuse_write_i(discard_fuse_write),
    .init_req_i       ( pwr_otp_req_synced                    ),
    .init_done_o      ( pwr_otp_rsp_d                         ),
    .part_init_req_o  ( part_init_req                         ),
    .part_init_done_i ( part_init_done                        ),
    .escalate_en_i    ( lc_escalate_en[DaiIdx]                ),
    .error_o          ( part_error[DaiIdx]                    ),
    .fsm_err_o        ( part_fsm_err[DaiIdx]                  ),
    .part_access_i    ( part_access_dai                       ),
    .dai_addr_i       ( dai_addr                              ),
    .dai_cmd_i        ( dai_cmd                               ),
    .dai_req_i        ( dai_req                               ),
    .dai_wdata_i      ( dai_wdata                             ),
    .dai_idle_o       ( dai_idle                              ),
    .dai_prog_idle_o  ( dai_prog_idle                         ),
    .dai_cmd_done_o   ( otp_operation_done                    ),
    .dai_rdata_o      ( dai_rdata                             ),
    .otp_req_o        ( part_otp_arb_req[DaiIdx]              ),
    .otp_cmd_o        ( part_otp_arb_bundle[DaiIdx].cmd       ),
    .otp_size_o       ( part_otp_arb_bundle[DaiIdx].size      ),
    .otp_wdata_o      ( part_otp_arb_bundle[DaiIdx].wdata     ),
    .otp_addr_o       ( part_otp_arb_bundle[DaiIdx].addr      ),
    .otp_gnt_i        ( part_otp_arb_gnt[DaiIdx]              ),
    .otp_rvalid_i     ( part_otp_rvalid[DaiIdx]               ),
    .otp_rdata_i      ( part_otp_rdata                        ),
    .otp_err_i        ( part_otp_err                          ),
    .scrmbl_mtx_req_o ( part_scrmbl_mtx_req[DaiIdx]           ),
    .scrmbl_mtx_gnt_i ( part_scrmbl_mtx_gnt[DaiIdx]           ),
    .scrmbl_cmd_o     ( part_scrmbl_req_bundle[DaiIdx].cmd    ),
    .scrmbl_mode_o    ( part_scrmbl_req_bundle[DaiIdx].mode   ),
    .scrmbl_sel_o     ( part_scrmbl_req_bundle[DaiIdx].sel    ),
    .scrmbl_data_o    ( part_scrmbl_req_bundle[DaiIdx].data   ),
    .scrmbl_valid_o   ( part_scrmbl_req_bundle[DaiIdx].valid  ),
    .scrmbl_ready_i   ( part_scrmbl_req_ready[DaiIdx]         ),
    .scrmbl_valid_i   ( part_scrmbl_rsp_valid[DaiIdx]         ),
    .scrmbl_data_i    ( part_scrmbl_rsp_data                  )
  );

  ////////////////////////////////////
  // Lifecycle Transition Interface //
  ////////////////////////////////////

  logic [PartInfo[LifeCycleIdx].size-1:0][7:0] lc_otp_program_data;
  assign lc_otp_program_data[LcStateOffset-LifeCycleOffset +: LcStateSize] =
      lc_otp_program_i.state;
  assign lc_otp_program_data[LcTransitionCntOffset-LifeCycleOffset +: LcTransitionCntSize] =
      lc_otp_program_i.count;

  otp_ctrl_lci #(
    .Info(PartInfo[LifeCycleIdx])
  ) u_otp_ctrl_lci (
    .clk_i,
    .rst_ni,
    .lci_en_i         ( pwr_otp_o.otp_done                ),
    .escalate_en_i    ( lc_escalate_en[LciIdx]            ),
    .error_o          ( part_error[LciIdx]                ),
    .fsm_err_o        ( part_fsm_err[LciIdx]              ),
    .lci_prog_idle_o  ( lci_prog_idle                     ),
    .lc_req_i         ( lc_otp_program_i.req              ),
    .lc_data_i        ( lc_otp_program_data               ),
    .lc_ack_o         ( lc_otp_program_o.ack              ),
    .lc_err_o         ( lc_otp_program_o.err              ),
    .otp_req_o        ( part_otp_arb_req[LciIdx]          ),
    .otp_cmd_o        ( part_otp_arb_bundle[LciIdx].cmd   ),
    .otp_size_o       ( part_otp_arb_bundle[LciIdx].size  ),
    .otp_wdata_o      ( part_otp_arb_bundle[LciIdx].wdata ),
    .otp_addr_o       ( part_otp_arb_bundle[LciIdx].addr  ),
    .otp_gnt_i        ( part_otp_arb_gnt[LciIdx]          ),
    .otp_rvalid_i     ( part_otp_rvalid[LciIdx]           ),
    .otp_rdata_i      ( part_otp_rdata                    ),
    .otp_err_i        ( part_otp_err                      )
  );

  // Tie off unused connections.
  assign part_scrmbl_mtx_req[LciIdx]    = '0;
  assign part_scrmbl_req_bundle[LciIdx] = '0;

  // This stops lint from complaining about unused signals.
  logic unused_lci_scrmbl_sigs;
  assign unused_lci_scrmbl_sigs = ^{part_scrmbl_mtx_gnt[LciIdx],
                                    part_scrmbl_req_ready[LciIdx],
                                    part_scrmbl_rsp_valid[LciIdx]};

  /////////////////////////
  // Partition Instances //
  /////////////////////////

  logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data;

  for (genvar k = 0; k < NumPart; k ++) begin : gen_partitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    if (PartInfo[k].variant == Unbuffered) begin : gen_unbuffered
      otp_ctrl_part_unbuf #(
        .Info(PartInfo[k])
      ) u_part_unbuf (
        .clk_i,
        .rst_ni,
        .init_req_i    ( part_init_req                ),
        .init_done_o   ( part_init_done[k]            ),
        .escalate_en_i ( lc_escalate_en[k]            ),
        .error_o       ( part_error[k]                ),
        .fsm_err_o     ( part_fsm_err[k]              ),
        .access_i      ( part_access[k]               ),
        .access_o      ( part_access_dai[k]           ),
        .digest_o      ( part_digest[k]               ),
        .tlul_req_i    ( part_tlul_req[k]             ),
        .tlul_gnt_o    ( part_tlul_gnt[k]             ),
        .tlul_addr_i   ( part_tlul_addr               ),
        .tlul_rerror_o ( part_tlul_rerror[k]          ),
        .tlul_rvalid_o ( part_tlul_rvalid[k]          ),
        .tlul_rdata_o  ( part_tlul_rdata[k]           ),
        .otp_req_o     ( part_otp_arb_req[k]          ),
        .otp_cmd_o     ( part_otp_arb_bundle[k].cmd   ),
        .otp_size_o    ( part_otp_arb_bundle[k].size  ),
        .otp_wdata_o   ( part_otp_arb_bundle[k].wdata ),
        .otp_addr_o    ( part_otp_arb_bundle[k].addr  ),
        .otp_gnt_i     ( part_otp_arb_gnt[k]          ),
        .otp_rvalid_i  ( part_otp_rvalid[k]           ),
        .otp_rdata_i   ( part_otp_rdata               ),
        .otp_err_i     ( part_otp_err                 )
      );

      // Tie off unused connections.
      assign part_scrmbl_mtx_req[k]    = '0;
      assign part_scrmbl_req_bundle[k] = '0;
      // These checks do not exist in this partition type,
      // so we always acknowledge the request.
      assign integ_chk_ack[k]          = 1'b1;
      assign cnsty_chk_ack[k]          = 1'b1;

      // No buffered data to expose.
      assign part_buf_data[PartInfo[k].offset +: PartInfo[k].size] = '0;

      // This stops lint from complaining about unused signals.
      logic unused_part_scrmbl_sigs;
      assign unused_part_scrmbl_sigs = ^{part_scrmbl_mtx_gnt[k],
                                         part_scrmbl_req_ready[k],
                                         part_scrmbl_rsp_valid[k],
                                         integ_chk_req[k],
                                         cnsty_chk_req[k]};

      `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlPartUnbufStateRegsCheck_A, u_part_unbuf.u_state_regs, alerts[1])

    ////////////////////////////////////////////////////////////////////////////////////////////////
    end else if (PartInfo[k].variant == Buffered) begin : gen_buffered
      otp_ctrl_part_buf #(
        .Info(PartInfo[k]),
        .DataDefault(PartInvDefault[PartInfo[k].offset*8 +: PartInfo[k].size*8])
      ) u_part_buf (
        .clk_i,
        .rst_ni,
        .init_req_i        ( part_init_req                   ),
        .init_done_o       ( part_init_done[k]               ),
        .integ_chk_req_i   ( integ_chk_req[k]                ),
        .integ_chk_ack_o   ( integ_chk_ack[k]                ),
        .cnsty_chk_req_i   ( cnsty_chk_req[k]                ),
        .cnsty_chk_ack_o   ( cnsty_chk_ack[k]                ),
        .escalate_en_i     ( lc_escalate_en[k]               ),
        // Only supported by life cycle partition (see further below).
        .check_byp_en_i    ( lc_ctrl_pkg::Off                ),
        .error_o           ( part_error[k]                   ),
        .fsm_err_o         ( part_fsm_err[k]                 ),
        .access_i          ( part_access[k]                  ),
        .access_o          ( part_access_dai[k]              ),
        .digest_o          ( part_digest[k]                  ),
        .data_o            ( part_buf_data[PartInfo[k].offset +: PartInfo[k].size] ),
        .otp_req_o         ( part_otp_arb_req[k]             ),
        .otp_cmd_o         ( part_otp_arb_bundle[k].cmd      ),
        .otp_size_o        ( part_otp_arb_bundle[k].size     ),
        .otp_wdata_o       ( part_otp_arb_bundle[k].wdata    ),
        .otp_addr_o        ( part_otp_arb_bundle[k].addr     ),
        .otp_gnt_i         ( part_otp_arb_gnt[k]             ),
        .otp_rvalid_i      ( part_otp_rvalid[k]              ),
        .otp_rdata_i       ( part_otp_rdata                  ),
        .otp_err_i         ( part_otp_err                    ),
        .scrmbl_mtx_req_o  ( part_scrmbl_mtx_req[k]          ),
        .scrmbl_mtx_gnt_i  ( part_scrmbl_mtx_gnt[k]          ),
        .scrmbl_cmd_o      ( part_scrmbl_req_bundle[k].cmd   ),
        .scrmbl_mode_o     ( part_scrmbl_req_bundle[k].mode  ),
        .scrmbl_sel_o      ( part_scrmbl_req_bundle[k].sel   ),
        .scrmbl_data_o     ( part_scrmbl_req_bundle[k].data  ),
        .scrmbl_valid_o    ( part_scrmbl_req_bundle[k].valid ),
        .scrmbl_ready_i    ( part_scrmbl_req_ready[k]        ),
        .scrmbl_valid_i    ( part_scrmbl_rsp_valid[k]        ),
        .scrmbl_data_i     ( part_scrmbl_rsp_data            )
      );

      // Buffered partitions are not accessible via the TL-UL window.
      logic unused_part_tlul_sigs;
      assign unused_part_tlul_sigs = ^part_tlul_req[k];
      assign part_tlul_gnt[k]    = 1'b0;
      assign part_tlul_rerror[k] = '0;
      assign part_tlul_rvalid[k] = 1'b0;
      assign part_tlul_rdata[k]  = '0;

      `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OtpCtrPartBufPrimCountCheck_A, u_part_buf.u_prim_count, alerts[1])
      `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlPartBufStateRegsCheck_A, u_part_buf.u_state_regs, alerts[1])

    ////////////////////////////////////////////////////////////////////////////////////////////////
    end else if (PartInfo[k].variant == LifeCycle) begin : gen_lifecycle
      otp_ctrl_part_buf #(
        .Info(PartInfo[k]),
        .DataDefault(PartInvDefault[PartInfo[k].offset*8 +: PartInfo[k].size*8])
      ) u_part_buf (
        .clk_i,
        .rst_ni,
        .init_req_i        ( part_init_req                   ),
        .init_done_o       ( part_init_done[k]               ),
        .integ_chk_req_i   ( integ_chk_req[k]                ),
        .integ_chk_ack_o   ( integ_chk_ack[k]                ),
        .cnsty_chk_req_i   ( cnsty_chk_req[k]                ),
        .cnsty_chk_ack_o   ( cnsty_chk_ack[k]                ),
        .escalate_en_i     ( lc_escalate_en[k]               ),
        // This is only supported by the life cycle partition. We need to prevent this partition
        // from escalating once the life cycle state in memory is being updated (and hence not
        // consistent with the values in the buffer regs anymore).
        .check_byp_en_i    ( lc_check_byp_en                 ),
        .error_o           ( part_error[k]                   ),
        .fsm_err_o         ( part_fsm_err[k]                 ),
        .access_i          ( part_access[k]                  ),
        .access_o          ( part_access_dai[k]              ),
        .digest_o          ( part_digest[k]                  ),
        .data_o            ( part_buf_data[PartInfo[k].offset +: PartInfo[k].size] ),
        .otp_req_o         ( part_otp_arb_req[k]             ),
        .otp_cmd_o         ( part_otp_arb_bundle[k].cmd      ),
        .otp_size_o        ( part_otp_arb_bundle[k].size     ),
        .otp_wdata_o       ( part_otp_arb_bundle[k].wdata    ),
        .otp_addr_o        ( part_otp_arb_bundle[k].addr     ),
        .otp_gnt_i         ( part_otp_arb_gnt[k]             ),
        .otp_rvalid_i      ( part_otp_rvalid[k]              ),
        .otp_rdata_i       ( part_otp_rdata                  ),
        .otp_err_i         ( part_otp_err                    ),
        // The LC partition does not need any scrambling features.
        .scrmbl_mtx_req_o  (                                 ),
        .scrmbl_mtx_gnt_i  ( 1'b0                            ),
        .scrmbl_cmd_o      (                                 ),
        .scrmbl_mode_o     (                                 ),
        .scrmbl_sel_o      (                                 ),
        .scrmbl_data_o     (                                 ),
        .scrmbl_valid_o    (                                 ),
        .scrmbl_ready_i    ( 1'b0                            ),
        .scrmbl_valid_i    ( 1'b0                            ),
        .scrmbl_data_i     ( '0                              )
      );

      // Buffered partitions are not accessible via the TL-UL window.
      logic unused_part_tlul_sigs;
      assign unused_part_tlul_sigs = ^part_tlul_req[k];
      assign part_tlul_gnt[k]    = 1'b0;
      assign part_tlul_rerror[k] = '0;
      assign part_tlul_rvalid[k] = 1'b0;
      assign part_tlul_rdata[k]  = '0;

      // Tie off unused connections.
      assign part_scrmbl_mtx_req[k]    = '0;
      assign part_scrmbl_req_bundle[k] = '0;

      // This stops lint from complaining about unused signals.
      logic unused_part_scrmbl_sigs;
      assign unused_part_scrmbl_sigs = ^{part_scrmbl_mtx_gnt[k],
                                         part_scrmbl_req_ready[k],
                                         part_scrmbl_rsp_valid[k]};

      `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OtpCtrLcPartBufPrimCountCheck_A, u_part_buf.u_prim_count, alerts[1])
      `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlLcPartBufStateRegsCheck_A, u_part_buf.u_state_regs, alerts[1])

    ////////////////////////////////////////////////////////////////////////////////////////////////
    end else begin : gen_invalid
      // This is invalid and should break elaboration
      assert_static_in_generate_invalid assert_static_in_generate_invalid();
    end
    ////////////////////////////////////////////////////////////////////////////////////////////////
  end

  //////////////////////////////////
  // Buffered Data Output Mapping //
  //////////////////////////////////

  // Output complete hardware config partition.
  // Actual mapping to other IPs is done via the intersignal topgen feature,
  // selection of fields can be done using the otp_hw_cfg_t struct fields.
  otp_broadcast_t otp_broadcast, otp_broadcast_FIPS_checked;
  logic lcc_is_in_SCRAP_mode;
  assign lcc_is_in_SCRAP_mode = (lc_ctrl_state_pkg::lc_state_e'(part_buf_data[LcStateOffset +: LcStateSize])
                            == lc_ctrl_state_pkg::LcStScrap);
  // Make sure the broadcast valid is flopped before sending it out.
  lc_ctrl_pkg::lc_tx_t otp_broadcast_valid_q;
  assign otp_broadcast = named_broadcast_assign(part_init_done, part_buf_data);
  caliptra_prim_lc_sender u_prim_lc_sender_otp_broadcast_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(otp_broadcast.valid),
    .lc_en_o(otp_broadcast_valid_q)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : zeroize_secret
    if (!rst_ni) begin
      otp_broadcast_o <= '0;
    end else begin
      if (FIPS_ZEROIZATION_CMD_i || lcc_is_in_SCRAP_mode) begin
        otp_broadcast_o <= '0;
      end else begin        
        otp_broadcast_o <= otp_broadcast_FIPS_checked;
      end
    end
  end

  always_comb begin : p_otp_broadcast_valid
    otp_broadcast_FIPS_checked       = otp_broadcast;
    otp_broadcast_FIPS_checked.valid = otp_broadcast_valid_q;
  end

  // LCC transition tokens.
  assign otp_lc_data_o.test_unlock_token = lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked1 ? part_buf_data[CptraSsTestUnlockToken1Offset +: CptraSsTestUnlockToken1Size] : 
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked2 ? part_buf_data[CptraSsTestUnlockToken2Offset +: CptraSsTestUnlockToken2Size] :
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked3 ? part_buf_data[CptraSsTestUnlockToken3Offset +: CptraSsTestUnlockToken3Size] :
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked4 ? part_buf_data[CptraSsTestUnlockToken4Offset +: CptraSsTestUnlockToken4Size] :
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked5 ? part_buf_data[CptraSsTestUnlockToken5Offset +: CptraSsTestUnlockToken5Size] :
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked6 ? part_buf_data[CptraSsTestUnlockToken6Offset +: CptraSsTestUnlockToken6Size] :
                                           lc_otp_program_i.state == lc_ctrl_state_pkg::LcStTestUnlocked7 ? part_buf_data[CptraSsTestUnlockToken7Offset +: CptraSsTestUnlockToken7Size] : '0;

  assign otp_lc_data_o.test_exit_dev_token     = part_buf_data[CptraSsTestExitToManufTokenOffset +:
                                                               CptraSsTestExitToManufTokenSize];
  assign otp_lc_data_o.dev_exit_prod_token     = part_buf_data[CptraSsManufToProdTokenOffset +:
                                                               CptraSsManufToProdTokenSize];
  assign otp_lc_data_o.prod_exit_prodend_token = part_buf_data[CptraSsProdToProdEndTokenOffset +:
                                                               CptraSsProdToProdEndTokenSize];
  assign otp_lc_data_o.rma_token               = part_buf_data[CptraSsRmaTokenOffset +:
                                                               CptraSsRmaTokenSize];

  lc_ctrl_pkg::lc_tx_t test_tokens_valid, rma_token_valid, secrets_valid;
  // The transition tokens have been provisioned.
  assign test_tokens_valid = (part_digest[SecretLcTransitionPartitionIdx] != '0) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
  // The rma token has been provisioned.
  assign rma_token_valid = (part_digest[SecretLcTransitionPartitionIdx] != '0) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
  // The device is personalized if the root key has been provisioned and locked.
  assign secrets_valid = lc_ctrl_pkg::Off;

  // Buffer these constants in order to ensure that synthesis does not try to optimize the encoding.
  // SEC_CM: TOKEN_VALID.CTRL.MUBI
  caliptra_prim_lc_sender #(
    .AsyncOn(0)
  ) u_prim_lc_sender_test_tokens_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(test_tokens_valid),
    .lc_en_o(otp_lc_data_o.test_tokens_valid)
  );

  caliptra_prim_lc_sender #(
    .AsyncOn(0)
  ) u_prim_lc_sender_rma_token_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(rma_token_valid),
    .lc_en_o(otp_lc_data_o.rma_token_valid)
  );

  caliptra_prim_lc_sender #(
    .AsyncOn(0)
  ) u_prim_lc_sender_secrets_valid (
    .clk_i,
    .rst_ni,
    .lc_en_i(secrets_valid),
    .lc_en_o(otp_lc_data_o.secrets_valid)
  );

  // Lifecycle state
  assign otp_lc_data_o.state = lc_ctrl_state_pkg::lc_state_e'(part_buf_data[LcStateOffset +:
                                                                            LcStateSize]);
  assign otp_lc_data_o.count = lc_ctrl_state_pkg::lc_cnt_e'(part_buf_data[LcTransitionCntOffset +:
                                                                          LcTransitionCntSize]);

  // Assert life cycle state valid signal only when all partitions have initialized.
  assign otp_lc_data_o.valid    = &part_init_done;
  // Signal whether there are any errors in the life cycle partition (both correctable and
  // uncorrectable ones). This bit is made available via the JTAG TAP, which is useful for
  // production testing in RAW life cycle state where the OTP regs are not accessible.
  assign otp_lc_data_o.error    = |part_error[LifeCycleIdx];

  // Not all bits of part_buf_data are used here.
  logic unused_buf_data;
  assign unused_buf_data = ^part_buf_data;

  ////////////////
  // Assertions //
  ////////////////

  //`CALIPTRA_ASSERT_INIT(RmaTokenSize_A,        lc_ctrl_state_pkg::LcTokenWidth == RmaTokenSize * 8)
  //`CALIPTRA_ASSERT_INIT(TestUnlockTokenSize_A, lc_ctrl_state_pkg::LcTokenWidth == TestUnlockToken0Size * 8)
  `CALIPTRA_ASSERT_INIT(LcStateSize_A,         lc_ctrl_state_pkg::LcStateWidth == LcStateSize * 8)
  `CALIPTRA_ASSERT_INIT(LcTransitionCntSize_A, lc_ctrl_state_pkg::LcCountWidth == LcTransitionCntSize * 8)
  `CALIPTRA_ASSERT_KNOWN(CoreTlOutKnown_A,            core_tl_o)
  `CALIPTRA_ASSERT_KNOWN(PrimTlOutKnown_A,            prim_tl_o)
  `CALIPTRA_ASSERT_KNOWN(IntrOtpOperationDoneKnown_A, intr_otp_operation_done_o)
  `CALIPTRA_ASSERT_KNOWN(IntrOtpErrorKnown_A,         intr_otp_error_o)
  `CALIPTRA_ASSERT_KNOWN(PwrOtpInitRspKnown_A,        pwr_otp_o)
  `CALIPTRA_ASSERT_KNOWN(LcOtpProgramRspKnown_A,      lc_otp_program_o)
  `CALIPTRA_ASSERT_KNOWN(OtpLcDataKnown_A,            otp_lc_data_o)
  `CALIPTRA_ASSERT_KNOWN(OtpBroadcastKnown_A,         otp_broadcast_o)

  `CALIPTRA_ASSERT(TransitionTokensValid_A, part_digest[SecretLcTransitionPartitionIdx] != '0 |-> test_tokens_valid == lc_ctrl_pkg::On)

  // Redirect error triggers to the state error alert port.
  `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OtpCtrlDaiPrimCountCheck_A, u_otp_ctrl_dai.u_prim_count, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlDaiStateRegsCheck_A, u_otp_ctrl_dai.u_state_regs, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(OtpCtrlPrimOnehotCheck_A, u_reg_core.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OptCtrlLciPrimCountCheck_A, u_otp_ctrl_lci.u_prim_count, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlLciStateRegsCheck_A, u_otp_ctrl_lci.u_state_regs, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OptCtrlLfsrTimerPrimCountCnstyCheck_A, u_otp_ctrl_lfsr_timer.u_prim_count_cnsty, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OptCtrlLfsrTimerPrimCountIntegCheck_A, u_otp_ctrl_lfsr_timer.u_prim_count_integ, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(OtpCtrlLfsrTimerPrimDoubleLfsrCheck_A, u_otp_ctrl_lfsr_timer.u_prim_double_lfsr, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlLfsrTimerStateRegsCheck_A, u_otp_ctrl_lfsr_timer.u_state_regs, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(OptCtrlScrmlPrimCountCheck_A, u_otp_ctrl_scrmbl.u_prim_count, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlScrmblStateRegsCheck_A, u_otp_ctrl_scrmbl.u_state_regs, alerts[1])
  `CALIPTRA_SS_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(OtpCtrlTlulLcGateStateRegsCheck_A, u_tlul_lc_gate.u_state_regs, alerts[1])

endmodule : otp_ctrl
