// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Direct access interface for OTP controller.
//

`include "caliptra_prim_flop_macros.sv"

module otp_ctrl_dai
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
(
  input                                  clk_i,
  input                                  rst_ni,

  output logic                           discarded_fuse_write_o,
  input                                  discard_fuse_write_i,
  // Init reqest from power manager
  input                                  init_req_i,
  output logic                           init_done_o,
  // Init request going to partitions
  output logic                           part_init_req_o,
  input  [NumPart-1:0]                   part_init_done_i,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the DAI.
  input lc_ctrl_pkg::lc_tx_t             escalate_en_i,
  // Output error state of DAI, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the DAI FSM into
  // a terminal error state.
  output otp_err_e                       error_o,
  // This error signal is pulsed high if the FSM has been glitched into an invalid state.
  // Although it is somewhat redundant with the error code in error_o above, it is
  // meant to cover cases where we already latched an error code while the FSM is
  // glitched into an invalid state (since in that case, the error code will not be
  // overridden with the FSM error code so that the original error code is still
  // discoverable).
  output logic                           fsm_err_o,
  // Access/lock status from partitions
  // SEC_CM: ACCESS.CTRL.MUBI
  input  part_access_t [NumPart-1:0]     part_access_i,
  // CSR interface
  input        [OtpByteAddrWidth-1:0]    dai_addr_i,
  input dai_cmd_e                        dai_cmd_i,
  input logic                            dai_req_i,
  input        [NumDaiWords-1:0][31:0]   dai_wdata_i,
  output logic                           dai_idle_o,      // wired to the status CSRs
  output logic                           dai_prog_idle_o, // wired to lfsr timer and pwrmgr
  output logic                           dai_cmd_done_o,  // this is used to raise an IRQ
  output logic [NumDaiWords-1:0][31:0]   dai_rdata_o,
  // OTP interface
  output logic                           otp_req_o,
  output prim_generic_otp_pkg::cmd_e     otp_cmd_o,
  output logic [OtpSizeWidth-1:0]        otp_size_o,
  output logic [OtpIfWidth-1:0]          otp_wdata_o,
  output logic [OtpAddrWidth-1:0]        otp_addr_o,
  input                                  otp_gnt_i,
  input                                  otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]          otp_rdata_i,
  input  prim_generic_otp_pkg::err_e     otp_err_i,
  // Scrambling mutex request
  output logic                           scrmbl_mtx_req_o,
  input                                  scrmbl_mtx_gnt_i,
  // Scrambling datapath interface
  output otp_scrmbl_cmd_e                scrmbl_cmd_o,
  output digest_mode_e                   scrmbl_mode_o,
  output logic [ConstSelWidth-1:0]       scrmbl_sel_o,
  output logic [ScrmblBlockWidth-1:0]    scrmbl_data_o,
  output logic                           scrmbl_valid_o,
  input  logic                           scrmbl_ready_i,
  input  logic                           scrmbl_valid_i,
  input  logic [ScrmblBlockWidth-1:0]    scrmbl_data_i,
  // Zeroization trigger indicators for each partition.
  // The first successful zeroization request will set the
  // corresponding MuBi in the array.
  output mubi8_t [NumPart-1:0] zer_trigs_o,
  input mubi8_t [NumPart-1:0] zer_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import caliptra_prim_mubi_pkg::*;
  import caliptra_prim_util_pkg::vbits;

  localparam int CntWidth = OtpByteAddrWidth - $clog2(ScrmblBlockWidth/8);

  // Integration checks for parameters.
  `CALIPTRA_ASSERT_INIT(CheckNativeOtpWidth0_A, (ScrmblBlockWidth % OtpWidth) == 0)
  `CALIPTRA_ASSERT_INIT(CheckNativeOtpWidth1_A, (32 % OtpWidth) == 0)

  /////////////////////
  // DAI Control FSM //
  /////////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 4 -m 22 -n 12 \
  //     -s 803253351 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||| (12.99%)
  //  5: |||||||||||||||||||| (25.11%)
  //  6: |||||||||||||||| (21.21%)
  //  7: |||||||||||||||| (20.35%)
  //  8: |||||||||| (12.99%)
  //  9: |||| (6.06%)
  // 10:  (0.87%)
  // 11:  (0.43%)
  // 12: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 11
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 9
  //
  localparam int StateWidth = 12;
  typedef enum logic [StateWidth-1:0] {
    ResetSt       = 12'b111001101100,
    InitOtpSt     = 12'b000011010001,
    InitPartSt    = 12'b101100000010,
    IdleSt        = 12'b101011110010,
    ErrorSt       = 12'b110010101001,
    ReadSt        = 12'b001111011011,
    ReadWaitSt    = 12'b000000111101,
    DescrSt       = 12'b100110010100,
    DescrWaitSt   = 12'b010100010001,
    WriteSt       = 12'b010111001100,
    WriteWaitSt   = 12'b101100100101,
    ScrSt         = 12'b110001010011,
    ScrWaitSt     = 12'b000101010110,
    DigClrSt      = 12'b011010111100,
    DigReadSt     = 12'b101011011100,
    DigReadWaitSt = 12'b101001001001,
    DigSt         = 12'b001110101001,
    DigPadSt      = 12'b001101100000,
    DigFinSt      = 12'b010010110111,
    DigWaitSt     = 12'b110101101111,
    ZerSt         = 12'b000100111010,
    ZerWaitSt     = 12'b001000001100
  } state_e;

  typedef enum logic [1:0] {
    OtpData = 2'b00,
    DaiData = 2'b01,
    ScrmblData = 2'b10
  } data_sel_e;


  typedef enum logic {
    PartOffset = 1'b0,
    DaiOffset = 1'b1
  } addr_sel_e;

  state_e state_d, state_q;
  logic [CntWidth-1:0] cnt;
  logic cnt_en, cnt_clr, cnt_err;
  otp_err_e error_d, error_q;
  logic data_en, data_clr;
  logic discarded_fuse_write_d;
  data_sel_e data_sel;
  addr_sel_e base_sel_d, base_sel_q;
  logic [ScrmblBlockWidth-1:0] data_q;
  logic [NumPartWidth-1:0] part_idx;
  logic [NumPart-1:0][OtpAddrWidth-1:0] digest_addr_lut;
  logic [NumPart-1:0][OtpAddrWidth-1:0] zeroize_addr_lut;
  logic part_sel_valid;
  mubi8_t [NumPart-1:0] zer_trigs_d;

  // Depending on the partition configuration, the wrapper is instructed to ignore integrity
  // calculations and checks. To be on the safe side, the partition filters error responses at this
  // point and does not report any integrity errors if integrity is disabled.
  otp_err_e otp_err;
  always_comb begin
    otp_err = otp_err_e'(otp_err_i);
    if (!PartInfo[part_idx].integrity &&
        otp_err_e'(otp_err_i) inside {MacroEccCorrError, MacroEccUncorrError}) begin
      otp_err = NoError;
    end
  end

  // Output partition error state.
  assign error_o       = error_q;
  // Working register is connected to data outputs.
  assign otp_wdata_o   = data_q;
  assign scrmbl_data_o = data_q;
  // Only expose this working register in IdleSt.
  // The FSM below makes sure to clear this register
  // after digest and write ops.
  assign dai_rdata_o   = (state_q == IdleSt) ? data_q : '0;

  ///////////////////////
  // Zeroization Check //
  ///////////////////////

  // The read-out data is is buffered and replicated, then screened for the
  // zeroization marker. This is only relevant for the `ZEROIZE` command to
  // prevent exposing scrambled data to software.

  localparam int ZerFanout = 4;

  // Compose several individual MuBis into a larger MuBi. The resulting
  // value must always be a valid MuBi constant (either `true` or `false`).
  logic   [ZerFanout-1:0][ScrmblBlockWidth-1:0] otp_rdata_post;
  mubi4_t [ZerFanout-1:0] zeroized_valid_pre;
  mubi16_t zeroized_valid;
  for (genvar k = 0; k < ZerFanout; k++) begin
    caliptra_prim_buf #(
      .Width(ScrmblBlockWidth)
    ) u_rdata_buf (
      .in_i  ( otp_rdata_i       ),
      .out_o ( otp_rdata_post[k] )
    );

    // Interleave MuBi4 chunks to create a higher-order MuBi.
    // Even indices: (MuBi4True, MuBi4False)
    // Odd indices:  (MuBi4False, MuBi4True)
    assign zeroized_valid_pre[k] = (check_zeroized_valid(otp_rdata_post[k]) ^~ (k % 2 == 0)) ? MuBi4True : MuBi4False;
  end

  caliptra_prim_buf #(
    .Width(MuBi16Width)
  ) u_zeroized_valid_buf (
    .in_i  ( zeroized_valid_pre ),
    .out_o ( {zeroized_valid}   )
  );

  always_comb begin : p_fsm
    state_d = state_q;

    // Init signals
    init_done_o = 1'b1;
    part_init_req_o = 1'b0;

    // DAI signals
    dai_idle_o = 1'b0;
    dai_prog_idle_o = 1'b1;
    dai_cmd_done_o = 1'b0;

    // OTP signals
    otp_req_o = 1'b0;
    otp_cmd_o = prim_generic_otp_pkg::Init;

    // Scrambling mutex
    scrmbl_mtx_req_o = 1'b0;

    // Scrambling datapath
    scrmbl_cmd_o   = LoadShadow;
    scrmbl_sel_o   = CnstyDigest;
    scrmbl_mode_o  = StandardMode;
    scrmbl_valid_o = 1'b0;

    // Counter
    cnt_en  = 1'b0;
    cnt_clr = 1'b0;
    base_sel_d = base_sel_q;

    // Temporary data register
    data_en = 1'b0;
    data_clr = 1'b0;
    discarded_fuse_write_d = 1'b0;
    data_sel = OtpData;

    // Error Register
    error_d = error_q;
    fsm_err_o = 1'b0;

    // Zeroization trigger
    zer_trigs_d = zer_trigs_o;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // We get here after reset and wait until the power manager
      // requests OTP initialization. If initialization is requested,
      // an init command is written to the OTP macro, and we move on
      // to the InitOtpSt waiting state.
      ResetSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        data_clr = 1'b1;
        discarded_fuse_write_d = 1'b0;
        if (init_req_i) begin
          otp_req_o = 1'b1;
          if (otp_gnt_i) begin
            state_d = InitOtpSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // We wait here unitl the OTP macro has initialized without
      // error. If an error occurred during this stage, we latch that
      // error and move into a terminal error  state.
      InitOtpSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        if (otp_rvalid_i) begin
          if ((!(otp_err inside {NoError, MacroEccCorrError}))) begin
            state_d = ErrorSt;
            error_d = otp_err;
          end else begin
            state_d = InitPartSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Since the OTP macro is now functional, we can send out an
      // initialization request to all partitions and wait until they
      // all have initialized.
      InitPartSt: begin
        init_done_o = 1'b0;
        dai_prog_idle_o = 1'b0;
        part_init_req_o = 1'b1;
        if (part_init_done_i == {NumPart{1'b1}}) begin
          state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Idle state where we wait for incoming commands.
      // Invalid commands trigger a CmdInvErr, which is recoverable.
      IdleSt: begin
        dai_idle_o  = 1'b1;
        if (dai_req_i) begin
          // This clears previous (recoverable) and reset the counter.
          error_d = NoError;
          cnt_clr = 1'b1;
          unique case (dai_cmd_i)
            DaiRead:  begin
              state_d = ReadSt;
              // Clear the temporary data register.
              data_clr = 1'b1;
              base_sel_d = DaiOffset;
            end
            DaiWrite: begin
              data_sel = DaiData;
              // Fetch data block.
              data_en = 1'b1;
              base_sel_d = DaiOffset;
              // If this partition is scrambled, directly go to write scrambling first.
              if (PartInfo[part_idx].secret) begin
                state_d = ScrSt;
              end else begin
                state_d = WriteSt;
              end
            end
            DaiDigest: begin
              state_d = DigClrSt;
              scrmbl_mtx_req_o = 1'b1;
              base_sel_d = PartOffset;
            end
            DaiZeroize: begin
              state_d = ZerSt;
              base_sel_d = DaiOffset;
            end
            default: ; // Ignore invalid commands
          endcase // dai_cmd_i
        end // dai_req_i
      end
      ///////////////////////////////////////////////////////////////////
      // Each time we request a block of data from OTP, we re-check
      // whether read access has been locked for this partition. If
      // that is the case, we immediately bail out. Otherwise, we
      // request a block of data from OTP.
      ReadSt: begin
        if ( !discard_fuse_write_i &&
          part_sel_valid && (mubi8_test_false_strict(part_access_i[part_idx].read_lock) ||
                               // HW digests and zeroization marker always remain readable.
                               (PartInfo[part_idx].hw_digest && otp_addr_o == digest_addr_lut[part_idx]) ||
                               (PartInfo[part_idx].zeroizable && otp_addr_o == zeroize_addr_lut[part_idx]))) begin
          otp_req_o = 1'b1;
          // Depending on the partition configuration,
          // the wrapper is instructed to ignore integrity errors.
          if (PartInfo[part_idx].integrity && mubi8_test_false_loose(zer_i[part_idx]) &&
              !(otp_addr_o == zeroize_addr_lut[part_idx])) begin
            otp_cmd_o = prim_generic_otp_pkg::Read;
          end else begin
            otp_cmd_o = prim_generic_otp_pkg::ReadRaw;
          end
          if (otp_gnt_i) begin
            state_d = ReadWaitSt;
          end
        end else begin
          discarded_fuse_write_d = 1'b1;
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and write to readout register. Check
      // whether descrambling is required or not. In case an OTP
      // transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      ReadWaitSt: begin
        // Continuously check read access and bail out if this is not consistent.
        if (part_sel_valid && (mubi8_test_false_strict(part_access_i[part_idx].read_lock) ||
                               // HW digests and zeroization marker always remain readable.
                               (PartInfo[part_idx].hw_digest && otp_addr_o == digest_addr_lut[part_idx]) ||
                               (PartInfo[part_idx].zeroizable && otp_addr_o == zeroize_addr_lut[part_idx]))) begin
          if (otp_rvalid_i) begin
            // Check OTP return code.
            if (otp_err inside {NoError, MacroEccCorrError}) begin
              data_en = 1'b1;
              // We do not need to descramble the digest and zeroization fields..
              if (PartInfo[part_idx].secret && otp_addr_o != digest_addr_lut[part_idx] && otp_addr_o != zeroize_addr_lut[part_idx]) begin
                state_d = DescrSt;
              end else begin
                state_d = IdleSt;
                dai_cmd_done_o = 1'b1;
              end
              // At this point the only error that we could have gotten are correctable ECC errors.
              if (otp_err != NoError) begin
                error_d = MacroEccCorrError;
              end
            end else begin
              state_d = ErrorSt;
              error_d = otp_err;
            end
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Descrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      DescrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Decrypt;
        scrmbl_sel_o = PartInfo[part_idx].key_sel;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = DescrWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the descrambled data to return. Note that we release
      // the mutex lock upon leaving this state.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      DescrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_sel_o = PartInfo[part_idx].key_sel;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          state_d = IdleSt;
          data_en = 1'b1;
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, check whether write accesses are allowed to this
      // partition, and error out otherwise. Note that for buffered
      // partitions, we do not allow DAI writes to the digest offset.
      // Unbuffered partitions have SW managed digests, hence that
      // check is not needed in that case. The LC partition is
      // permanently write locked and can hence not be written via the DAI.
      WriteSt: begin
        dai_prog_idle_o = 1'b0;
        if ( !discard_fuse_write_i && // If there is no access violation.
            part_sel_valid && mubi8_test_false_strict(part_access_i[part_idx].write_lock) &&
            // If this is a HW digest write to a buffered partition.
            ((PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == PartOffset && otp_addr_o == digest_addr_lut[part_idx]) ||
             // If this is a non HW digest write to a buffered partition.
             (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == DaiOffset && otp_addr_o < digest_addr_lut[part_idx]) ||
             // If this is a write to an unbuffered partition
             (PartInfo[part_idx].variant != Buffered && base_sel_q == DaiOffset))) begin
          otp_req_o = 1'b1;
          // Depending on the partition configuration,
          // the wrapper is instructed to ignore integrity errors.
          if (PartInfo[part_idx].integrity) begin
            otp_cmd_o = prim_generic_otp_pkg::Write;
          end else begin
            otp_cmd_o = prim_generic_otp_pkg::WriteRaw;
          end
          if (otp_gnt_i) begin
            state_d = WriteWaitSt;
          end
        end else begin
          // Clear working register state.
          discarded_fuse_write_d = 1'b1;
          data_clr = 1'b1;
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response, and then go back to idle. In case an
      // OTP transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      WriteWaitSt: begin
        dai_prog_idle_o = 1'b0;
        // Continuously check write access and bail out if this is not consistent.
        if (part_sel_valid && mubi8_test_false_strict(part_access_i[part_idx].write_lock) &&
            // If this is a HW digest write to a buffered partition.
            ((PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == PartOffset && otp_addr_o == digest_addr_lut[part_idx]) ||
             // If this is a non HW digest write to a buffered partition.
             (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].hw_digest &&
              base_sel_q == DaiOffset && otp_addr_o < digest_addr_lut[part_idx]) ||
             // If this is a write to an unbuffered partition
             (PartInfo[part_idx].variant != Buffered && base_sel_q == DaiOffset))) begin

          if (otp_rvalid_i) begin
            // Check OTP return code. Note that non-blank errors are recoverable.
            if ((!(otp_err inside {NoError, MacroWriteBlankError}))) begin
              state_d = ErrorSt;
              error_d = otp_err;
            end else begin
              // Clear working register state.
              data_clr = 1'b1;
              state_d = IdleSt;
              dai_cmd_done_o = 1'b1;
              // Signal non-blank state, but do not go to terminal error state.
              if (otp_err == MacroWriteBlankError) begin
                error_d = otp_err;
              end
            end
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Scrambling state. This first acquires the scrambling
      // datapath mutex. Note that once the mutex is acquired, we have
      // exclusive access to the scrambling datapath until we release
      // the mutex by deasserting scrmbl_mtx_req_o.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      ScrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        // Check write access and bail out if this is not consistent.
        if (part_sel_valid && mubi8_test_false_strict(part_access_i[part_idx].write_lock) &&
            // If this is a non HW digest write to a buffered partition.
            (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].secret &&
             PartInfo[part_idx].hw_digest && base_sel_q == DaiOffset &&
             otp_addr_o < digest_addr_lut[part_idx])) begin

          scrmbl_valid_o = 1'b1;
          scrmbl_cmd_o = Encrypt;
          scrmbl_sel_o = PartInfo[part_idx].key_sel;
          if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
            state_d = ScrWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the scrambled data to return. Note that we release
      // the mutex lock upon leaving this state.
      // SEC_CM: SECRET.MEM.SCRAMBLE
      ScrWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        // Continously check write access and bail out if this is not consistent.
        if (part_sel_valid && mubi8_test_false_strict(part_access_i[part_idx].write_lock) &&
            // If this is a non HW digest write to a buffered partition.
            (PartInfo[part_idx].variant == Buffered && PartInfo[part_idx].secret &&
             PartInfo[part_idx].hw_digest && base_sel_q == DaiOffset &&
             otp_addr_o < digest_addr_lut[part_idx])) begin
          data_sel = ScrmblData;
          if (scrmbl_valid_i) begin
            state_d = WriteSt;
            data_en = 1'b1;
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, acquire the mutex for the digest and clear the digest state.
      // SEC_CM: PART.MEM.DIGEST
      DigClrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // Need to reset the digest state and set digest mode to "standard".
        scrmbl_cmd_o = DigestInit;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = DigReadSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This requests a 64bit block to be pushed into the digest datapath.
      // We also check here whether the partition has been write locked.
      // SEC_CM: PART.MEM.DIGEST
      DigReadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        if (part_sel_valid &&
            mubi8_test_false_strict(part_access_i[part_idx].read_lock) &&
            mubi8_test_false_strict(part_access_i[part_idx].write_lock)) begin
          otp_req_o = 1'b1;
          // Depending on the partition configuration,
          // the wrapper is instructed to ignore integrity errors.
          if (PartInfo[part_idx].integrity) begin
            otp_cmd_o = prim_generic_otp_pkg::Read;
          end else begin
            otp_cmd_o = prim_generic_otp_pkg::ReadRaw;
          end
          if (otp_gnt_i) begin
            state_d = DigReadWaitSt;
          end
        end else begin
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response and write to readout register. Check
      // whether descrambling is required or not. In case an OTP
      // transaction fails, latch the OTP error code, and jump to
      // terminal error state.
      // SEC_CM: PART.MEM.DIGEST
      DigReadWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        if (otp_rvalid_i) begin
          cnt_en = 1'b1;
          // Check OTP return code.
          if ((!(otp_err inside {NoError, MacroEccCorrError}))) begin
            state_d = ErrorSt;
            error_d = otp_err;
          end else begin
            data_en = 1'b1;
            state_d = DigSt;
            // Signal soft ECC errors, but do not go into terminal error state.
            if (otp_err == MacroEccCorrError) begin
              error_d = otp_err;
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Push the word read into the scrambling datapath.  The last
      // block is repeated in case the number blocks in this partition
      // is odd.
      // SEC_CM: PART.MEM.DIGEST
      DigSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // No need to digest the digest value itself
        if (otp_addr_o == digest_addr_lut[part_idx]) begin
          // Trigger digest round in case this is the second block in a row.
          if (!cnt[0]) begin
            scrmbl_cmd_o = Digest;
            if (scrmbl_ready_i) begin
              state_d = DigFinSt;
            end
          // Otherwise, just load low word and go to padding state.
          end else if (scrmbl_ready_i) begin
            state_d = DigPadSt;
          end
        end else begin
          // Trigger digest round in case this is the second block in a row.
          if (!cnt[0]) begin
            scrmbl_cmd_o = Digest;
          end
          // Go back and fetch more data blocks.
          if (scrmbl_ready_i) begin
            state_d = DigReadSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Padding state, just repeat the last block and go to digest
      // finalization.
      // SEC_CM: PART.MEM.DIGEST
      DigPadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = Digest;
        if (scrmbl_ready_i) begin
          state_d = DigFinSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Trigger digest finalization and go wait for the result.
      // SEC_CM: PART.MEM.DIGEST
      DigFinSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = DigestFinalize;
        if (scrmbl_ready_i) begin
          state_d = DigWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the digest to return, and write the result to OTP.
      // Note that the write address will be correct in this state,
      // since the counter has been stepped to the correct address as
      // part of the readout sequence, and the correct size for this
      // access has been loaded before.
      // SEC_CM: PART.MEM.DIGEST
      DigWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        data_sel = ScrmblData;
        if (scrmbl_valid_i) begin
          state_d = WriteSt;
          data_en = 1'b1;
        end
      end

      ///////////////////////////////////////////////////////////////////
      // Check whether partition is zeroizable and transition into the
      // wait state once the OTP request has been granted.
      ZerSt: begin
        dai_prog_idle_o = 1'b0;
        if (// Fuses in a partition can only be zeroized if the partition
            // is parametrized to allow it.
            PartInfo[part_idx].zeroizable &&
            // Check that the address is not out-of-bounds.
            part_sel_valid &&
            // Check that the AXI user ID is correct.
            !discard_fuse_write_i &&
            // The entire address space of a zeroizable partition can be cleared
            base_sel_q == DaiOffset) begin
          otp_req_o = 1'b1;
          otp_cmd_o = prim_generic_otp_pkg::Zeroize;
          if (otp_gnt_i) begin
            state_d = ZerWaitSt;
          end
        end else begin
          // Clear working register state.
          discarded_fuse_write_d = 1'b1;
          data_clr = 1'b1;
          state_d = IdleSt;
          error_d = AccessError; // Signal this error, but do not go into terminal error state.
          dai_cmd_done_o = 1'b1;
        end
      end

      ///////////////////////////////////////////////////////////////////
      // Wait for OTP response to the zeroization request. An error or
      // a non-zeroized value will not be returned to software. Note that
      // in order to retry a failed zeroization requeset all errors are
      // treated as recoverable.
      ZerWaitSt: begin
        dai_prog_idle_o = 1'b0;
        // Continuously check write access and bail out if this is not consistent.
        if (PartInfo[part_idx].zeroizable &&
            // The entire address space of a zeroizable partition is writable.
            base_sel_q == DaiOffset) begin
          if (otp_rvalid_i) begin

            dai_cmd_done_o = 1'b1;
            state_d = IdleSt;

            if (otp_err == NoError) begin
              if (PartInfo[part_idx].secret) begin
                // Only release the zeroized fuse when the read out data reaches
                // the valid threshold.
                if (mubi16_test_true_strict(zeroized_valid)) begin
                  data_en = 1'b1;
                  // Flop trigger for the affected partition such that it can disable
                  // periodic checks that could fail.
                  zer_trigs_d[part_idx] = MuBi8True;
                end
              // For software partitions, the read out data is always released.
              end else begin
                data_en = 1'b1;
              end

            end else begin
              error_d = otp_err;
            end
          end
        // At this point, this check MUST succeed - otherwise this means that
        // there was a tampering attempt. Hence we go into a terminal error state
        // when this check fails.
        end else begin
          state_d = ErrorSt;
          error_d = FsmStateError;
        end
      end

      ///////////////////////////////////////////////////////////////////
      // Terminal Error State. This locks access to the DAI. Make sure
      // an FsmStateError error code is assigned here, in case no error code has
      // been assigned yet.
      ErrorSt: begin
        if (error_q == NoError) begin
          error_d = FsmStateError;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // We should never get here. If we do (e.g. via a malicious
      // glitch), error out immediately.
      default: begin
        state_d = ErrorSt;
        fsm_err_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of escalation.
    // SEC_CM: DAI.FSM.LOCAL_ESC, DAI.FSM.GLOBAL_ESC
    if (lc_ctrl_pkg::lc_tx_test_true_loose(escalate_en_i) || cnt_err) begin
      state_d = ErrorSt;
      fsm_err_o = 1'b1;
      if (state_q != ErrorSt) begin
        error_d = FsmStateError;
      end
    end
    // Unconditionally jump into the terminal error state when a zeroization
    // indicator takes on an invalid value.
    for (int k = 0; k < NumPart; k++) begin
      if (mubi8_test_invalid(zer_trigs_o[k]) || mubi16_test_invalid(zeroized_valid)) begin
        state_d = ErrorSt;
        fsm_err_o = 1'b1;
        error_d = FsmStateError;
      end
    end
  end

  ////////////////////////////
  // Partition Select Logic //
  ////////////////////////////

  // This checks which partition the address belongs to by comparing
  // the incoming address to the partition address ranges. The onehot
  // bitvector generated by the parallel comparisons is fed into a
  // binary tree that determines the partition index with O(log(N)) delay.

  logic [NumPart-1:0] part_sel_oh;
  for (genvar k = 0; k < NumPart; k++) begin : gen_part_sel
    localparam int unsigned PartEndInt = 32'(PartInfo[k].offset) + 32'(PartInfo[k].size);
    localparam int unsigned DigestOffsetInt = PartEndInt - (ScrmblBlockWidth / 8) - (PartInfo[k].zeroizable ? 8 : 0);
    localparam int unsigned DigestAddrLutInt = DigestOffsetInt >> OtpAddrShift;

    localparam int unsigned ZeroizeOffsetInt = PartEndInt - (ScrmblBlockWidth / 8);
    localparam int unsigned ZeroizeAddrLutInt = ZeroizeOffsetInt >> OtpAddrShift;

    // PartEnd has an extra bit to cope with the case where offset + size overflows. However, we
    // arrange the address map to make sure that PartEndInt is at most 1 << OtpByteAddrWidth. Check
    // that here.
    `CALIPTRA_ASSERT_INIT(PartEndMax_A, PartEndInt <= (1 << OtpByteAddrWidth))

    // The shift right by OtpAddrShift drops exactly the bottom bits that are needed to convert
    // between OtpAddrWidth and OtpByteAddrWidth, so we know that we can slice safely here.
    localparam bit [OtpAddrWidth-1:0] DigestAddrLut = DigestAddrLutInt[OtpAddrWidth-1:0];
    localparam bit [OtpAddrWidth-1:0] ZeroizeAddrLut = ZeroizeAddrLutInt[OtpAddrWidth-1:0];

    if (PartInfo[k].offset == 0) begin : gen_zero_offset
      assign part_sel_oh[k] = ({1'b0, dai_addr_i} < PartEndInt[OtpByteAddrWidth:0]);

    end else begin : gen_nonzero_offset
      assign part_sel_oh[k] = (dai_addr_i >= PartInfo[k].offset) &
                              ({1'b0, dai_addr_i} < PartEndInt[OtpByteAddrWidth:0]);
    end
    assign digest_addr_lut[k] = DigestAddrLut;
    assign zeroize_addr_lut[k] = ZeroizeAddrLut;
  end

  `CALIPTRA_ASSERT(ScrmblBlockWidthGe8_A, ScrmblBlockWidth >= 8)
  `CALIPTRA_ASSERT(PartSelMustBeOnehot_A, $onehot0(part_sel_oh))

  caliptra_prim_arbiter_fixed #(
    .N(NumPart),
    .EnDataPort(0)
  ) u_part_sel_idx (
    .clk_i,
    .rst_ni,
    .req_i   ( part_sel_oh    ),
    .data_i  ( '{default: '0} ),
    .gnt_o   (                ), // unused
    .idx_o   ( part_idx       ),
    .valid_o ( part_sel_valid ), // used for detecting OOB addresses
    .data_o  (                ), // unused
    .ready_i ( 1'b0           )
  );

  /////////////////////////////////////
  // Address Calculations for Digest //
  /////////////////////////////////////

  // Depending on whether this is a 32bit or 64bit partition, we cut off the lower address bits.
  // Access sizes are either 64bit or 32bit, depending on what region the access goes to.
  logic [OtpByteAddrWidth-1:0] addr_base;
  always_comb begin : p_size_sel
    otp_size_o = OtpSizeWidth'(unsigned'(32 / OtpWidth - 1));
    addr_base = {dai_addr_i[OtpByteAddrWidth-1:2], 2'h0};

    // 64bit transaction for scrambled partitions.
    if (PartInfo[part_idx].secret) begin
      otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
      addr_base = {dai_addr_i[OtpByteAddrWidth-1:3], 3'h0};
    // 64bit transaction if computing a digest.
    end else if (PartInfo[part_idx].hw_digest && (base_sel_q == PartOffset)) begin
        otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
        addr_base = PartInfo[part_idx].offset;
    // 64bit transaction if the DAI address points to the partition's digest offset.
    end else if ((PartInfo[part_idx].hw_digest || PartInfo[part_idx].sw_digest) &&
        (base_sel_q == DaiOffset) &&
        ({dai_addr_i[OtpByteAddrWidth-1:3], 2'b0} == digest_addr_lut[part_idx])) begin
      otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
      addr_base = {dai_addr_i[OtpByteAddrWidth-1:3], 3'h0};
    // 64bit transaction if the DAI address points to the partition's zeroization marker.
    end else if ((PartInfo[part_idx].zeroizable) &&
        (base_sel_q == DaiOffset) &&
        ({dai_addr_i[OtpByteAddrWidth-1:3], 2'b0} == zeroize_addr_lut[part_idx])) begin
      otp_size_o = OtpSizeWidth'(unsigned'(ScrmblBlockWidth / OtpWidth - 1));
      addr_base = {dai_addr_i[OtpByteAddrWidth-1:3], 3'h0};
    end
  end

  // Address counter - this is only used for computing a digest, hence the increment is
  // fixed to 8 byte.
  // SEC_CM: DAI.CTR.REDUN
  caliptra_prim_count #(
    .Width(CntWidth)
  ) u_prim_count (
    .clk_i,
    .rst_ni,
    .clr_i(cnt_clr),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(cnt_en),
    .decr_en_i(1'b0),
    .step_i(CntWidth'(1)),
    .commit_i(1'b1),
    .cnt_o(cnt),
    .cnt_after_commit_o(),
    .err_o(cnt_err)
  );

  // Note that OTP works on halfword (16bit) addresses, hence need to
  // shift the addresses appropriately.
  logic [OtpByteAddrWidth-1:0] addr_calc;
  assign addr_calc = {cnt, {$clog2(ScrmblBlockWidth/8){1'b0}}} + addr_base;
  assign otp_addr_o = OtpAddrWidth'(addr_calc >> OtpAddrShift);

  ///////////////
  // Registers //
  ///////////////

  `CALIPTRA_PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ResetSt)

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      error_q        <= NoError;
      data_q         <= '0;
      base_sel_q     <= DaiOffset;
    end else begin
      error_q        <= error_d;
      base_sel_q     <= base_sel_d;

      // Working register
      if (data_clr) begin
        data_q <= '0;
      end else if (data_en) begin
        if (data_sel == ScrmblData) begin
          data_q <= scrmbl_data_i;
        end else if (data_sel == DaiData) begin
          data_q <= dai_wdata_i;
        end else begin
          data_q <= otp_rdata_i;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : access_block
    if (!rst_ni) begin
      discarded_fuse_write_o        <= '0;
    end else begin
      discarded_fuse_write_o        <= discarded_fuse_write_d;
    end
  end

  // Flop the array of zeroization triggers.
  caliptra_prim_flop #(
    .Width(NumPart*MuBi8Width),
    .ResetValue({NumPart{MuBi8False}})
  ) u_zeroized_flop(
    .clk_i,
    .rst_ni,
    .d_i(zer_trigs_d),
    .q_o({zer_trigs_o})
  );

  ////////////////
  // Assertions //
  ////////////////

  // Known assertions
  `CALIPTRA_ASSERT_KNOWN(InitDoneKnown_A,     init_done_o)
  `CALIPTRA_ASSERT_KNOWN(PartInitReqKnown_A,  part_init_req_o)
  `CALIPTRA_ASSERT_KNOWN(ErrorKnown_A,        error_o)
  `CALIPTRA_ASSERT_KNOWN(DaiIdleKnown_A,      dai_idle_o)
  `CALIPTRA_ASSERT_KNOWN(DaiRdataKnown_A,     dai_rdata_o)
  `CALIPTRA_ASSERT_KNOWN(OtpReqKnown_A,       otp_req_o)
  `CALIPTRA_ASSERT_KNOWN(OtpCmdKnown_A,       otp_cmd_o)
  `CALIPTRA_ASSERT_KNOWN(OtpSizeKnown_A,      otp_size_o)
  `CALIPTRA_ASSERT_KNOWN(OtpWdataKnown_A,     otp_wdata_o)
  `CALIPTRA_ASSERT_KNOWN(OtpAddrKnown_A,      otp_addr_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblMtxReqKnown_A, scrmbl_mtx_req_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblCmdKnown_A,    scrmbl_cmd_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblModeKnown_A,   scrmbl_mode_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblSelKnown_A,    scrmbl_sel_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblDataKnown_A,   scrmbl_data_o)
  `CALIPTRA_ASSERT_KNOWN(ScrmblValidKnown_A,  scrmbl_valid_o)

  // OTP error response
  `CALIPTRA_ASSERT(OtpErrorState_A,
      state_q inside {InitOtpSt, ReadWaitSt, WriteWaitSt, DigReadWaitSt} && otp_rvalid_i &&
      !(otp_err inside {NoError, MacroEccCorrError, MacroWriteBlankError})
      |=>
      state_q == ErrorSt && error_o == $past(otp_err))

endmodule : otp_ctrl_dai
