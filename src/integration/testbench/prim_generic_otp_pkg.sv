// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Common interface definitions for OTP primitives.

package prim_generic_otp_pkg;

  // The command is sparsely encoded to make it more difficult to tamper with.
  parameter int CmdWidth = 7;
  parameter int ErrWidth = 3;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 4 -m 6 -n 7 \
  //     -s 787759652 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //  6: --
  //  7: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  typedef enum logic [CmdWidth-1:0] {
    Read     = 7'b1111010,
    Write    = 7'b1001001,
    // Raw commands ignore integrity
    ReadRaw  = 7'b1010100,
    WriteRaw = 7'b1100111,
    Init     = 7'b0100000,
    Zeroize  = 7'b0111101
  } cmd_e;

  typedef enum logic [ErrWidth-1:0] {
    NoError              = 3'h0,
    MacroError           = 3'h1,
    MacroEccCorrError    = 3'h2,
    MacroEccUncorrError  = 3'h3,
    MacroWriteBlankError = 3'h4,
    MacroZeroizeError    = 3'h5
  } err_e;

endpackage : prim_generic_otp_pkg
