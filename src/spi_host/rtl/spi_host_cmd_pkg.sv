// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Command & Configuration Options structure for SPI HOST.
//

package caliptra_ss_spi_host_cmd_pkg;

  parameter int CSW = caliptra_prim_util_pkg::vbits(caliptra_ss_spi_host_reg_pkg::NumCS);
  parameter int CmdSize = CSW + 45;

  // For decoding the direction register
  typedef enum logic [1:0] {
     Dummy  = 2'b00,
     RdOnly = 2'b01,
     WrOnly = 2'b10,
     Bidir  = 2'b11
   } caliptra_ss_reg_direction_t;

  // For decoding the direction register
  typedef enum logic [1:0] {
     Standard = 2'b00,
     Dual     = 2'b01,
     Quad     = 2'b10,
     RsvdSpd  = 2'b11
   } caliptra_ss_speed_t;

  typedef struct packed {
    logic [15:0] clkdiv;
    logic [3:0]  csnidle;
    logic [3:0]  csnlead;
    logic [3:0]  csntrail;
    logic        full_cyc;
    logic        cpha;
    logic        cpol;
  } caliptra_ss_configopts_t;

  typedef struct packed {
    logic [1:0]  speed;
    logic        cmd_wr_en;
    logic        cmd_rd_en;
    logic [19:0] len;
    logic        csaat;
  } caliptra_ss_segment_t;

  typedef struct packed {
    logic [CSW-1:0] csid;
    caliptra_ss_segment_t segment;
    caliptra_ss_configopts_t configopts;
  } caliptra_ss_command_t;

endpackage
