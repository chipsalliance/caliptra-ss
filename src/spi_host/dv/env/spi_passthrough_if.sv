// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface spi_passthrough_if
(
  input logic rst_n
);

  // Driven passthrough inputs (4-state logic initialized cleanly to inactive '0 / '1)
  logic       passthrough_en = 1'b0;
  logic       sck            = 1'b0;
  logic       sck_en         = 1'b0;
  logic       csb            = 1'b1;
  logic       csb_en         = 1'b0;
  logic [3:0] is             = 4'h0;
  logic [3:0] s_en           = 4'h0;
  logic [3:0] cio_sd_i       = 4'h0;

  // Sampled 4-state DUT outputs (cio_csb_* widened across both target chip selects)
  logic [3:0] os;
  logic       cio_sck_o;
  logic       cio_sck_en_o;
  logic [1:0] cio_csb_o;
  logic [1:0] cio_csb_en_o;
  logic [3:0] cio_sd_o;
  logic [3:0] cio_sd_en_o;

  // Contention-free internal TL-UL SECDED fault injection controls (wired in tb.sv)
  bit         inject_cmd_intg_err  = 1'b0;
  bit         inject_data_intg_err = 1'b0;

endinterface : spi_passthrough_if
