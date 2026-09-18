// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage and protocol assertions for spi_host

`include "caliptra_prim_assert.sv"

interface spi_host_cov_if #(
  parameter int unsigned NumCS = 1
) (
  input logic clk_i,
  input logic rst_ni,
  input logic cio_sck_o,
  input logic cio_sck_en_o,
  input logic [NumCS-1:0] cio_csb_o,
  input logic [NumCS-1:0] cio_csb_en_o,
  input logic [3:0] cio_sd_o,
  input logic [3:0] cio_sd_en_o,
  input logic [3:0] cio_sd_i,
  input logic intr_error_o,
  input logic intr_spi_event_o
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import caliptra_ss_spi_host_reg_pkg::*;
  import caliptra_ss_spi_host_cmd_pkg::*;

  bit en_full_cov = 1'b1;

  // 1. SCK Clock Pin Coverage
  covergroup sck_pin_cg @(posedge clk_i);
    option.per_instance = 1;
    sck_val_cp : coverpoint cio_sck_o;
    sck_en_cp  : coverpoint cio_sck_en_o;
    sck_active_cross : cross sck_val_cp, sck_en_cp;
  endgroup

  // 2. Chip Select Pin Coverage
  covergroup csb_pin_cg @(posedge clk_i);
    option.per_instance = 1;
    csb_val_cp : coverpoint cio_csb_o[0];
    csb_en_cp  : coverpoint cio_csb_en_o[0];
    csb_active_cross : cross csb_val_cp, csb_en_cp;
  endgroup

  // 3. Serial Data (SD) Output Enable Width Coverage
  covergroup sd_en_width_cg @(posedge clk_i);
    option.per_instance = 1;
    sd_en_cp : coverpoint cio_sd_en_o {
      bins disabled  = {4'b0000};
      bins standard  = {4'b0001};
      bins dual      = {4'b0011};
      bins quad      = {4'b1111};
    }
  endgroup

  // 4. Hardware Interrupt Lines Coverage
  covergroup intr_pins_cg @(posedge clk_i);
    option.per_instance = 1;
    intr_err_cp : coverpoint intr_error_o;
    intr_evt_cp : coverpoint intr_spi_event_o;
    intr_cross  : cross intr_err_cp, intr_evt_cp;
  endgroup

  // Instantiate covergroups
  sck_pin_cg      u_sck_pin_cg = new();
  csb_pin_cg      u_csb_pin_cg = new();
  sd_en_width_cg  u_sd_en_width_cg = new();
  intr_pins_cg    u_intr_pins_cg = new();

  // 5. Protocol Timing Cover Properties (SVA Coverage)
  // Cover SCK running while CS is asserted
  property p_csb_active_sck_toggles;
    @(posedge clk_i) disable iff (!rst_ni)
    (!cio_csb_o[0] && cio_sck_en_o) ##1 $changed(cio_sck_o);
  endproperty
  c_csb_active_sck_toggles: cover property (p_csb_active_sck_toggles);

  // Cover Quad-mode active data transmission
  property p_quad_mode_transfer;
    @(posedge clk_i) disable iff (!rst_ni)
    (!cio_csb_o[0] && cio_sd_en_o == 4'b1111);
  endproperty
  c_quad_mode_transfer: cover property (p_quad_mode_transfer);

  // Cover Dual-mode active data transmission
  property p_dual_mode_transfer;
    @(posedge clk_i) disable iff (!rst_ni)
    (!cio_csb_o[0] && cio_sd_en_o == 4'b0011);
  endproperty
  c_dual_mode_transfer: cover property (p_dual_mode_transfer);

  // Cover Standard-mode active data transmission
  property p_standard_mode_transfer;
    @(posedge clk_i) disable iff (!rst_ni)
    (!cio_csb_o[0] && cio_sd_en_o == 4'b0001);
  endproperty
  c_standard_mode_transfer: cover property (p_standard_mode_transfer);

  // Cover CS deassertion (CS inactive high) between transfers
  property p_csb_idle_between_trans;
    @(posedge clk_i) disable iff (!rst_ni)
    $fell(cio_csb_o[0]) ##[1:$] $rose(cio_csb_o[0]) ##[1:50] $fell(cio_csb_o[0]);
  endproperty
  c_csb_idle_between_trans: cover property (p_csb_idle_between_trans);

endinterface
