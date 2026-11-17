// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage and protocol assertions for spi_host across all NumCS chip selects

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

  `include "uvm_macros.svh"

  bit en_full_cov = 1'b1;

  // 1. SCK Clock Pin Coverage
  covergroup sck_pin_cg @(posedge clk_i);
    option.per_instance = 1;
    sck_val_cp : coverpoint cio_sck_o;
    sck_en_cp  : coverpoint cio_sck_en_o;
    sck_active_cross : cross sck_val_cp, sck_en_cp;
  endgroup

  // 2.Serial Data (SD) Output Enable Width Coverage
  covergroup sd_en_width_cg @(posedge clk_i);
    option.per_instance = 1;
    sd_en_cp : coverpoint cio_sd_en_o {
      bins disabled  = {4'b0000};
      bins standard  = {4'b0001};
      bins dual      = {4'b0011};
      bins quad      = {4'b1111};
    }
  endgroup

  // 3. Hardware Interrupt Lines Coverage
  covergroup intr_pins_cg @(posedge clk_i);
    option.per_instance = 1;
    intr_err_cp : coverpoint intr_error_o;
    intr_evt_cp : coverpoint intr_spi_event_o;
    intr_cross  : cross intr_err_cp, intr_evt_cp;
  endgroup

  // Instantiate shared pin covergroups
  sck_pin_cg      u_sck_pin_cg     = new();
  sd_en_width_cg  u_sd_en_width_cg = new();
  intr_pins_cg    u_intr_pins_cg   = new();

  // 4. Per-Chip-Select Pin Coverage across all NumCS lines (CS0 .. CS[NumCS-1])
  for (genvar cs = 0; cs < NumCS; cs++) begin : gen_csb_cov
    covergroup csb_pin_cg @(posedge clk_i);
      option.per_instance = 1;
      csb_val_cp : coverpoint cio_csb_o[cs];
      csb_en_cp  : coverpoint cio_csb_en_o[cs];
      csb_active_cross : cross csb_val_cp, csb_en_cp;
    endgroup
    csb_pin_cg u_csb_pin_cg = new();
  end : gen_csb_cov

  // 5. Multi-CS Mutual-Exclusion Assertion & Per-CS Protocol Timing Cover Properties (SVA)
  property p_csb_onehot0;
    @(posedge clk_i) disable iff (!rst_ni)
    $onehot0(~cio_csb_o);
  endproperty
  a_csb_onehot0: assert property (p_csb_onehot0)
    else `uvm_error("spi_host_cov_if", $sformatf("Multiple cio_csb_o lines active low: 0b%b", cio_csb_o))
  c_csb_onehot0: cover property (p_csb_onehot0);

  for (genvar cs = 0; cs < NumCS; cs++) begin : gen_cs_protocol_cov
    // Cover SCK running while CS[cs] is asserted
    property p_csb_active_sck_toggles;
      @(posedge clk_i) disable iff (!rst_ni)
      (!cio_csb_o[cs] && cio_sck_en_o) ##1 $changed(cio_sck_o);
    endproperty
    c_csb_active_sck_toggles: cover property (p_csb_active_sck_toggles);

    // Cover Quad-mode active data transmission on CS[cs]
    property p_quad_mode_transfer;
      @(posedge clk_i) disable iff (!rst_ni)
      (!cio_csb_o[cs] && cio_sd_en_o == 4'b1111);
    endproperty
    c_quad_mode_transfer: cover property (p_quad_mode_transfer);

    // Cover Dual-mode active data transmission on CS[cs]
    property p_dual_mode_transfer;
      @(posedge clk_i) disable iff (!rst_ni)
      (!cio_csb_o[cs] && cio_sd_en_o == 4'b0011);
    endproperty
    c_dual_mode_transfer: cover property (p_dual_mode_transfer);

    // Cover Standard-mode active data transmission on CS[cs]
    property p_standard_mode_transfer;
      @(posedge clk_i) disable iff (!rst_ni)
      (!cio_csb_o[cs] && cio_sd_en_o == 4'b0001);
    endproperty
    c_standard_mode_transfer: cover property (p_standard_mode_transfer);

    // Cover CS[cs] deassertion (CS inactive high) between transfers
    property p_csb_idle_between_trans;
      @(posedge clk_i) disable iff (!rst_ni)
      $fell(cio_csb_o[cs]) ##[1:$] $rose(cio_csb_o[cs]) ##[1:50] $fell(cio_csb_o[cs]);
    endproperty
    c_csb_idle_between_trans: cover property (p_csb_idle_between_trans);
  end : gen_cs_protocol_cov

endinterface
