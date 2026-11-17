// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic default behind css_mcu0_el2_prim_rst_mux2.
//
// This combinational AND/OR mux is not guaranteed glitchless after synthesis.
// Silicon integrations must replace it with a qualified reset mux cell or set
// css_mcu0_RV_PRIM_RST_MUX2_IMPL to an already-mapped implementation.

module css_mcu0_el2_prim_generic_rst_mux2 (
  input        rst0_i,
  input        rst1_i,
  input        sel_i,
  output logic rst_o
);

  assign rst_o = (sel_i & rst1_i) | (~sel_i & rst0_i);

endmodule
