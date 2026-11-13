// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Integrators select a technology-specific implementation with
// css_mcu0_RV_PRIM_RST_MUX2_IMPL; the standalone default is generic RTL.
`ifndef css_mcu0_RV_PRIM_RST_MUX2_IMPL
  `define css_mcu0_RV_PRIM_RST_MUX2_IMPL css_mcu0_el2_prim_generic_rst_mux2
`endif

module css_mcu0_el2_prim_rst_mux2 (
  input        rst0_i,
  input        rst1_i,
  input        sel_i,
  output logic rst_o
);
  `css_mcu0_RV_PRIM_RST_MUX2_IMPL u_impl (.rst0_i(rst0_i), .rst1_i(rst1_i), .sel_i(sel_i), .rst_o(rst_o));
endmodule
