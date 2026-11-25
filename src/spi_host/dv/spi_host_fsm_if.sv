// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Passive observer interface bound into caliptra_ss_spi_host_core to monitor FSM state
// transitions without forcing any internal RTL signals.
interface spi_host_fsm_if ();
  // Retained as a passive 0 flag for backward compatibility; all sequences run unforced.
  bit fast_mode = 1'b0;

  // Passively observe FSM state, bit counter, and software reset input
  logic       fsm_clk;
  logic [2:0] fsm_state;
  logic [2:0] fsm_bit_cntr;
  logic       fsm_sw_rst;

  assign fsm_clk      = u_fsm.clk_i;
  assign fsm_state    = u_fsm.state_q;
  assign fsm_bit_cntr = u_fsm.bit_cntr_q;
  assign fsm_sw_rst   = u_fsm.sw_rst_i;
endinterface
