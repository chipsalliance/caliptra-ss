// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_assert.sv"

`ifdef UVM
import uvm_pkg::*;
`endif

// Verifies SPI host launch/sample stability using the FSM's accepted-command
// configuration (fsm_cpol_i, fsm_cpha_i) rather than live CSR
// reg2hw.configopts, so pipelined mid-command single-bit CPOL/CPHA updates for
// queued descriptors never corrupt active-command sample-edge selection.
//
// Pin ownership / loopback note:
// - cio_sd_o (masked by cio_sd_en_o) and cio_sd_en_o are dedicated host outputs
//   and are checked both continuously on every core clk_i cycle across the active
//   launch-to-sample phase (including across the sampling SCK edge and at clkdiv==0)
//   and at the sampling SCK edge.
// - cio_sd_i pad loopback is checked on host-driven lanes (cio_sd_en_o & {4{cio_sck_en_o}}),
//   verifying pad loopback without over-constraining legal peripheral tCLQV > 1ps on input lanes.
module spi_host_data_stable_sva #(
  parameter int unsigned NumCS = 1
) (
  input logic                                                     clk_i,
  input logic                                                     rst_ni,
  input logic                                                     active_i,
  input logic                                                     cio_sck_o,
  input logic                                                     cio_sck_en_o,
  input logic [NumCS-1:0]                                         cio_csb_o,
  input logic [3:0]                                               cio_sd_o,
  input logic [3:0]                                               cio_sd_i,
  input logic [3:0]                                               cio_sd_en_o,
  input logic                                                     fsm_cpol_i,
  input logic                                                     fsm_cpha_i,
  input logic [1:0]                                               fsm_cmd_speed_d_i,
  input logic                                                     fsm_cmd_rd_en_d_i,
  input logic                                                     fsm_cmd_wr_en_d_i,
  input logic [31:0]                                              fsm_csid_i,
  input caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_req_t passthrough_i
);

  // Active !rst_ni counterparts for RTL configuration/command invariants whose inline
  // CALIPTRA_ASSERT macros pass active-low rst_ni instead of !rst_ni (P0-1):
  if (NumCS > 1) begin : gen_passthrough_numcs_sva
    `CALIPTRA_ASSERT(PassthroughNumCSCompat_Bound_A, !passthrough_i.passthrough_en, clk_i, !rst_ni)
  end
  `CALIPTRA_ASSERT(BidirOnlyInStdMode_Bound_A,
                   (fsm_cmd_speed_d_i == caliptra_ss_spi_host_cmd_pkg::Standard) ||
                   !(fsm_cmd_rd_en_d_i && fsm_cmd_wr_en_d_i),
                   clk_i, !rst_ni)
  `CALIPTRA_ASSERT(ValidSpeed_Bound_A,
                   fsm_cmd_speed_d_i != caliptra_ss_spi_host_cmd_pkg::RsvdSpd,
                   clk_i, !rst_ni)
  `CALIPTRA_ASSERT(ValidCSID_Bound_A, fsm_csid_i < NumCS, clk_i, !rst_ni)

  // Truth table:
  // ---------------------------------
  // CPHA | CPOL | posedge | negedge |
  // ---------------------------------
  // 0    | 0    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // 0    | 1    | 0       | 1       | -> XOR(cpha, cpol):  drive posedge, sample negedge
  // 1    | 0    | 0       | 1       | -> XOR(cpha, cpol):  drive posedge, sample negedge
  // 1    | 1    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // ---------------------------------

  logic csbs;
  logic sampled_negedge_enable;
  logic sampled_posedge_enable;

  assign csbs = &cio_csb_o;

  // Derived strictly from accepted-command FSM state while output buffers are enabled
  assign sampled_negedge_enable = !csbs & cio_sck_en_o & (fsm_cpha_i ^ fsm_cpol_i);
  assign sampled_posedge_enable = !csbs & cio_sck_en_o & !(fsm_cpha_i ^ fsm_cpol_i);

  // 1. Dedicated host TX output data stability (cio_sd_o on enabled lanes)
  whole_cycle_data_stable_signal_checker #(
    .VECTOR_WIDTH       (4),
    .CHECK_CORE_CLK_HOLD(1'b1)
  ) u_sva_cio_sd_o_whole_cycle_data_stable_check (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .sck_o                 (cio_sck_o),
    .csb_o                 (csbs),
    .active_i              (active_i),
    .fsm_cpha_i            (fsm_cpha_i),
    .lane_en_i             (cio_sd_en_o & {4{cio_sck_en_o}}),
    .signal2check_i        (cio_sd_o & cio_sd_en_o),
    .sampled_negedge_enable(sampled_negedge_enable),
    .sampled_posedge_enable(sampled_posedge_enable),
    .passthrough_en        (passthrough_i.passthrough_en)
  );

  // 2. Host output-enable stability across the sampling phase
  whole_cycle_data_stable_signal_checker #(
    .VECTOR_WIDTH       (4),
    .CHECK_CORE_CLK_HOLD(1'b1)
  ) u_sva_cio_sd_en_o_whole_cycle_data_stable_check (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .sck_o                 (cio_sck_o),
    .csb_o                 (csbs),
    .active_i              (active_i),
    .fsm_cpha_i            (fsm_cpha_i),
    .lane_en_i             ({4{cio_sck_en_o}}),
    .signal2check_i        (cio_sd_en_o),
    .sampled_negedge_enable(sampled_negedge_enable),
    .sampled_posedge_enable(sampled_posedge_enable),
    .passthrough_en        (passthrough_i.passthrough_en)
  );

  // 3. Resolved pad loopback stability on host-driven lanes across all modes (incl. FULLCYC)
  whole_cycle_data_stable_signal_checker #(
    .VECTOR_WIDTH       (4),
    .CHECK_CORE_CLK_HOLD(1'b0)
  ) u_sva_cio_sd_i_whole_cycle_data_stable_check (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .sck_o                 (cio_sck_o),
    .csb_o                 (csbs),
    .active_i              (active_i),
    .fsm_cpha_i            (fsm_cpha_i),
    .lane_en_i             (cio_sd_en_o & {4{cio_sck_en_o}}),
    .signal2check_i        (cio_sd_i),
    .sampled_negedge_enable(sampled_negedge_enable),
    .sampled_posedge_enable(sampled_posedge_enable),
    .passthrough_en        (passthrough_i.passthrough_en)
  );

endmodule // spi_host_data_stable_sva


module whole_cycle_data_stable_signal_checker #(
  parameter int VECTOR_WIDTH        = 4,
  parameter bit CHECK_CORE_CLK_HOLD = 1'b1
) (
  input logic                    clk_i,
  input logic                    rst_ni,
  input logic                    sck_o,
  input logic                    csb_o,
  input logic                    active_i,
  input logic                    fsm_cpha_i,
  input logic [VECTOR_WIDTH-1:0] lane_en_i,
  input logic [VECTOR_WIDTH-1:0] signal2check_i,
  input logic                    sampled_negedge_enable,
  input logic                    sampled_posedge_enable,
  input logic                    passthrough_en
);

  // Track whether we are inside the active launch-to-sample half-cycle on clk_i
  // so transient mid-phase glitches (and simultaneous NBA glitches at the sampling SCK edge)
  // are caught across all 4 (CPOL, CPHA) modes and all clkdiv values including clkdiv == 0.
  logic in_sample_phase_q;
  logic sck_q, csb_q, active_q;
  logic launch_edge_clk;
  logic sample_edge_clk;
  logic lead_launch_clk;

  assign launch_edge_clk = (sampled_posedge_enable && (sck_q && !sck_o)) ||
                           (sampled_negedge_enable && (!sck_q && sck_o));
  assign sample_edge_clk = (sampled_posedge_enable && (!sck_q && sck_o)) ||
                           (sampled_negedge_enable && (sck_q && !sck_o));
  assign lead_launch_clk = ((csb_q && !csb_o) || (!active_q && active_i && !csb_o)) && !fsm_cpha_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sck_q             <= 1'b0;
      csb_q             <= 1'b1;
      active_q          <= 1'b0;
      in_sample_phase_q <= 1'b0;
    end else begin
      sck_q    <= sck_o;
      csb_q    <= csb_o;
      active_q <= active_i;
      if (csb_o || passthrough_en || !active_i) begin
        in_sample_phase_q <= 1'b0;
      end else if (sample_edge_clk) begin
        in_sample_phase_q <= 1'b0;
      end else if (launch_edge_clk || lead_launch_clk) begin
        in_sample_phase_q <= 1'b1;
      end
    end
  end

  for (genvar i = 0; i < VECTOR_WIDTH; i++) begin : g_signal_stable_sva
    logic neg_value, pos_value;

    always @(negedge sck_o or negedge csb_o or posedge active_i) begin
      #1ps neg_value = signal2check_i[i];
    end
    always @(posedge sck_o or negedge csb_o or posedge active_i) begin
      #1ps pos_value = signal2check_i[i];
    end

    property posedge_no_change_check_p;
      @(posedge sck_o) disable iff (!rst_ni || csb_o || passthrough_en || !lane_en_i[i])
        sampled_posedge_enable |-> (signal2check_i[i] === neg_value);
    endproperty

    property negedge_no_change_check_p;
      @(negedge sck_o) disable iff (!rst_ni || csb_o || passthrough_en || !lane_en_i[i])
        sampled_negedge_enable |-> (signal2check_i[i] === pos_value);
    endproperty

    NEGEDGE_SAME_VALUE_CHECK_P: assert property (negedge_no_change_check_p)
    else begin
`ifdef UVM
      uvm_report_error("NEGEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED", i),
                        $sformatf(" act_value (0x%0x) != pos_value (0x%0x)",
                                  $sampled(signal2check_i[i]), $sampled(pos_value)),
                        $sformatf(" - time=%t", $time)});
`else
      $error("%m: [i=%0d] NEGEDGE_SAME_VALUE_CHECK_P failed: act=0x%0x exp=0x%0x time=%t",
             i, $sampled(signal2check_i[i]), $sampled(pos_value), $time);
`endif
    end

    POSEDGE_SAME_VALUE_CHECK_P: assert property (posedge_no_change_check_p)
    else begin
`ifdef UVM
      uvm_report_error("POSEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED", i),
                        $sformatf(" act_value (0x%0x) != neg_value (0x%0x)",
                                  $sampled(signal2check_i[i]), $sampled(neg_value)),
                        $sformatf(" - time=%t", $time)});
`else
      $error("%m: [i=%0d] POSEDGE_SAME_VALUE_CHECK_P failed: act=0x%0x exp=0x%0x time=%t",
             i, $sampled(signal2check_i[i]), $sampled(neg_value), $time);
`endif
    end

    if (CHECK_CORE_CLK_HOLD) begin : g_core_clk_hold_sva
      CORE_CLK_SAMPLE_PHASE_STABLE_P: assert property (
        @(posedge clk_i) disable iff (!rst_ni || csb_o || passthrough_en || !active_i)
        (in_sample_phase_q && !launch_edge_clk &&
         !csb_o && !csb_q && active_i && active_q &&
         lane_en_i[i] && $past(lane_en_i[i]))
        |-> $stable(signal2check_i[i])
      ) else begin
`ifdef UVM
        uvm_report_error("CORE_CLK_SAMPLE_PHASE_STABLE_P",
                         $sformatf("%m: [i=%0d] transient mid-phase change detected on host signal at time=%t",
                                   i, $time));
`else
        $error("%m: [i=%0d] CORE_CLK_SAMPLE_PHASE_STABLE_P failed at time=%t", i, $time);
`endif
      end
    end
  end // block: g_signal_stable_sva

endmodule
