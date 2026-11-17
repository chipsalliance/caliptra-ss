// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import uvm_pkg::*;

// Verifies SPI host launch/sample stability using the FSM's accepted-command
// configuration (fsm_cpol_i, fsm_cpha_i, fsm_full_cyc_i) rather than live CSR
// reg2hw.configopts, so pipelined mid-command single-bit CPOL/CPHA updates for
// queued descriptors never corrupt active-command sample-edge selection.
//
// Pin ownership / loopback note:
// - cio_sd_o (masked by cio_sd_en_o) and cio_sd_en_o are dedicated host outputs
//   and are checked both continuously on every core clk_i cycle across the active
//   launch-to-sample phase and at the sampling SCK edge.
// - cio_sd_i reflects the resolved pad input (host loopback on driven lanes or
//   external peripheral MISO on input lanes) and is checked when !fsm_full_cyc_i
//   (when FULLCYC=1, external MISO is permitted to transition after the half-cycle
//   edge prior to full-cycle capture).
module spi_host_data_stable_sva #(
  parameter int unsigned NumCS = 1
) (
  input logic                                                     clk_i,
  input logic                                                     rst_ni,
  input logic                                                     active_i,
  input logic                                                     cio_sck_o,
  input logic [NumCS-1:0]                                         cio_csb_o,
  input logic [3:0]                                               cio_sd_o,
  input logic [3:0]                                               cio_sd_i,
  input logic [3:0]                                               cio_sd_en_o,
  input logic                                                     fsm_cpol_i,
  input logic                                                     fsm_cpha_i,
  input logic                                                     fsm_full_cyc_i,
  input caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_req_t passthrough_i
);

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

  // Derived strictly from accepted-command FSM state
  assign sampled_negedge_enable = !csbs & (fsm_cpha_i ^ fsm_cpol_i);
  assign sampled_posedge_enable = !csbs & !sampled_negedge_enable;

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
    .lane_en_i             (cio_sd_en_o),
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
    .lane_en_i             (4'hF),
    .signal2check_i        (cio_sd_en_o),
    .sampled_negedge_enable(sampled_negedge_enable),
    .sampled_posedge_enable(sampled_posedge_enable),
    .passthrough_en        (passthrough_i.passthrough_en)
  );

  // 3. Resolved pad input stability at nominal half-cycle sampling edge when FULLCYC == 0
  whole_cycle_data_stable_signal_checker #(
    .VECTOR_WIDTH       (4),
    .CHECK_CORE_CLK_HOLD(1'b0)
  ) u_sva_cio_sd_i_whole_cycle_data_stable_check (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .sck_o                 (cio_sck_o),
    .csb_o                 (csbs),
    .active_i              (active_i),
    .lane_en_i             (4'hF),
    .signal2check_i        (cio_sd_i),
    .sampled_negedge_enable(sampled_negedge_enable & !fsm_full_cyc_i),
    .sampled_posedge_enable(sampled_posedge_enable & !fsm_full_cyc_i),
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
  input logic [VECTOR_WIDTH-1:0] lane_en_i,
  input logic [VECTOR_WIDTH-1:0] signal2check_i,
  input logic                    sampled_negedge_enable,
  input logic                    sampled_posedge_enable,
  input logic                    passthrough_en
);

  // Track whether we are inside the active launch-to-sample half-cycle on clk_i
  // so transient mid-phase glitches that revert before the sample edge are caught.
  logic in_sample_phase_q;
  logic sck_q, csb_q;
  logic launch_edge_clk;
  logic sample_edge_clk;

  assign launch_edge_clk = (sampled_posedge_enable && (sck_q && !sck_o)) ||
                           (sampled_negedge_enable && (!sck_q && sck_o));
  assign sample_edge_clk = (sampled_posedge_enable && (!sck_q && sck_o)) ||
                           (sampled_negedge_enable && (sck_q && !sck_o));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sck_q             <= 1'b0;
      csb_q             <= 1'b1;
      in_sample_phase_q <= 1'b0;
    end else begin
      sck_q <= sck_o;
      csb_q <= csb_o;
      if (csb_o || passthrough_en || !active_i) begin
        in_sample_phase_q <= 1'b0;
      end else if (sample_edge_clk) begin
        in_sample_phase_q <= 1'b0;
      end else if (launch_edge_clk || ((csb_q && !csb_o) && sampled_posedge_enable)) begin
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
      uvm_report_error("NEGEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED", i),
                        $sformatf(" act_value (0x%0x) != pos_value (0x%0x)",
                                  $sampled(signal2check_i[i]), $sampled(pos_value)),
                        $sformatf(" - time=%t", $time)});
    end

    POSEDGE_SAME_VALUE_CHECK_P: assert property (posedge_no_change_check_p)
    else begin
      uvm_report_error("POSEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED", i),
                        $sformatf(" act_value (0x%0x) != neg_value (0x%0x)",
                                  $sampled(signal2check_i[i]), $sampled(neg_value)),
                        $sformatf(" - time=%t", $time)});
    end

    if (CHECK_CORE_CLK_HOLD) begin : g_core_clk_hold_sva
      CORE_CLK_SAMPLE_PHASE_STABLE_P: assert property (
        @(posedge clk_i) disable iff (!rst_ni || csb_o || passthrough_en || !active_i)
        (in_sample_phase_q && !launch_edge_clk && !sample_edge_clk &&
         !csb_o && !csb_q && active_i && $past(active_i) &&
         lane_en_i[i] && $past(lane_en_i[i]))
        |-> $stable(signal2check_i[i])
      ) else begin
        uvm_report_error("CORE_CLK_SAMPLE_PHASE_STABLE_P",
                         $sformatf("%m: [i=%0d] transient mid-phase change detected on host signal at time=%t",
                                   i, $time));
      end
    end
  end // block: g_signal_stable_sva

endmodule
