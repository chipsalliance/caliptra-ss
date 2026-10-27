// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import uvm_pkg::*;

module spi_host_data_stable_sva #(
  parameter int unsigned NumCS = 1
) (
  input logic                                              rst_ni,
  input logic                                              cio_sck_o,
  input logic [NumCS-1:0]                                  cio_csb_o,
  input logic [3:0]                                        cio_sd_i,
  input logic [3:0]                                        cio_sd_en_o,
  input caliptra_ss_spi_host_reg_pkg::caliptra_ss_spi_host_reg2hw_configopts_mreg_t [NumCS-1:0] configopts,
  input caliptra_ss_spi_device_pkg::caliptra_ss_passthrough_req_t                  passthrough_i
 );

  // Check to ensure cio_sd_o[i] stays stable for a whole clock cycle
  // Truth table:
  // ---------------------------------
  // CPHA | CPOL | posedge | negedge |
  // ---------------------------------
  // 0    | 0    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // 0    | 1    | 0       | 1       | -> XOR(cpha, cpol): drive posedge, sample negedge
  // 1    | 0    | 0       | 1       | -> XOR(cpha, cpol): drive posedge, sample negedge
  // 1    | 1    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // ---------------------------------


  // Driven in pos-edge, sampled in neg-edge
  reg    sampled_negedge_enable;
  // Driven in neg-edge, sampled in pos-edge
  reg    sampled_posedge_enable;
  logic  csbs;
  logic  active_cpha;
  logic  active_cpol;

  assign csbs = &cio_csb_o;

  // Select configopts corresponding to the active (low) chip-select line
  always_comb begin
    active_cpha = configopts[0].cpha.q;
    active_cpol = configopts[0].cpol.q;
    for (int i = 0; i < NumCS; i++) begin
      if (!cio_csb_o[i]) begin
        active_cpha = configopts[i].cpha.q;
        active_cpol = configopts[i].cpol.q;
      end
    end
  end

  // HIGH when driven on pos-edge, sampled on the negedge
  assign sampled_negedge_enable = !csbs & (active_cpha ^ active_cpol);
  assign sampled_posedge_enable = !csbs & !sampled_negedge_enable;

  whole_cycle_data_stable_signal_checker #(.VECTOR_WIDTH(4))
  u_sva_cio_sd_i_whole_cycle_data_stable_check (
     .rst_ni (rst_ni),
     .sck_o (cio_sck_o),
     .csb_o (csbs),
     .active_i (u_spi_core.active_o),
     .signal2check_i (cio_sd_i),
     .sampled_negedge_enable (sampled_negedge_enable),
     .sampled_posedge_enable (sampled_posedge_enable),
     .passthrough_en (passthrough_i.passthrough_en)
     );

  whole_cycle_data_stable_signal_checker #(.VECTOR_WIDTH(4))
  u_sva_cio_sd_en_o_whole_cycle_data_stable_check (
     .rst_ni (rst_ni),
     .sck_o (cio_sck_o),
     .csb_o (csbs),
     .active_i (u_spi_core.active_o),
     .signal2check_i (cio_sd_en_o),
     .sampled_negedge_enable (sampled_negedge_enable),
     .sampled_posedge_enable (sampled_posedge_enable),
     .passthrough_en (passthrough_i.passthrough_en)
     );


endmodule // spi_host_data_stable_sva


module whole_cycle_data_stable_signal_checker #( parameter int VECTOR_WIDTH = 4 )
(
 input logic                    rst_ni,
 input logic                    sck_o,
 input logic                    csb_o,
 input logic                    active_i,
 input logic [VECTOR_WIDTH-1:0] signal2check_i,
 input logic                    sampled_negedge_enable,
 input logic                    sampled_posedge_enable,
 input logic                    passthrough_en
 );


  for (genvar i = 0; i < VECTOR_WIDTH; i++) begin : g_signal_stable_sva
    logic neg_value, pos_value;

    // Sample launched value right after the launch edge (or CSB assertion / IdleCSBActive exit
    // for CPHA=0) to verify data remains stable until the sampling edge.
    always @(negedge sck_o or negedge csb_o or posedge active_i) begin
      #1ps neg_value = signal2check_i[i];
    end
    always @(posedge sck_o or negedge csb_o or posedge active_i) begin
      #1ps pos_value = signal2check_i[i];
    end

    // The data bus is driven on one edge and sampled on the next. Hence the value can't
    // toggle in the "sample phase"
    property posedge_no_change_check_p;
      @(posedge sck_o) disable iff (!rst_ni || csb_o || passthrough_en)
        sampled_posedge_enable |-> (signal2check_i[i] === neg_value);
    endproperty

    property negedge_no_change_check_p;
      @(negedge sck_o) disable iff (!rst_ni || csb_o || passthrough_en)
        sampled_negedge_enable |-> (signal2check_i[i] === pos_value);
    endproperty

    NEGEDGE_SAME_VALUE_CHECK_P: assert property (negedge_no_change_check_p)
    else begin
      uvm_report_error("NEGEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                        $sformatf(" act_value (0x%0x) != pos_value (0x%0x)",
                                  $sampled(signal2check_i[i]), $sampled(pos_value)),
                        $sformatf(" - time=%t", $time)});
    end

    POSEDGE_SAME_VALUE_CHECK_P: assert property (posedge_no_change_check_p)
    else begin
       uvm_report_error("POSEDGE_SAME_VALUE_CHECK_P",
                        {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                         $sformatf(" act_value (0x%0x) != neg_value (0x%0x)",
                                   $sampled(signal2check_i[i]), $sampled(neg_value)),
                         $sformatf(" - time=%t", $time)});
    end
  end // block: g_signal_stable_sva

endmodule
