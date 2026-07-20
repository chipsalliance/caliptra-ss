// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AXI write response channel

interface axi_write_response_if (input clk_i, input rst_ni);
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Device, dv_utils_pkg::Monitor;

  // The interface mode.
  //
  //  - Host:    An agent is driving the interface signals through mgr_cb, acting as a Manager.
  //  - Device:  An agent is driving the interface signals through sub_cb, acting as a Subordinate.
  //  - Monitor: No agent is driving interface signals and the interface is purely passive.
  if_mode_e if_mode = Monitor;

  // The ID_W_WIDTH property. Set this by calling set_id_w_width().
  int unsigned id_w_width = 32;

  // The BRESP_WIDTH property. Set this by calling set_bresp_width().
  int unsigned bresp_width = 3;

  // The USER_RESP_WIDTH property. Set this by calling set_user_resp_width().
  int unsigned user_resp_width = 16;

  // The core defined signals for the write response channel.
  //
  // This interface uses a max footprint approach. Signals of configurable width (like wdata) might
  // only use the lower bits.
  //
  // Not all possible write response channel signals are included. Not included are:
  //
  //    - BTRACE    (Trace_Signals is false)
  //    - BLOOP     (Loopback_Signals is false)
  //    - BBUSY     (Busy_Support is false)
  //    - BIDUNQ    (Unique_ID_Support is false)
  //    - BCOMP     (Neither cache maintence for persistence nor memory tagging are supported)
  //    - BPERSIST  (Persist_CMO is false)
  //    - BTAGMATCH (MTE_Support is false)
  wire         bvalid;
  wire         bready;
  wire [31:0]  bid;
  wire [2:0]   bresp;
  wire [15:0]  buser;

  // A copy of bready, which is driven by mgr_cb (only used if if_mode == Host). The bready_driven
  // signal is directly driven by the clocking block. The bready_internal signal tracks it, but is
  // also cleared on reset.
  logic         bready_driven, bready_internal;

  // Copies of the signals that are driven by sub_cb (only used if if_mode == Device). The
  // "*_driven" signals are directly driven by the clocking block. The "*_internal" signals track
  // these, but take masks into account for signals with configurable length and are also cleared on
  // reset.
  logic        bvalid_driven, bvalid_internal;
  logic [31:0] bid_driven, bid_internal;
  logic [2:0]  bresp_driven, bresp_internal;
  logic [15:0] buser_driven, buser_internal;

  // Masks used when converting some *_driven signals to *_internal
  logic [31:0] bid_mask;
  logic [2:0]  bresp_mask;
  logic [15:0] buser_mask;

  assign bid_mask   = (32'b1 << id_w_width) - 1;
  assign bresp_mask = (3'b1 << bresp_width) - 1;
  assign buser_mask = (16'b1 << user_resp_width) - 1;

  clocking mon_cb @(posedge clk_i);
    input bvalid;
    input bready;
    input bid;
    input bresp;
    input buser;
  endclocking

  clocking mgr_cb @(posedge clk_i);
    input  bvalid;
    output bready = bready_driven;
    input  bid;
    input  bresp;
    input  buser;
  endclocking

  clocking sub_cb @(posedge clk_i);
    output bvalid = bvalid_driven;
    input  bready;
    output bid    = bid_driven;
    output bresp  = bresp_driven;
    output buser  = buser_driven;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      bvalid_internal = '0;
      bready_internal = '0;
      bid_internal    = '0;
      bresp_internal  = '0;
      buser_internal  = '0;
    end else begin
      bvalid_internal = bvalid_driven;
      bready_internal = bready_driven;
      bid_internal    = bid_driven & bid_mask;
      bresp_internal  = bresp_driven & bresp_mask;
      buser_internal  = buser_driven & buser_mask;
    end
  end

  assign bvalid = (if_mode == Device) ? bvalid_internal : 'z;
  assign bready = (if_mode == Host)   ? bready_internal : 'z;
  assign bid    = (if_mode == Device) ? bid_internal    : 'z;
  assign bresp  = (if_mode == Device) ? bresp_internal  : 'z;
  assign buser  = (if_mode == Device) ? buser_internal  : 'z;

  // Set the ID_W_WIDTH property. The allowed range is 0..32 (see AMBA AXI protocol specification,
  // issue J, section B1.3)
  function void set_id_w_width(int unsigned width);
    if (width > 32) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set ID_W_WIDTH to %0d: maximum in spec is 32.", width))
      width = 32;
    end

    id_w_width = width;
  endfunction

  // Set the BRESP_WIDTH property. The allowed values are 0, 2, 3 (see AMBA AXI protocol
  // specification, issue J, section B1.3)
  function void set_bresp_width(int unsigned width);
    if (! (width inside {0, 2, 3})) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set BRESP_WIDTH to %0d: must be 0, 2 or 3.", width))
      width = 3;
    end

    bresp_width = width;
  endfunction

  // Set the USER_RESP_WIDTH property. The allowed range is 0..16 (see AMBA AXI protocol
  // specification, issue J, section B1.3)
  function void set_user_resp_width(int unsigned width);
    if (width > 16) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set USER_RESP_WIDTH to %0d: maximum in spec is 16.", width))
      width = 16;
    end

    user_resp_width = width;
  endfunction

endinterface
