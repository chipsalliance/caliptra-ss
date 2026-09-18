// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AXI write data channel

interface axi_write_data_if (input clk_i, input rst_ni);
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Device, dv_utils_pkg::Monitor;

  // The interface mode.
  //
  //  - Host:    An agent is driving the interface signals through mgr_cb, acting as a Manager.
  //  - Device:  An agent is driving the interface signals through sub_cb, acting as a Subordinate.
  //  - Monitor: No agent is driving interface signals and the interface is purely passive.
  if_mode_e if_mode = Monitor;

  // The DATA_WIDTH property. Set this by calling set_data_width().
  int unsigned data_width = 1024;

  // The USER_DATA_WIDTH property. Set this by calling set_user_data_width().
  int unsigned user_data_width = 512;

  // The core defined signals for the write request channel.
  //
  // This interface uses a max footprint approach. Signals of configurable width (like wdata) might
  // only use the lower bits.
  //
  // Not all possible write data channel signals are included. Not included are:
  //
  //    - WPOISON  (Poison is false)
  //    - WTRACE   (Trace_Signals is false)
  //    - WTAG*    (MTE_Support is false)
  wire          wvalid;
  wire          wready;
  wire [1023:0] wdata;
  wire [127:0]  wstrb;
  wire          wlast;
  wire [511:0]  wuser;

  // Copies of the signals that are driven by mgr_cb (only used if if_mode == Host). The "*_driven"
  // signals are directly driven by the clocking block. The "*_internal" signals track these, but
  // take masks into account for signals with configurable length and are also cleared on reset.
  logic          wvalid_driven, wvalid_internal;
  logic [1023:0] wdata_driven, wdata_internal;
  logic [127:0]  wstrb_driven, wstrb_internal;
  logic          wlast_driven, wlast_internal;
  logic [511:0]  wuser_driven, wuser_internal;

  // A copy of wready, which is driven by sub_cb (only used if if_mode == Device). The
  // wready_driven signal is directly driven by the clocking block. The wready_internal signal
  // tracks it, but is also cleared on reset.
  logic         wready_driven, wready_internal;

  // Masks used when converting some *_driven signals to *_internal
  logic [1023:0] wdata_mask;
  logic [127:0]  wstrb_mask;
  logic [511:0]  wuser_mask;

  assign wdata_mask  = (1024'b1 << data_width) - 1;
  assign wstrb_mask = (128'b1 << ((data_width + 7) / 8)) - 1;
  assign wuser_mask = (512'b1 << user_data_width) - 1;

  clocking mon_cb @(posedge clk_i);
    input wvalid;
    input wready;
    input wdata;
    input wstrb;
    input wlast;
    input wuser;
  endclocking

  clocking mgr_cb @(posedge clk_i);
    output wvalid = wvalid_driven;
    input  wready;
    output wdata  = wdata_driven;
    output wstrb  = wstrb_driven;
    output wlast  = wlast_driven;
    output wuser  = wuser_driven;
  endclocking

  clocking sub_cb @(posedge clk_i);
    input  wvalid;
    output wready = wready_driven;
    input  wdata;
    input  wstrb;
    input  wlast;
    input  wuser;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      wvalid_internal = '0;
      wready_internal = '0;
      wdata_internal  = '0;
      wstrb_internal  = '0;
      wlast_internal  = '0;
      wuser_internal  = '0;
    end else begin
      wvalid_internal = wvalid_driven;
      wready_internal = wready_driven;
      wdata_internal  = wdata_driven & wdata_mask;
      wstrb_internal  = wstrb_driven & wstrb_mask;
      wlast_internal  = wlast_driven;
      wuser_internal  = wuser_driven & wuser_mask;
    end
  end

  assign wvalid = (if_mode == Host)   ? wvalid_internal : 'z;
  assign wready = (if_mode == Device) ? wready_internal : 'z;
  assign wdata  = (if_mode == Host)   ? wdata_internal  : 'z;
  assign wstrb  = (if_mode == Host)   ? wstrb_internal  : 'z;
  assign wlast  = (if_mode == Host)   ? wlast_internal  : 'z;
  assign wuser  = (if_mode == Host)   ? wuser_internal  : 'z;

  // Set the DATA_WIDTH property. The allowed values are 8, 16, 32, 64, 128, 256, 512, 1024 (see
  // AMBA AXI protocol specification, issue J, section B1.3)
  function void set_data_width(int unsigned width);
    if (! (width inside {8, 16, 32, 64, 128, 256, 512, 1024})) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set DATA_WIDTH to %0d: must be a value 2^k between 8 and 1024.",
                           width))
      width = 1024;
    end
    if (width < user_data_width * 2) begin
      `uvm_error($sformatf("%m"),
                 $sformatf({"Cannot set DATA_WIDTH to %0d when USER_DATA_WIDTH is %0d: ",
                            "DATA_WIDTH must be at least 2*USER_DATA_WIDTH."},
                            width, user_data_width))
      width = 1024;
    end

    data_width = width;
  endfunction

  // Set the USER_DATA_WIDTH property. The allowed range depends on DATA_WIDTH and is
  // 0..DATA_WIDTH/2 (see AMBA AXI protocol specification, issue J, section B1.3)
  function void set_user_data_width(int unsigned width);
    if (width > data_width / 2) begin
      `uvm_error($sformatf("%m"),
                 $sformatf({"Cannot set USER_DATA_WIDTH to %0d when DATA_WIDTH is %0d: ",
                            "USER_DATA_WIDTH must be in the range 0..DATA_WIDTH/2."},
                            width, data_width))
      width = data_width / 2;
    end

    user_data_width = width;
  endfunction

endinterface
