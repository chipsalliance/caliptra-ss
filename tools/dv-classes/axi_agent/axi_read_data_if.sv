// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AXI read data channel

interface axi_read_data_if (input clk_i, input rst_ni);
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Device, dv_utils_pkg::Monitor;

  // The interface mode.
  //
  //  - Host:    An agent is driving the interface signals through mgr_cb, acting as a Manager.
  //  - Device:  An agent is driving the interface signals through sub_cb, acting as a Subordinate.
  //  - Monitor: No agent is driving interface signals and the interface is purely passive.
  if_mode_e if_mode = Monitor;

  // The ID_R_WIDTH property. Set this by calling set_id_r_width().
  int unsigned id_r_width = 32;

  // The DATA_WIDTH property. Set this by calling set_data_width().
  int unsigned data_width = 1024;

  // The USER_DATA_WIDTH property. Set this by calling set_user_data_width().
  int unsigned user_data_width = 512;

  // The RRESP_WIDTH property. Set this by calling set_rresp_width().
  int unsigned rresp_width = 3;

  // The USER_RESP_WIDTH property. Set this by calling set_user_resp_width().
  int unsigned user_resp_width = 16;

  // The core defined signals for the read data channel.
  //
  // This interface uses a max footprint approach. Signals of configurable width (like rid) might
  // only use the lower bits.
  //
  // Not all possible read data channel signals are included. Not included are:
  //
  //    - RPOISON (Poison is false)
  //    - RTRACE  (Trace_Signals is false)
  //    - RLOOP   (Loopback_Signals is false)
  //    - RBUSY   (Busy_Support is false)
  //    - RIDUNQ  (Unique_ID_Support is false)
  //    - RCHUNK* (Read_Data_Chunking is false)
  //    - RTAG    (MTE_Support is false)
  wire          rvalid;
  wire          rready;
  wire [31:0]   rid;
  wire [1023:0] rdata;
  wire [2:0]    rresp;
  wire          rlast;
  wire [527:0]  ruser;

  // A copy of rready, which is driven by mgr_cb (only used if if_mode == Host). The rready_driven
  // signal is directly driven by the clocking block. The rready_internal signal tracks it, but is
  // also cleared on reset.
  logic         rready_driven, rready_internal;

  // Copies of the signals that are driven by sub_cb (only used if if_mode == Device). The
  // "*_driven" signals are directly driven by the clocking block. The "*_internal" signals track
  // these, but take masks into account for signals with configurable length and are also cleared on
  // reset.
  logic          rvalid_driven, rvalid_internal;
  logic [31:0]   rid_driven, rid_internal;
  logic [1023:0] rdata_driven, rdata_internal;
  logic [2:0]    rresp_driven, rresp_internal;
  logic          rlast_driven, rlast_internal;
  logic [527:0]  ruser_driven, ruser_internal;

  // Masks used when converting some *_driven signals to *_internal
  logic [31:0]   rid_mask;
  logic [1023:0] rdata_mask;
  logic [2:0]    rresp_mask;
  logic [527:0]  ruser_mask;

  assign rid_mask   = (32'b1 << id_r_width) - 1;
  assign rdata_mask = (1024'b1 << data_width) - 1;
  assign rresp_mask = (3'b1 << rresp_width) - 1;
  assign ruser_mask = (528'b1 << (user_data_width + user_resp_width)) - 1;

  clocking mon_cb @(posedge clk_i);
    input rvalid;
    input rready;
    input rid;
    input rdata;
    input rresp;
    input rlast;
    input ruser;
  endclocking

  clocking mgr_cb @(posedge clk_i);
    input  rvalid;
    output rready = rready_driven;
    input  rid;
    input  rdata;
    input  rresp;
    input  rlast;
    input  ruser;
  endclocking

  clocking sub_cb @(posedge clk_i);
    output rvalid = rvalid_driven;
    input  rready;
    output rid    = rid_driven;
    output rdata  = rdata_driven;
    output rresp  = rresp_driven;
    output rlast  = rlast_driven;
    output ruser  = ruser_driven;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      rvalid_internal = '0;
      rready_internal = '0;
      rid_internal    = '0;
      rdata_internal  = '0;
      rresp_internal  = '0;
      rlast_internal  = '0;
      ruser_internal  = '0;
    end else begin
      rvalid_internal = rvalid_driven;
      rready_internal = rready_driven;
      rid_internal    = rid_driven & rid_mask;
      rdata_internal  = rdata_driven & rdata_mask;
      rresp_internal  = rresp_driven & rresp_mask;
      rlast_internal  = rlast_driven;
      ruser_internal  = ruser_driven & ruser_mask;
    end
  end

  assign rvalid = (if_mode == Device) ? rvalid_internal : 'z;
  assign rready = (if_mode == Host)   ? rready_internal : 'z;
  assign rid    = (if_mode == Device) ? rid_internal    : 'z;
  assign rdata  = (if_mode == Device) ? rdata_internal  : 'z;
  assign rresp  = (if_mode == Device) ? rresp_internal  : 'z;
  assign rlast  = (if_mode == Device) ? rlast_internal  : 'z;
  assign ruser  = (if_mode == Device) ? ruser_internal  : 'z;

  // Set the ID_R_WIDTH property. The allowed range is 0..32 (see AMBA AXI protocol specification,
  // issue J, section B1.3)
  function void set_id_r_width(int unsigned width);
    if (width > 32) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set ID_R_WIDTH to %0d: maximum in spec is 32.", width))
      width = 32;
    end

    id_r_width = width;
  endfunction

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

  // Set the RRESP_WIDTH property. The allowed values are 0, 2, 3 (see AMBA AXI protocol
  // specification, issue J, section B1.3)
  function void set_rresp_width(int unsigned width);
    if (! (width inside {0, 2, 3})) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set RRESP_WIDTH to %0d: must be 0, 2 or 3.", width))
      width = 3;
    end

    rresp_width = width;
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
