// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AXI write request channel

interface axi_write_request_if (input clk_i, input rst_ni);
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

  // The ADDR_WIDTH property. Set this by calling set_addr_width().
  int unsigned addr_width = 64;

  // The USER_REQ_WIDTH property. Set this by calling set_user_req_width().
  int unsigned user_req_width = 128;

  // The core defined signals for the write request channel.
  //
  // This interface uses a max footprint approach. Signals of configurable width (like awid) might
  // only use the lower bits.
  //
  // Not all possible write request channel signals are included. Not included are:
  //
  //    - AWDOMAIN      (Shareable_Transactions is false)
  //    - AWSNOOP       (AWSNOOP_WIDTH is zero)
  //    - AWSTASHNID    (Cache_Stash_Transactions is false)
  //    - AWSTASHNIDLEN (Cache_Stash_Transactions is false)
  //    - AWSTASHLPID   (Cache_Stash_Transactions is false)
  //    - AWSTASHLPIDEN (Cache_Stash_Transactions is false)
  //    - AWTRACE       (Trace_Signals is false)
  //    - AWLOOP        (Loopback_Signals is false)
  //    - AWMMU*        (Untranslated_Transactions is false)
  //    - AWPBHA        (Untranslated_Transactions is false)
  //    - AWNSAID       (NSAccess_Identifiers is false)
  //    - AWSUBSYSID    (SUBSYSID_WIDTH is zero)
  //    - AWATOP        (Atomic_Transactions is false)
  //    - AWMPAM        (MPAM_Support is false)
  //    - AWIDUNQ       (Unique_ID_Support is false)
  //    - AWCMO         (AWCMO_WIDTH is zero)
  //    - AWTAGOP       (MTE_Support is false)
  wire         awvalid;
  wire         awready;
  wire [31:0]  awid;
  wire [63:0]  awaddr;
  wire [3:0]   awregion;
  wire [7:0]   awlen;
  wire [2:0]   awsize;
  wire [1:0]   awburst;
  wire         awlock;
  wire [3:0]   awcache;
  wire [2:0]   awprot;
  wire [3:0]   awqos;
  wire [127:0] awuser;

  // Copies of the signals that are driven by mgr_cb (only used if if_mode == Host). The "*_driven"
  // signals are directly driven by the clocking block. The "*_internal" signals track these, but
  // take masks into account for signals with configurable length and are also cleared on reset.
  logic         awvalid_driven, awvalid_internal;
  logic [31:0]  awid_driven, awid_internal;
  logic [63:0]  awaddr_driven, awaddr_internal;
  logic [3:0]   awregion_driven, awregion_internal;
  logic [7:0]   awlen_driven, awlen_internal;
  logic [2:0]   awsize_driven, awsize_internal;
  logic [1:0]   awburst_driven, awburst_internal;
  logic         awlock_driven, awlock_internal;
  logic [3:0]   awcache_driven, awcache_internal;
  logic [2:0]   awprot_driven, awprot_internal;
  logic [3:0]   awqos_driven, awqos_internal;
  logic [127:0] awuser_driven, awuser_internal;

  // A copy of awready, which is driven by sub_cb (only used if if_mode == Device). The
  // awready_driven signal is directly driven by the clocking block. The awready_internal signal
  // tracks it, but is also cleared on reset.
  logic         awready_driven, awready_internal;

  // Masks used when converting some *_driven signals to *_internal
  logic [31:0]  awid_mask;
  logic [63:0]  awaddr_mask;
  logic [127:0] awuser_mask;

  assign awid_mask   = (32'b1 << id_w_width) - 1;
  assign awaddr_mask = (64'b1 << addr_width) - 1;
  assign awuser_mask = (128'b1 << user_req_width) - 1;

  clocking mon_cb @(posedge clk_i);
    input awvalid;
    input awready;
    input awid;
    input awaddr;
    input awregion;
    input awlen;
    input awsize;
    input awburst;
    input awlock;
    input awcache;
    input awprot;
    input awqos;
    input awuser;
  endclocking

  clocking mgr_cb @(posedge clk_i);
    output awvalid  = awvalid_driven;
    input  awready;
    output awid     = awid_driven;
    output awaddr   = awaddr_driven;
    output awregion = awregion_driven;
    output awlen    = awlen_driven;
    output awsize   = awsize_driven;
    output awburst  = awburst_driven;
    output awlock   = awlock_driven;
    output awcache  = awcache_driven;
    output awprot   = awprot_driven;
    output awqos    = awqos_driven;
    output awuser   = awuser_driven;
  endclocking

  clocking sub_cb @(posedge clk_i);
    input  awvalid;
    output awready = awready_driven;
    input  awid;
    input  awaddr;
    input  awregion;
    input  awlen;
    input  awsize;
    input  awburst;
    input  awlock;
    input  awcache;
    input  awprot;
    input  awqos;
    input  awuser;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      awvalid_internal  = '0;
      awready_internal  = '0;
      awid_internal     = '0;
      awaddr_internal   = '0;
      awregion_internal = '0;
      awlen_internal    = '0;
      awsize_internal   = '0;
      awburst_internal  = '0;
      awlock_internal   = '0;
      awcache_internal  = '0;
      awprot_internal   = '0;
      awqos_internal    = '0;
      awuser_internal   = '0;
    end else begin
      awvalid_internal  = awvalid_driven;
      awready_internal  = awready_driven;
      awid_internal     = awid_driven & awid_mask;
      awaddr_internal   = awaddr_driven & awaddr_mask;
      awregion_internal = awregion_driven;
      awlen_internal    = awlen_driven;
      awsize_internal   = awsize_driven;
      awburst_internal  = awburst_driven;
      awlock_internal   = awlock_driven;
      awcache_internal  = awcache_driven;
      awprot_internal   = awprot_driven;
      awqos_internal    = awqos_driven;
      awuser_internal   = awuser_driven & awuser_mask;
    end
  end

  assign awvalid  = (if_mode == Host)   ? awvalid_internal  : 'z;
  assign awready  = (if_mode == Device) ? awready_internal  : 'z;
  assign awid     = (if_mode == Host)   ? awid_internal     : 'z;
  assign awaddr   = (if_mode == Host)   ? awaddr_internal   : 'z;
  assign awregion = (if_mode == Host)   ? awregion_internal : 'z;
  assign awlen    = (if_mode == Host)   ? awlen_internal    : 'z;
  assign awsize   = (if_mode == Host)   ? awsize_internal   : 'z;
  assign awburst  = (if_mode == Host)   ? awburst_internal  : 'z;
  assign awlock   = (if_mode == Host)   ? awlock_internal   : 'z;
  assign awcache  = (if_mode == Host)   ? awcache_internal  : 'z;
  assign awprot   = (if_mode == Host)   ? awprot_internal   : 'z;
  assign awqos    = (if_mode == Host)   ? awqos_internal    : 'z;
  assign awuser   = (if_mode == Host)   ? awuser_internal   : 'z;

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

  // Set the ADDR_WIDTH property. The allowed range is 1..64 (see AMBA AXI protocol specification,
  // issue J, section B1.3)
  function void set_addr_width(int unsigned width);
    if (width < 1 || width > 64) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set ADDR_WIDTH to %0d: range in spec is 1..64.", width))
      width = 64;
    end

    addr_width = width;
  endfunction

  // Set the USER_REQ_WIDTH property. The allowed range is 0..128 (see AMBA AXI protocol
  // specification, issue J, section B1.3)
  function void set_user_req_width(int unsigned width);
    if (width > 128) begin
      `uvm_error($sformatf("%m"),
                 $sformatf("Cannot set USER_REQ_WIDTH to %0d: maximum in spec is 128.", width))
      width = 128;
    end

    user_req_width = width;
  endfunction
endinterface
