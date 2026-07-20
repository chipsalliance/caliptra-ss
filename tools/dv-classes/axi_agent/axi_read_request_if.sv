// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface to track an AXI read request channel

interface axi_read_request_if (input clk_i, input rst_ni);
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

  // The ADDR_WIDTH property. Set this by calling set_addr_width().
  int unsigned addr_width = 64;

  // The USER_REQ_WIDTH property. Set this by calling set_user_req_width().
  int unsigned user_req_width = 128;

  // The core defined signals for the read request channel.
  //
  // This interface uses a max footprint approach. Signals of configurable width (like arid) might
  // only use the lower bits.
  //
  // Not all possible read request channel signals are included. Not included are:
  //
  //    - ARNSE      (RME_Support is false)
  //    - ARDOMAIN   (Shareable_Transactions is false)
  //    - ARSNOOP    (ARSNOOP_WIDTH is zero)
  //    - ARTRACE    (Trace_Signals is false)
  //    - ARMMU*     (Untranslated_Transactions is false)
  //    - ARPBHA     (Untranslated_Transactions is false)
  //    - ARNSAID    (NSAccess_Identifiers is false)
  //    - ARSUBSYSID (SUBSYSID_WIDTH is zero)
  //    - ARMPAM     (MPAM_Support is false)
  //    - ARCHUNKEN  (Read_Data_Chunking is false)
  //    - ARIDUNQ    (Unique_ID_Support is false)
  //    - ARTAGOP    (MTE_Support is false)
  wire         arvalid;
  wire         arready;
  wire [31:0]  arid;
  wire [63:0]  araddr;
  wire [3:0]   arregion;
  wire [7:0]   arlen;
  wire [2:0]   arsize;
  wire [1:0]   arburst;
  wire         arlock;
  wire [3:0]   arcache;
  wire [2:0]   arprot;
  wire [3:0]   arqos;
  wire [127:0] aruser;

  // Copies of the signals that are driven by mgr_cb (only used if if_mode == Host). The "*_driven"
  // signals are directly driven by the clocking block. The "*_internal" signals track these, but
  // take masks into account for signals with configurable length and are also cleared on reset.
  logic         arvalid_driven, arvalid_internal;
  logic [31:0]  arid_driven, arid_internal;
  logic [63:0]  araddr_driven, araddr_internal;
  logic [3:0]   arregion_driven, arregion_internal;
  logic [7:0]   arlen_driven, arlen_internal;
  logic [2:0]   arsize_driven, arsize_internal;
  logic [1:0]   arburst_driven, arburst_internal;
  logic         arlock_driven, arlock_internal;
  logic [3:0]   arcache_driven, arcache_internal;
  logic [2:0]   arprot_driven, arprot_internal;
  logic [3:0]   arqos_driven, arqos_internal;
  logic [127:0] aruser_driven, aruser_internal;

  // A copy of arready, which is driven by sub_cb (only used if if_mode == Device). The
  // arready_driven signal is directly driven by the clocking block. The arready_internal signal
  // tracks it, but is cleared on reset.
  logic         arready_driven, arready_internal;

  // Masks used when converting some *_driven signals to *_internal
  logic [31:0]  arid_mask;
  logic [63:0]  araddr_mask;
  logic [127:0] aruser_mask;

  assign arid_mask   = (32'b1 << id_r_width) - 1;
  assign araddr_mask = (64'b1 << addr_width) - 1;
  assign aruser_mask = (128'b1 << user_req_width) - 1;

  clocking mon_cb @(posedge clk_i);
    input arvalid;
    input arready;
    input arid;
    input araddr;
    input arregion;
    input arlen;
    input arsize;
    input arburst;
    input arlock;
    input arcache;
    input arprot;
    input arqos;
    input aruser;
  endclocking

  clocking mgr_cb @(posedge clk_i);
    output arvalid  = arvalid_driven;
    input  arready;
    output arid     = arid_driven;
    output araddr   = araddr_driven;
    output arregion = arregion_driven;
    output arlen    = arlen_driven;
    output arsize   = arsize_driven;
    output arburst  = arburst_driven;
    output arlock   = arlock_driven;
    output arcache  = arcache_driven;
    output arprot   = arprot_driven;
    output arqos    = arqos_driven;
    output aruser   = aruser_driven;
  endclocking

  clocking sub_cb @(posedge clk_i);
    input  arvalid;
    output arready = arready_driven;
    input  arid;
    input  araddr;
    input  arregion;
    input  arlen;
    input  arsize;
    input  arburst;
    input  arlock;
    input  arcache;
    input  arprot;
    input  arqos;
    input  aruser;
  endclocking

  always_comb begin
    if (!rst_ni) begin
      arvalid_internal  = '0;
      arready_internal  = '0;
      arid_internal     = '0;
      araddr_internal   = '0;
      arregion_internal = '0;
      arlen_internal    = '0;
      arsize_internal   = '0;
      arburst_internal  = '0;
      arlock_internal   = '0;
      arcache_internal  = '0;
      arprot_internal   = '0;
      arqos_internal    = '0;
      aruser_internal   = '0;
    end else begin
      arvalid_internal  = arvalid_driven;
      arready_internal  = arready_driven;
      arid_internal     = arid_driven & arid_mask;
      araddr_internal   = araddr_driven & araddr_mask;
      arregion_internal = arregion_driven;
      arlen_internal    = arlen_driven;
      arsize_internal   = arsize_driven;
      arburst_internal  = arburst_driven;
      arlock_internal   = arlock_driven;
      arcache_internal  = arcache_driven;
      arprot_internal   = arprot_driven;
      arqos_internal    = arqos_driven;
      aruser_internal   = aruser_driven & aruser_mask;
    end
  end

  assign arvalid  = (if_mode == Host)   ? arvalid_internal  : 'z;
  assign arready  = (if_mode == Device) ? arready_internal  : 'z;
  assign arid     = (if_mode == Host)   ? arid_internal     : 'z;
  assign araddr   = (if_mode == Host)   ? araddr_internal   : 'z;
  assign arregion = (if_mode == Host)   ? arregion_internal : 'z;
  assign arlen    = (if_mode == Host)   ? arlen_internal    : 'z;
  assign arsize   = (if_mode == Host)   ? arsize_internal   : 'z;
  assign arburst  = (if_mode == Host)   ? arburst_internal  : 'z;
  assign arlock   = (if_mode == Host)   ? arlock_internal   : 'z;
  assign arcache  = (if_mode == Host)   ? arcache_internal  : 'z;
  assign arprot   = (if_mode == Host)   ? arprot_internal   : 'z;
  assign arqos    = (if_mode == Host)   ? arqos_internal    : 'z;
  assign aruser   = (if_mode == Host)   ? aruser_internal   : 'z;

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
