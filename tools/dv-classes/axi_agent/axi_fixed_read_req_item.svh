// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents the request that should be made to send a single AXI read with
// AWBURST set to FIXED and AWLEN = 0 (so just a single data transfer).

class axi_fixed_read_req_item extends uvm_sequence_item;
  `uvm_object_utils(axi_fixed_read_req_item)
  // Transaction identifier for the read channel
  //
  // This is sent as AWID, whose width is configurable (and will be checked against the
  // corresponding width in the interface by the driver).
  rand bit [31:0]                  m_id;

  // The address.
  //
  // This is AWADDR, whose width is configurable (and will be checked against the
  // corresponding width in the interface by the driver).
  rand bit [63:0]                  m_addr;

  // The region identifier, sent as AWREGION in the request transfer.
  rand bit [3:0]                   m_region;

  // Number of bytes in the data transfer. Sent as AWSIZE and encoded as log2(byte_size).
  rand bit [2:0]                   m_size;

  // Request exclusive access? Sent as AWLOCK.
  rand bit                         m_lock;

  // Memory attributes (applying to caches in the system). Sent as AWCACHE.
  rand bit [3:0]                   m_cache;

  // Memory access attributes. Sent as AWPROT.
  rand bit [2:0]                   m_prot;

  // Traffic stream QoS identifier. Sent as AWQOS.
  rand bit [3:0]                   m_qos;

  // Extra user bits.
  //
  // This is sent as AWUSER, whose width is configurable (and will be checked against the
  // corresponding width in the interface by the driver).
  rand bit [127:0]                 m_user;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function axi_fixed_read_req_item::new(string name = "");
  super.new(name);
endfunction

function void axi_fixed_read_req_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_id", m_id, 32, UVM_HEX);
  printer.print_field("m_addr", m_addr, 64, UVM_HEX);
  printer.print_field_int("m_region", m_region, 4, UVM_HEX);
  printer.print_field_int("m_size", m_size, 3, UVM_DEC);
  printer.print_field_int("m_lock", m_lock, 1, UVM_BIN);
  printer.print_field_int("m_cache", m_cache, 4, UVM_BIN);
  printer.print_field_int("m_prot", m_prot, 3, UVM_BIN);
  printer.print_field_int("m_qos", m_qos, 4, UVM_HEX);
  printer.print_field("m_user", m_user, 128, UVM_HEX);
endfunction

function void axi_fixed_read_req_item::do_copy(uvm_object rhs);
  axi_fixed_read_req_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_id     = rhs_.m_id;
  this.m_addr   = rhs_.m_addr;
  this.m_region = rhs_.m_region;
  this.m_size   = rhs_.m_size;
  this.m_lock   = rhs_.m_lock;
  this.m_cache  = rhs_.m_cache;
  this.m_prot   = rhs_.m_prot;
  this.m_qos    = rhs_.m_qos;
  this.m_user   = rhs_.m_user;
endfunction

function bit axi_fixed_read_req_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_fixed_read_req_item rhs_;

  // These items are only equivalent if rhs is actually an axi_fixed_read_req_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_fixed_read_req_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_id", m_id, rhs_.m_id, 32, UVM_HEX) &
          comparer.compare_field("m_addr", m_addr, rhs_.m_addr, 64, UVM_HEX) &
          comparer.compare_field_int("m_region", m_region, rhs_.m_region, 4, UVM_HEX) &
          comparer.compare_field_int("m_size", m_size, rhs_.m_size, 3, UVM_DEC) &
          comparer.compare_field_int("m_lock", m_lock, rhs_.m_lock, 1, UVM_BIN) &
          comparer.compare_field_int("m_cache", m_cache, rhs_.m_cache, 4, UVM_BIN) &
          comparer.compare_field_int("m_prot", m_prot, rhs_.m_prot, 3, UVM_BIN) &
          comparer.compare_field_int("m_qos", m_qos, rhs_.m_qos, 4, UVM_HEX) &
          comparer.compare_field("m_user", m_user, rhs_.m_user, 128, UVM_HEX));
endfunction
