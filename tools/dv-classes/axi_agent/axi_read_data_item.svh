// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents the data sent by an AXI Subordinate to respond to a read

class axi_read_data_item extends uvm_sequence_item;
  `uvm_object_utils(axi_read_data_item)

  // The possible encoded values of the RRESP signal
  typedef enum bit [2:0] {
    RRespOkay       = 0,
    RRespExOkay     = 1,
    RRespSlverr     = 2,
    RRespDecErr     = 3,
    RRespPrefetched = 4,
    RRespTransfault = 5,
    RRespOkayDirty  = 6
  } rresp_e;

  // Transaction identifier for the read channel
  //
  // This is sent over the RID signal, whose width is configurable, based on the ID_R_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bit [31:0]   m_id;

  // Read data
  //
  // This is sent over the RDATA signal, whose width is configurable, based on the DATA_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bit [1023:0] m_data;

  // Read response
  //
  // This is sent over the RRESP signal, whose width is configurable, based on the RRESP_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand rresp_e      m_resp;

  // Asserted on the last transfer in a burst
  rand bit          m_last;

  // Extra user-defined bits that extend m_data and m_resp. This is sent over the RUSER signal,
  // whose width is configurable, based on the USER_DATA_WIDTH and USER_RESP_WIDTH properties. The
  // representation in the item uses a max footprint approach but the driver will fail with an error
  // if bits above the top of the signal are nonzero.
  rand bit [527:0]  m_user;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function axi_read_data_item::new(string name = "");
  super.new(name);
endfunction

function void axi_read_data_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_id", m_id, 32, UVM_HEX);
  printer.print_field("m_data", m_data, 1024, UVM_HEX);
  printer.print_string("m_resp", m_resp.name());
  printer.print_field_int("m_last", m_last, 1, UVM_BIN);
  printer.print_field("m_user", m_user, 528, UVM_HEX);
endfunction

function void axi_read_data_item::do_copy(uvm_object rhs);
  axi_read_data_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_id   = rhs_.m_id;
  this.m_data = rhs_.m_data;
  this.m_resp = rhs_.m_resp;
  this.m_last = rhs_.m_last;
  this.m_user = rhs_.m_user;
endfunction

function bit axi_read_data_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_read_data_item rhs_;

  // These items are only equivalent if rhs is actually an axi_read_data_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_read_data_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_id", m_id, rhs_.m_id, 32, UVM_HEX) &
          comparer.compare_field("m_data", m_data, rhs_.m_data, 1024, UVM_HEX) &
          comparer.compare_field_int("m_resp", m_resp, rhs_.m_resp, 3, UVM_HEX) &
          comparer.compare_field_int("m_last", m_last, rhs_.m_last, 1, UVM_BIN) &
          comparer.compare_field("m_user", m_user, rhs_.m_user, 528, UVM_HEX));
endfunction
