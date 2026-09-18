// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents the data sent by an AXI Subordinate to respond to a write

class axi_write_response_item extends uvm_sequence_item;
  `uvm_object_utils(axi_write_response_item)

  // The possible encoded values of the BRESP signal
  typedef enum bit [2:0] {
    BRespOkay        = 0,
    BRespExOkay      = 1,
    BRespSlverr      = 2,
    BRespDecErr      = 3,
    BRespDefer       = 4,
    BRespTransfault  = 5,
    // (Note the gap at index 6: there is a reserved value here, unlike RRESP, which has it at 7)
    BRespUnsupported = 7
  } bresp_e;

  // Transaction identifier for the write channels
  //
  // This is sent over the BID signal, whose width is configurable, based on the ID_W_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bit [31:0] m_id;

  // Write response
  //
  // This is sent over the BRESP signal, whose width is configurable, based on the BRESP_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bresp_e    m_resp;

  // Extra user-defined bits that extend m_resp. This is sent over the BUSER signal, whose width is
  // configurable, based on the USER_RESP_WIDTH property. The representation in the item uses a max
  // footprint approach but the driver will fail with an error if bits above the top of the signal
  // are nonzero.
  rand bit [15:0] m_user;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function axi_write_response_item::new(string name = "");
  super.new(name);
endfunction

function void axi_write_response_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_id", m_id, 32, UVM_HEX);
  printer.print_string("m_resp", m_resp.name());
  printer.print_field_int("m_user", m_user, 16, UVM_HEX);
endfunction

function void axi_write_response_item::do_copy(uvm_object rhs);
  axi_write_response_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_id   = rhs_.m_id;
  this.m_resp = rhs_.m_resp;
  this.m_user = rhs_.m_user;
endfunction

function bit axi_write_response_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_write_response_item rhs_;

  // These items are only equivalent if rhs is actually an axi_write_response_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_write_response_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_id", m_id, rhs_.m_id, 32, UVM_HEX) &
          comparer.compare_field_int("m_resp", m_resp, rhs_.m_resp, 3, UVM_BIN) &
          comparer.compare_field_int("m_user", m_user, rhs_.m_user, 16, UVM_HEX));
endfunction
