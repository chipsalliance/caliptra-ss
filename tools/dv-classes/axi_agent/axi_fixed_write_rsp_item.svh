// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents a response to an AXI write with a single beat
//
// The fields are null when the instance is created, and should be filled with results of the three
// sequences (which may be null if the sequences were interrupted by a reset).

class axi_fixed_write_rsp_item extends uvm_sequence_item;
  `uvm_object_utils(axi_fixed_write_rsp_item)
  // The status of the write request transfer (which either completed or was interrupted by reset)
  axi_status_item         m_aw_status;

  // The status of the write data transfer (which either completed or was interrupted by reset)
  axi_status_item         m_w_status;

  // The write response seen (on the B channel)
  axi_write_response_item m_write_response;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function axi_fixed_write_rsp_item::new(string name = "");
  super.new(name);
endfunction

function void axi_fixed_write_rsp_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_object("m_aw_status", m_aw_status);
  printer.print_object("m_w_status", m_w_status);
  printer.print_object("m_write_response", m_write_response);
endfunction

function void axi_fixed_write_rsp_item::do_copy(uvm_object rhs);
  axi_fixed_write_rsp_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  if (rhs_.m_aw_status == null) m_aw_status = null;
  else if (!$cast(m_aw_status, rhs_.m_aw_status.clone())) begin
    `uvm_fatal("do_copy", "Failed to clone m_aw_status.")
  end

  if (rhs_.m_w_status == null) m_w_status = null;
  else if (!$cast(m_w_status, rhs_.m_w_status.clone())) begin
    `uvm_fatal("do_copy", "Failed to clone m_w_status.")
  end

  if (rhs_.m_write_response == null) m_write_response = null;
  if (!$cast(m_write_response, rhs_.m_write_response.clone())) begin
    `uvm_fatal("do_copy", "Failed to clone m_write_response.")
  end
endfunction

function bit axi_fixed_write_rsp_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  bit all_match = 1;
  axi_fixed_write_rsp_item rhs_;

  // These items are only equivalent if rhs is actually an axi_fixed_write_rsp_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_fixed_write_rsp_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_object("m_aw_status", m_aw_status, rhs_.m_aw_status) &
          comparer.compare_object("m_w_status", m_w_status, rhs_.m_w_status) &
          comparer.compare_object("m_write_response", m_write_response, rhs_.m_write_response));
endfunction
