// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents the action a driver should take when accepting a response (on the
// B or R channels, for example).

class axi_response_accept_item extends uvm_sequence_item;
  `uvm_object_utils(axi_response_accept_item)

  // Should the driver assert READY some of the time when VALID has not yet been asserted? This
  // field gives the percentage of the time that READY should be asserted. To only assert READY
  // after VALID, set this to zero.
  rand int unsigned m_ready_without_valid_pct;

  // What is the time that the driver should wait after seeing VALID before asserting READY? (This
  // might have no effect if m_ready_without_valid_pct is nonzero and we happen to have asserted
  // READY on the cycle that VALID is asserted).
  rand int unsigned m_valid_to_ready_delay;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Constrain m_ready_without_valid_pct to be a valid percentage
  extern constraint ready_without_valid_c;

  // Constrain m_valid_to_ready_delay to be reasonably short (to avoid wasting time in simulations).
  // This is a soft constraint, so it's easy to override.
  extern constraint valid_to_ready_c;
endclass

function axi_response_accept_item::new(string name = "");
  super.new(name);
endfunction

function void axi_response_accept_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_ready_without_valid_pct", m_ready_without_valid_pct, 32, UVM_DEC);
  printer.print_field_int("m_valid_to_ready_delay", m_valid_to_ready_delay, 32, UVM_DEC);
endfunction

function void axi_response_accept_item::do_copy(uvm_object rhs);
  axi_response_accept_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_ready_without_valid_pct = rhs_.m_ready_without_valid_pct;
  this.m_valid_to_ready_delay = rhs_.m_valid_to_ready_delay;
endfunction

function bit axi_response_accept_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_response_accept_item rhs_;

  // These items are only equivalent if rhs is actually an axi_response_accept_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_response_accept_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_ready_without_valid_pct", m_ready_without_valid_pct,
                                     rhs_.m_ready_without_valid_pct, 32, UVM_DEC) &
          comparer.compare_field_int("m_valid_to_ready_delay", m_valid_to_ready_delay,
                                     rhs_.m_valid_to_ready_delay, 32, UVM_DEC));
endfunction

constraint axi_response_accept_item::ready_without_valid_c {
  m_ready_without_valid_pct <= 100;
}

constraint axi_response_accept_item::valid_to_ready_c {
  soft m_valid_to_ready_delay <= 5;
}
