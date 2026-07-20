// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item representing a change of reset state on an interface

class axi_reset_item extends uvm_sequence_item;
  `uvm_object_utils(axi_reset_item)

  // True if the interface is in reset after the change of state
  bit m_in_reset;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function axi_reset_item::new(string name = "");
  super.new(name);
endfunction

function void axi_reset_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_in_reset", m_in_reset, 1, UVM_BIN);
endfunction

function void axi_reset_item::do_copy(uvm_object rhs);
  axi_reset_item rhs_;

  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);

  m_in_reset = rhs_.m_in_reset;
endfunction

function bit axi_reset_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_reset_item rhs_;

  // These items are only equivalent if rhs is actually an axi_reset_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_reset_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_in_reset", m_in_reset, rhs_.m_in_reset, 1, UVM_BIN));
endfunction
