// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A subclass of axi_mgr_write_data_seq that sends a single sequence item
//
// This can be used for a write where LEN is zero.

class axi_mgr_write_single_data_seq extends axi_mgr_write_data_seq;
  `uvm_object_utils(axi_mgr_write_single_data_seq)

  // The data to be written
  rand axi_write_data_item m_write_data_item;

  extern function new(string name="");

  // An override of axi_mgr_write_data_seq::randomize_item, ensuring that the item that is sent
  // matches m_write_data_item.
  extern protected function void randomize_item(axi_write_data_item item, bit is_last);

  // Write exactly one item
  extern constraint single_item_c;
endclass

function axi_mgr_write_single_data_seq::new(string name="");
  super.new(name);
  m_write_data_item = axi_write_data_item::type_id::create("m_write_data_item");
endfunction

function void axi_mgr_write_single_data_seq::randomize_item(axi_write_data_item item, bit is_last);
  // This completely replaces the base class function, and the "randomisation" is done by copying
  // from m_write_data_item.
  item.copy(m_write_data_item);
endfunction

constraint axi_mgr_write_single_data_seq::single_item_c {
  m_number_of_items == 1;
}
