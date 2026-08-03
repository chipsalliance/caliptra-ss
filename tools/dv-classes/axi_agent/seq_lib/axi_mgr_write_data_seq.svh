// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a sequence of axi_write_data_item items, representing a single burst.

class axi_mgr_write_data_seq extends uvm_sequence #(axi_write_data_item, axi_status_item);
  `uvm_object_utils(axi_mgr_write_data_seq)

  // The number of items to send in the burst. This should be constrained by the virtual sequence
  // that creates this sequence to match the m_len value that the virtual sequence is sending on AW.
  rand int unsigned m_number_of_items;

  extern function new(string name="");
  extern task body();

  // Randomize an item that is about to be sent. Defining this explicitly allows a sequence
  // extending this one to more easily constrain the randomisation of the items that get sent.
  //
  // The is_last argument is set when this is the last item in the stream of data words.
  extern protected virtual function void randomize_item(axi_write_data_item item, bit is_last);

  // The number of items needs to match m_len from the AW channel, which is represented by an 8-bit
  // value that gives the last index. As such, m_number_of_items should be in the range 1..256.
  extern constraint number_of_items_c;
endclass

function axi_mgr_write_data_seq::new(string name="");
  super.new(name);
endfunction

task axi_mgr_write_data_seq::body();
  for (int unsigned i = 0; i < m_number_of_items; i++) begin
    uvm_sequence_item base_status_item;
    axi_write_data_item item = axi_write_data_item::type_id::create("item");

    start_item(item);
    randomize_item(item, i + 1 == m_number_of_items);
    finish_item(item);

    // Get the response from the driver and check it is actually of the expected axi_status_item
    // type.
    get_base_response(base_status_item);
    if (!$cast(rsp, base_status_item)) begin
      `uvm_fatal(get_full_name(), "Status response is not an axi_status_item")
    end

    // If the driver didn't finish sending the item, there has been a reset and we should stop
    // immediately. The virtual sequence can see that we saw the reset because it will see
    // m_sending_complete false in the rsp field.
    if (!rsp.m_sending_complete) break;
  end
endtask

function void axi_mgr_write_data_seq::randomize_item(axi_write_data_item item, bit is_last);
  if (!item.randomize() with {
        m_last == local::is_last;
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise item.")
  end
endfunction

constraint axi_mgr_write_data_seq::number_of_items_c {
  1 <= m_number_of_items;
  m_number_of_items <= 256;
}
