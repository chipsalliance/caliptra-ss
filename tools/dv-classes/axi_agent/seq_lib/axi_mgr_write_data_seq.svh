// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a sequence of axi_write_data_item items, representing a single burst.

class axi_mgr_write_data_seq extends uvm_sequence #(axi_write_data_item, axi_status_item);
  `uvm_object_utils(axi_mgr_write_data_seq)

  // The number of items to send in the burst. This should be constrained by the virtual sequence
  // that creates this sequence to match the m_len value that the virtual sequence is sending on AW.
  rand int unsigned m_number_of_items;

  // Configurable interface widths and optional strobe overrides so randomized W beats stay within
  // the active bus width across both set_widths() callers and direct field-override callers.
  int unsigned m_data_width      = 1024;
  int unsigned m_user_data_width = 512;
  bit          m_widths_set      = 1'b0;
  bit          m_use_fixed_strb  = 1'b0;
  bit [127:0]  m_fixed_strb      = '0;

  extern function new(string name="");
  extern function void set_widths(int unsigned data_width, int unsigned user_data_width);
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

function void axi_mgr_write_data_seq::set_widths(int unsigned data_width,
                                                 int unsigned user_data_width);
  m_data_width      = data_width;
  m_user_data_width = user_data_width;
  m_widths_set      = 1'b1;
endfunction

task axi_mgr_write_data_seq::body();
  if (!m_widths_set && m_data_width == 1024 && m_user_data_width == 512) begin
    virtual axi_write_data_if wd_vif;
    if (uvm_config_db#(virtual axi_write_data_if)::get(m_sequencer, "", "vif", wd_vif) ||
        uvm_config_db#(virtual axi_write_data_if)::get(null, "*", "write_data_vif", wd_vif) ||
        uvm_config_db#(virtual axi_write_data_if)::get(null, "*", "w_vif", wd_vif)) begin
      m_data_width      = wd_vif.data_width;
      m_user_data_width = wd_vif.user_data_width;
    end
  end

  // Serialize W-channel beats per sequencer via a process-safe mutex (automatically reclaimed on
  // `disable fork` / `stop_sequences()` without deadlocking `try_next_item()`).
  axi_seq_lock_mgr::acquire_w_burst(m_sequencer);

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

  axi_seq_lock_mgr::release_w_burst(m_sequencer);
endtask

function void axi_mgr_write_data_seq::randomize_item(axi_write_data_item item, bit is_last);
  int unsigned strb_width = (m_data_width + 7) / 8;
  if (!item.randomize() with {
        m_last == local::is_last;
        if (local::m_data_width < 1024)     { (m_data >> local::m_data_width) == '0; }
        if (strb_width < 128)               { (m_strb >> strb_width) == '0; }
        if (local::m_user_data_width < 512) { (m_user >> local::m_user_data_width) == '0; }
        if (local::m_use_fixed_strb)        { m_strb == local::m_fixed_strb; }
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise item.")
  end
endfunction

constraint axi_mgr_write_data_seq::number_of_items_c {
  1 <= m_number_of_items;
  m_number_of_items <= 256;
}
