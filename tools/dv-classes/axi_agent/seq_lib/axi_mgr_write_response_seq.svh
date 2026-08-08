// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a single axi_response_accept_item. The response to that item will be stored
// in the rsp class variable, which will be null if the sequence saw a reset before a response.

class axi_mgr_write_response_seq extends uvm_sequence #(axi_response_accept_item,
                                                        axi_write_response_item);
  `uvm_object_utils(axi_mgr_write_response_seq)

  // This sequence uses late randomisation, so doesn't randomise the request until it is scheduled
  // on the sequencer. Of course, this is a bit tricky to use in a situation where you want to
  // control a particular variable when randomising. To do so for a field called XYZ, set
  // m_use_fixed_XYZ=1 and set m_fixed_XYZ to the required value. Do this before starting the
  // sequence and m_XYZ in the generated item will be "randomised" to match m_fixed_XYZ.
  //
  // The pairs of variables below are named to match the fields of axi_response_accept_item.

  bit          m_use_fixed_ready_without_valid_pct;
  int unsigned m_fixed_ready_without_valid_pct;

  bit          m_use_fixed_valid_to_ready_delay;
  int unsigned m_fixed_valid_to_ready_delay;

  extern function new(string name="");
  extern task body();
endclass

function axi_mgr_write_response_seq::new(string name="");
  super.new(name);
endfunction

task axi_mgr_write_response_seq::body();
  axi_response_accept_item item = axi_response_accept_item::type_id::create("item");
  uvm_sequence_item base_response_item;

  start_item(item);

  if (!item.randomize() with {
        local::m_use_fixed_ready_without_valid_pct ->
          m_ready_without_valid_pct == local::m_fixed_ready_without_valid_pct;

        local::m_use_fixed_valid_to_ready_delay ->
          m_valid_to_ready_delay == local::m_fixed_valid_to_ready_delay;
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise item.")
  end

  finish_item(item);

  // Get a response from the driver, which will either be an axi_write_response_item (meaning that
  // we have seen a response on the interface) or an axi_status_item with m_sending_complete == 0
  // (meaning that we saw a reset).
  //
  // If there is a response, set rsp to match. If not, leave rsp == null.
  get_base_response(base_response_item);

  if ($cast(rsp, base_response_item)) begin
    // The response was an axi_write_response_item and we have now set the sequence response to
    // match: we're done and can just return.
  end else begin
    axi_status_item status_item;
    if (!$cast(status_item, base_response_item)) begin
      `uvm_fatal(get_full_name(),
                 {"Driver responded with an item that is ",
                  "neither an axi_write_response_item nor an axi_status_item."})
    end

    // If the cast succeeded, check that the driver did indeed leave m_sending_complete=0, then do
    // nothing more: we can just leave rsp null.
    if (status_item.m_sending_complete) begin
      `uvm_fatal(get_full_name(), "Driver responded with a complete status. (?!)")
    end
  end
endtask
