// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base class for routing responses from AXI Subordinates to Managers. These are routed based on
// RID / BID.

class axi_response_router extends uvm_component;
  `uvm_component_utils(axi_response_router)

  typedef uvm_sequence_item item_queue_t[$];

  // An associative array that maps ID to a queue of response items that have been seen for that ID
  // (the FIFO works by pop_front and push_back).
  //
  // We never store an empty list as a value in this associative array, so can wait for a response
  // on a given ID by just waiting for the ID to have some value.
  local item_queue_t m_id_to_responses[int unsigned];

  // A flag that is set by assert_reset and cleared by clear_reset. When this is set,
  // m_id_to_responses will be empty and all calls to wait_for_response will return immediately.
  local bit m_in_reset;

  // An event that triggers all waiting tasks. This runs when a new response is added to
  // m_id_to_responses or when a reset is asserted.
  local uvm_event m_update_event;

  // An import for reset events (asserting or clearing reset)
  uvm_analysis_imp #(axi_reset_item, axi_response_router) reset_imp;

  extern function new (string name, uvm_component parent);

  // The write function for reset_imp, which is called when a reset event is broadcast
  extern virtual function void write(axi_reset_item item);

  // Wait for a response to be seen with the given ID.
  //
  // This returns when such a response is seen, setting rsp. If there is a reset, this task will
  // return, setting rsp = null.
  extern task wait_for_response(int unsigned id, output uvm_sequence_item rsp);

  // Notify the router that there has been the given response, for the supplied id.
  extern function void on_response(int unsigned id, uvm_sequence_item rsp);
endclass

function axi_response_router::new(string name, uvm_component parent);
  super.new(name, parent);
  m_update_event = new("m_update_event");
  reset_imp = new("reset_imp", this);
endfunction

function void axi_response_router::write(axi_reset_item item);
  if (item.m_in_reset) begin
    // Reset is being asserted. If we don't know about it already, set a flag, clear
    // m_id_to_responses and trigger the event to cause all tasks waiting to finish.
    if (!m_in_reset) begin
      m_in_reset = 1'b1;
      m_id_to_responses.delete();
      m_update_event.trigger();
    end
  end else begin
    // Reset is being cleared. All we have to do is clear m_in_reset.
    m_in_reset = 1'b0;
  end
endfunction

task axi_response_router::wait_for_response(int unsigned             id,
                                            output uvm_sequence_item rsp);
  while (!m_id_to_responses.exists(id) && !m_in_reset) m_update_event.wait_trigger();

  if (m_in_reset) begin
    rsp = null;
  end else begin
    // The logic just below should ensure that m_id_to_responses[id] is never an empty queue, but it
    // probably makes sense to add an extra check here for debugging.
    if (m_id_to_responses[id].size() == 0) begin
      `uvm_fatal(get_full_name(),
                 $sformatf("m_id_to_responses[0x%0h] is an empty queue.", id))
    end

    rsp = m_id_to_responses[id].pop_front;

    if (m_id_to_responses[id].size() == 0) begin
      m_id_to_responses.delete(id);
    end
  end
endtask

function void axi_response_router::on_response(int unsigned id, uvm_sequence_item rsp);
  if (rsp == null) `uvm_fatal(get_full_name(), "rsp must not be null.")

  if (!m_in_reset) begin
    if (!m_id_to_responses.exists(id)) begin
      m_id_to_responses[id] = '{};
    end
    m_id_to_responses[id].push_back(rsp);
    m_update_event.trigger();
  end
endfunction
