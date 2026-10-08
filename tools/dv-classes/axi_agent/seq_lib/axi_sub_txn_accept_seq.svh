// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate sequence that accepts a single AW or AR request item and stores it in rsp.

class axi_sub_txn_accept_seq extends uvm_sequence #(axi_response_accept_item, axi_txn_request_item);
  `uvm_object_utils(axi_sub_txn_accept_seq)

  bit          m_use_fixed_ready_without_valid_pct;
  int unsigned m_fixed_ready_without_valid_pct;

  bit          m_use_fixed_valid_to_ready_delay;
  int unsigned m_fixed_valid_to_ready_delay;

  function new(string name="");
    super.new(name);
  endfunction

  task body();
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

    get_base_response(base_response_item);
    if (!$cast(rsp, base_response_item)) begin
      axi_status_item status_item;
      if (!$cast(status_item, base_response_item) || status_item.m_sending_complete) begin
        `uvm_fatal(get_full_name(), "Unexpected response item from subordinate request driver.")
      end
    end
  endtask
endclass
