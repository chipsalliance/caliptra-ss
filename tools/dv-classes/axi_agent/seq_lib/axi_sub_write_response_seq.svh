// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate sequence that sends a single B channel write response.

class axi_sub_write_response_seq extends uvm_sequence #(axi_write_response_item, axi_status_item);
  `uvm_object_utils(axi_sub_write_response_seq)

  rand axi_write_response_item m_resp_item;

  function new(string name="");
    super.new(name);
    m_resp_item = axi_write_response_item::type_id::create("m_resp_item");
  endfunction

  task body();
    axi_write_response_item item = axi_write_response_item::type_id::create("item");
    uvm_sequence_item base_status_item;

    start_item(item);
    item.copy(m_resp_item);
    finish_item(item);

    get_base_response(base_status_item);
    if (!$cast(rsp, base_status_item)) begin
      `uvm_fatal(get_full_name(), "Status response is not an axi_status_item")
    end
  endtask
endclass
