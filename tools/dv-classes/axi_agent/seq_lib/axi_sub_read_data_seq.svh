// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate sequence that sends a single R channel read data beat.

class axi_sub_read_data_seq extends uvm_sequence #(axi_read_data_item, axi_status_item);
  `uvm_object_utils(axi_sub_read_data_seq)

  rand axi_read_data_item m_read_data_item;

  function new(string name="");
    super.new(name);
    m_read_data_item = axi_read_data_item::type_id::create("m_read_data_item");
  endfunction

  task body();
    axi_read_data_item item = axi_read_data_item::type_id::create("item");
    uvm_sequence_item base_status_item;

    start_item(item);
    item.copy(m_read_data_item);
    finish_item(item);

    get_base_response(base_status_item);
    if (!$cast(rsp, base_status_item)) begin
      `uvm_fatal(get_full_name(), "Status response is not an axi_status_item")
    end
  endtask
endclass
