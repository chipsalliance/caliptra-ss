// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a single item (a write request (AW) or read request (AR) transfer)
//
// When it completes, the rsp field will contain a status item that shows whether the sequence ran
// to completion (rather than being interrupted by a reset).

class axi_mgr_txn_request_seq extends uvm_sequence #(axi_txn_request_item, axi_status_item);
  `uvm_object_utils(axi_mgr_txn_request_seq)

  // This sequence uses late randomisation, so doesn't randomise the request until it is scheduled
  // on the sequencer. Of course, this is a bit tricky to use in a situation where you want to
  // control a particular variable when randomising. To do so for a field called XYZ, set
  // m_use_fixed_XYZ=1 and set m_fixed_XYZ to the required value. Do this before starting the
  // sequence and m_XYZ in the generated item will be "randomised" to match m_fixed_XYZ.
  //
  // The pairs of variables below are named to match the fields of axi_txn_request_item.

  bit         m_use_fixed_id;
  bit [31:0]  m_fixed_id;

  bit         m_use_fixed_addr;
  bit [63:0]  m_fixed_addr;

  bit         m_use_fixed_region;
  bit [3:0]   m_fixed_region;

  bit         m_use_fixed_len;
  bit [7:0]   m_fixed_len;

  bit         m_use_fixed_size;
  bit [2:0]   m_fixed_size;

  bit         m_use_fixed_burst;
  burst_e     m_fixed_burst;

  bit         m_use_fixed_lock;
  bit         m_fixed_lock;

  bit         m_use_fixed_cache;
  bit [3:0]   m_fixed_cache;

  bit         m_use_fixed_prot;
  bit [2:0]   m_fixed_prot;

  bit         m_use_fixed_qos;
  bit [3:0]   m_fixed_qos;

  bit         m_use_fixed_user;
  bit [127:0] m_fixed_user;

  extern function new(string name="");
  extern task body();
endclass

function axi_mgr_txn_request_seq::new(string name="");
  super.new(name);
endfunction

task axi_mgr_txn_request_seq::body();
  axi_txn_request_item item = axi_txn_request_item::type_id::create("item");
  uvm_sequence_item base_status_item;

  start_item(item);

  if (!item.randomize() with {
        local::m_use_fixed_id     -> m_id     == local::m_fixed_id;
        local::m_use_fixed_addr   -> m_addr   == local::m_fixed_addr;
        local::m_use_fixed_region -> m_region == local::m_fixed_region;
        local::m_use_fixed_len    -> m_len    == local::m_fixed_len;
        local::m_use_fixed_size   -> m_size   == local::m_fixed_size;
        local::m_use_fixed_burst  -> m_burst  == local::m_fixed_burst;
        local::m_use_fixed_lock   -> m_lock   == local::m_fixed_lock;
        local::m_use_fixed_cache  -> m_cache  == local::m_fixed_cache;
        local::m_use_fixed_prot   -> m_prot   == local::m_fixed_prot;
        local::m_use_fixed_qos    -> m_qos    == local::m_fixed_qos;
        local::m_use_fixed_user   -> m_user   == local::m_fixed_user;
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise item.")
  end

  finish_item(item);

  // Get a response, which will always be sent by the driver (and is available already: there's no
  // pipelining and finish_item just completed).
  get_base_response(base_status_item);
  if (!$cast(rsp, base_status_item)) begin
    `uvm_fatal(get_full_name(), "Status response is not an axi_status_item")
  end
endtask
