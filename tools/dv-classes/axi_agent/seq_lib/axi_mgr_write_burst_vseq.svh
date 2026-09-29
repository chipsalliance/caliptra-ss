// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that sends a multi-beat AXI write burst (AWLEN = 0..255, BurstFixed/Incr/Wrap),
// drives (m_len + 1) W channel beats with WLAST on the final beat, and awaits the B response.

class axi_mgr_write_burst_vseq extends uvm_sequence#(uvm_sequence_item, axi_fixed_write_rsp_item);
  `uvm_object_utils(axi_mgr_write_burst_vseq)

  local axi_response_router        m_write_response_router;
  local write_request_sequencer_t  m_write_request_sequencer;
  local write_data_sequencer_t     m_write_data_sequencer;
  local write_response_sequencer_t m_write_response_sequencer;

  rand axi_txn_request_item m_req;

  function new(string name="");
    super.new(name);
    m_req = axi_txn_request_item::type_id::create("m_req");
  endfunction

  function void set_write_response_router(axi_response_router router);
    if (router == null) `uvm_fatal(get_full_name(), "Router is null.")
    m_write_response_router = router;
  endfunction

  function void set_sequencers(write_request_sequencer_t  write_request_sequencer,
                               write_data_sequencer_t     write_data_sequencer,
                               write_response_sequencer_t write_response_sequencer);
    if (write_request_sequencer == null)  `uvm_fatal(get_full_name(), "No write_request_sequencer.")
    if (write_data_sequencer == null)     `uvm_fatal(get_full_name(), "No write_data_sequencer.")
    if (write_response_sequencer == null) `uvm_fatal(get_full_name(), "No write_response_sequencer.")
    m_write_request_sequencer  = write_request_sequencer;
    m_write_data_sequencer     = write_data_sequencer;
    m_write_response_sequencer = write_response_sequencer;
  endfunction

  task body();
    axi_mgr_txn_request_seq    aw_seq;
    axi_mgr_write_data_seq     w_seq;
    axi_mgr_write_response_seq b_seq;
    axi_write_response_item    write_response;

    if (m_write_response_router == null) begin
      `uvm_fatal(get_full_name(), "Cannot run sequence because there is no write response router.")
    end
    if (m_write_request_sequencer == null ||
        m_write_data_sequencer == null ||
        m_write_response_sequencer == null) begin
      `uvm_fatal(get_full_name(), "Cannot run sequence because sequencers are not all set.")
    end

    aw_seq = axi_mgr_txn_request_seq::type_id::create("aw_seq");
    aw_seq.m_use_fixed_id     = 1'b1; aw_seq.m_fixed_id     = m_req.m_id;
    aw_seq.m_use_fixed_addr   = 1'b1; aw_seq.m_fixed_addr   = m_req.m_addr;
    aw_seq.m_use_fixed_region = 1'b1; aw_seq.m_fixed_region = m_req.m_region;
    aw_seq.m_use_fixed_len    = 1'b1; aw_seq.m_fixed_len    = m_req.m_len;
    aw_seq.m_use_fixed_size   = 1'b1; aw_seq.m_fixed_size   = m_req.m_size;
    aw_seq.m_use_fixed_burst  = 1'b1; aw_seq.m_fixed_burst  = m_req.m_burst;
    aw_seq.m_use_fixed_lock   = 1'b1; aw_seq.m_fixed_lock   = m_req.m_lock;
    aw_seq.m_use_fixed_cache  = 1'b1; aw_seq.m_fixed_cache  = m_req.m_cache;
    aw_seq.m_use_fixed_prot   = 1'b1; aw_seq.m_fixed_prot   = m_req.m_prot;
    aw_seq.m_use_fixed_qos    = 1'b1; aw_seq.m_fixed_qos    = m_req.m_qos;
    aw_seq.m_use_fixed_user   = 1'b1; aw_seq.m_fixed_user   = m_req.m_user;
    if (!aw_seq.randomize()) begin
      `uvm_fatal(get_full_name(), "Failed to randomize aw_seq.")
    end

    w_seq = axi_mgr_write_data_seq::type_id::create("w_seq");
    if (!w_seq.randomize() with { m_number_of_items == local::m_req.m_len + 1; }) begin
      `uvm_fatal(get_full_name(), "Failed to randomize w_seq.")
    end

    b_seq = axi_mgr_write_response_seq::type_id::create("b_seq");
    if (!b_seq.randomize()) begin
      `uvm_fatal(get_full_name(), "Failed to randomize b_seq.")
    end

    fork begin
      b_seq.start(m_write_response_sequencer);
      if (b_seq.rsp != null) begin
        m_write_response_router.on_response(b_seq.rsp.m_id, b_seq.rsp);
      end
    end join_none

    fork
      aw_seq.start(m_write_request_sequencer);
      w_seq.start(m_write_data_sequencer);
      begin
        uvm_sequence_item raw_write_rsp;
        m_write_response_router.wait_for_response(m_req.m_id, raw_write_rsp);
        if (raw_write_rsp != null) void'($cast(write_response, raw_write_rsp));
      end
    join

    rsp = axi_fixed_write_rsp_item::type_id::create("rsp");
    rsp.m_aw_status      = aw_seq.rsp;
    rsp.m_w_status       = w_seq.rsp;
    rsp.m_write_response = write_response;
  endtask
endclass
