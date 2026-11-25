// Copyright 2026 Google LLC (chipsalliance project).
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
  int unsigned              m_data_width      = 32;
  int unsigned              m_user_data_width = 0;
  bit                       m_widths_set      = 1'b0;
  bit                       m_use_fixed_strb  = 1'b1;
  bit [127:0]               m_fixed_strb      = 128'hf;

  function new(string name="");
    super.new(name);
    m_req = axi_txn_request_item::type_id::create("m_req");
  endfunction

  function void set_widths(int unsigned data_width, int unsigned user_data_width);
    m_data_width      = data_width;
    m_user_data_width = user_data_width;
    m_widths_set      = 1'b1;
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
    if (m_widths_set) begin
      w_seq.set_widths(m_data_width, m_user_data_width);
    end else begin
      w_seq.m_data_width      = m_data_width;
      w_seq.m_user_data_width = m_user_data_width;
    end
    w_seq.m_use_fixed_strb = m_use_fixed_strb;
    w_seq.m_fixed_strb     = m_fixed_strb;
    if (!w_seq.randomize() with { m_number_of_items == local::m_req.m_len + 1; }) begin
      `uvm_fatal(get_full_name(), "Failed to randomize w_seq.")
    end

    b_seq = axi_mgr_write_response_seq::type_id::create("b_seq");
    if (!b_seq.randomize()) begin
      `uvm_fatal(get_full_name(), "Failed to randomize b_seq.")
    end

    begin
      int unsigned start_epoch;
      bit          rsp_done    = 1'b0;
      bit          req_aborted = 1'b0;
      axi_seq_lock_mgr::acquire_aw_w_issue(m_write_request_sequencer);
      start_epoch = m_write_response_router.get_reset_epoch();
      m_write_response_router.register_waiter(m_req.m_id, start_epoch);

      fork begin
        if (!req_aborted && (m_write_response_router.get_reset_epoch() == start_epoch)) begin
          b_seq.start(m_write_response_sequencer);
          if (b_seq.rsp != null) begin
            m_write_response_router.on_response(b_seq.rsp.m_id, b_seq.rsp);
          end
        end
        rsp_done = 1'b1;
      end join_none

      fork
        aw_seq.start(m_write_request_sequencer);
        w_seq.start(m_write_data_sequencer);
      join
      axi_seq_lock_mgr::release_aw_w_issue(m_write_request_sequencer);

      if (aw_seq.rsp != null && aw_seq.rsp.m_sending_complete &&
          w_seq.rsp != null && w_seq.rsp.m_sending_complete) begin
        uvm_sequence_item raw_write_rsp;
        m_write_response_router.wait_for_response(
            m_req.m_id, raw_write_rsp,
            .use_start_epoch(1'b1), .start_epoch(start_epoch),
            .pre_registered(1'b1), .release_waiter(1'b1));
        if (raw_write_rsp != null) void'($cast(write_response, raw_write_rsp));
      end else begin
        req_aborted = 1'b1;
        m_write_response_router.unregister_waiter(m_req.m_id);
      end
      wait (rsp_done || (m_write_response_router.get_reset_epoch() != start_epoch));
    end

    rsp = axi_fixed_write_rsp_item::type_id::create("rsp");
    rsp.m_aw_status      = aw_seq.rsp;
    rsp.m_w_status       = w_seq.rsp;
    rsp.m_write_response = write_response;
  endtask
endclass
