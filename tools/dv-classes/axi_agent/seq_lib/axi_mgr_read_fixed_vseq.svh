// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that sends a single AXI read with ARBURST set to FIXED and ARLEN = 0 (so
// there is a single data transfer)
//
// The single request item is a randomised field (m_fixed_req) and the response is created in the
// rsp field, which will be created before the sequence completes.

class axi_mgr_read_fixed_vseq extends uvm_sequence#(uvm_sequence_item, axi_fixed_read_rsp_item);
  `uvm_object_utils(axi_mgr_read_fixed_vseq)

  // The read response router. Set this by calling set_read_response_router before starting the
  // sequence.
  local axi_response_router        m_read_response_router;

  // Sequencers for AR and R. Set these by calling set_sequencers before starting the sequence.
  local read_request_sequencer_t  m_read_request_sequencer;
  local read_data_sequencer_t     m_read_data_sequencer;

  // An item representing the single request that will be sent.
  rand axi_fixed_read_req_item m_fixed_req;

  extern function new(string name="");
  extern task body();

  // Set the read response router
  extern function void set_read_response_router(axi_response_router router);

  // Set sequencers for the AR and R channels
  extern function void set_sequencers(read_request_sequencer_t  read_request_sequencer,
                                      read_data_sequencer_t     read_data_sequencer);
endclass

function axi_mgr_read_fixed_vseq::new(string name="");
  super.new(name);
  m_fixed_req = axi_fixed_read_req_item::type_id::create("m_fixed_req");
endfunction

task axi_mgr_read_fixed_vseq::body();
  axi_mgr_txn_request_seq ar_seq;
  axi_mgr_read_data_seq   r_seq;
  axi_read_data_item      read_data;

  if (m_read_response_router == null) begin
    `uvm_fatal(get_full_name(), "Cannot run sequence because there is no read response router.")
  end

  if (m_read_request_sequencer == null || m_read_data_sequencer == null) begin
    `uvm_fatal(get_full_name(), "Cannot run sequence because sequencers are not both set.")
  end

  // Create the sequence to send the read request (AR). It doesn't need much randomising: we've
  // actually picked all the fields already in this virtual sequence. Use the "m_use_fixed_*"
  // variables to set things.
  ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq");
  ar_seq.m_use_fixed_id     = 1'b1;
  ar_seq.m_fixed_id         = m_fixed_req.m_id;
  ar_seq.m_use_fixed_addr   = 1'b1;
  ar_seq.m_fixed_addr       = m_fixed_req.m_addr;
  ar_seq.m_use_fixed_region = 1'b1;
  ar_seq.m_fixed_region     = m_fixed_req.m_region;
  ar_seq.m_use_fixed_len    = 1'b1;
  ar_seq.m_fixed_len        = 8'd0;
  ar_seq.m_use_fixed_size   = 1'b1;
  ar_seq.m_fixed_size       = m_fixed_req.m_size;
  ar_seq.m_use_fixed_burst  = 1'b1;
  ar_seq.m_fixed_burst      = BurstFixed;
  ar_seq.m_use_fixed_lock   = 1'b1;
  ar_seq.m_fixed_lock       = m_fixed_req.m_lock;
  ar_seq.m_use_fixed_cache  = 1'b1;
  ar_seq.m_fixed_cache      = m_fixed_req.m_cache;
  ar_seq.m_use_fixed_prot   = 1'b1;
  ar_seq.m_fixed_prot       = m_fixed_req.m_prot;
  ar_seq.m_use_fixed_qos    = 1'b1;
  ar_seq.m_fixed_qos        = m_fixed_req.m_qos;
  ar_seq.m_use_fixed_user   = 1'b1;
  ar_seq.m_fixed_user       = m_fixed_req.m_user;
  if (!ar_seq.randomize()) begin
    `uvm_fatal(get_full_name(), "Failed to randomize ar_seq.")
  end

  // Create a sequence to receive a single read data transaction (R). (This might or might not match
  // our ID, but that doesn't matter: the point is that we need to send it as a token)
  r_seq = axi_mgr_read_data_seq::type_id::create("r_seq");
  if (!r_seq.randomize()) begin
    `uvm_fatal(get_full_name(), "Failed to randomize r_seq.")
  end

  // Run the sequence to consume a read data item in the background. The item in question might not
  // be for the ID we're tracking, so we don't wait directly for it to finish.
  fork begin
    r_seq.start(m_read_data_sequencer);

    // Once the R channel sequence has finished, pass its read data to the router (unless there is
    // none, which means that both it and the router are seeing a reset).
    if (r_seq.rsp != null) begin
      m_read_response_router.on_response(r_seq.rsp.m_id, r_seq.rsp);
    end
  end join_none

  // Run the other sequences. This waits for ar_seq to complete and for a response from
  // m_read_response_router (which may or may not be the response to r_seq).
  fork
    ar_seq.start(m_read_request_sequencer);
    begin
      uvm_sequence_item raw_read_data;
      m_read_response_router.wait_for_response(m_fixed_req.m_id, raw_read_data);
      if (raw_read_data != null) void'($cast(read_data, raw_read_data));
    end
  join

  // At this point, the AR sequence has completed (either by sending its items or by seeing a reset)
  // and wait_for_response has completed, writing to read_data.
  rsp = axi_fixed_read_rsp_item::type_id::create("rsp");
  rsp.m_ar_status = ar_seq.rsp;
  rsp.m_read_data = read_data;
endtask

function void axi_mgr_read_fixed_vseq::set_read_response_router(axi_response_router router);
  if (router == null) `uvm_fatal(get_full_name(), "Router is null.")
  m_read_response_router = router;
endfunction

function void
  axi_mgr_read_fixed_vseq::set_sequencers(read_request_sequencer_t  read_request_sequencer,
                                          read_data_sequencer_t     read_data_sequencer);
  if (read_request_sequencer == null)  `uvm_fatal(get_full_name(), "No read_request_sequencer.")
  if (read_data_sequencer == null)     `uvm_fatal(get_full_name(), "No read_data_sequencer.")

  m_read_request_sequencer  = read_request_sequencer;
  m_read_data_sequencer     = read_data_sequencer;
endfunction
