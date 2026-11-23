// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that sends a multi-beat AXI read burst (ARLEN = 0..255, BurstFixed/Incr/Wrap)
// and collects all (m_len + 1) R channel data beats via the read response router until RLAST.

class axi_mgr_read_burst_vseq extends uvm_sequence#(uvm_sequence_item, uvm_sequence_item);
  `uvm_object_utils(axi_mgr_read_burst_vseq)

  local axi_response_router       m_read_response_router;
  local read_request_sequencer_t  m_read_request_sequencer;
  local read_data_sequencer_t     m_read_data_sequencer;

  rand axi_txn_request_item m_req;
  axi_status_item           m_ar_status;
  axi_read_data_item        m_read_data_items[$];

  function new(string name="");
    super.new(name);
    m_req = axi_txn_request_item::type_id::create("m_req");
  endfunction

  function void set_read_response_router(axi_response_router router);
    if (router == null) `uvm_fatal(get_full_name(), "Router is null.")
    m_read_response_router = router;
  endfunction

  function void set_sequencers(read_request_sequencer_t read_request_sequencer,
                               read_data_sequencer_t    read_data_sequencer);
    if (read_request_sequencer == null) `uvm_fatal(get_full_name(), "No read_request_sequencer.")
    if (read_data_sequencer == null)    `uvm_fatal(get_full_name(), "No read_data_sequencer.")
    m_read_request_sequencer = read_request_sequencer;
    m_read_data_sequencer    = read_data_sequencer;
  endfunction

  task body();
    axi_mgr_txn_request_seq ar_seq;
    int unsigned num_beats;

    if (m_read_response_router == null) begin
      `uvm_fatal(get_full_name(), "Cannot run sequence because there is no read response router.")
    end
    if (m_read_request_sequencer == null || m_read_data_sequencer == null) begin
      `uvm_fatal(get_full_name(), "Cannot run sequence because sequencers are not both set.")
    end

    num_beats = m_req.m_len + 1;
    m_read_data_items.delete();

    ar_seq = axi_mgr_txn_request_seq::type_id::create("ar_seq");
    ar_seq.m_use_fixed_id     = 1'b1; ar_seq.m_fixed_id     = m_req.m_id;
    ar_seq.m_use_fixed_addr   = 1'b1; ar_seq.m_fixed_addr   = m_req.m_addr;
    ar_seq.m_use_fixed_region = 1'b1; ar_seq.m_fixed_region = m_req.m_region;
    ar_seq.m_use_fixed_len    = 1'b1; ar_seq.m_fixed_len    = m_req.m_len;
    ar_seq.m_use_fixed_size   = 1'b1; ar_seq.m_fixed_size   = m_req.m_size;
    ar_seq.m_use_fixed_burst  = 1'b1; ar_seq.m_fixed_burst  = m_req.m_burst;
    ar_seq.m_use_fixed_lock   = 1'b1; ar_seq.m_fixed_lock   = m_req.m_lock;
    ar_seq.m_use_fixed_cache  = 1'b1; ar_seq.m_fixed_cache  = m_req.m_cache;
    ar_seq.m_use_fixed_prot   = 1'b1; ar_seq.m_fixed_prot   = m_req.m_prot;
    ar_seq.m_use_fixed_qos    = 1'b1; ar_seq.m_fixed_qos    = m_req.m_qos;
    ar_seq.m_use_fixed_user   = 1'b1; ar_seq.m_fixed_user   = m_req.m_user;
    if (!ar_seq.randomize()) begin
      `uvm_fatal(get_full_name(), "Failed to randomize ar_seq.")
    end

    // Demand-driven R-channel token loop synchronized explicitly with the collector via
    // tokens_allowed / tokens_started (no #0 yield race, never killing cur_r_seq mid-handshake,
    // and strict per-burst token conservation across interleaved multi-ID and same-ID pipelined
    // bursts). AR issuance is serialized with router waiter registration so router FIFO order
    // strictly matches wire AR order, and burst-level waiter retention prevents same-ID beat
    // interleaving across concurrent multi-beat bursts.
    begin
      bit                   reset_seen     = 1'b0;
      bit                   done           = 1'b0;
      bit                   r_loop_done    = 1'b0;
      int unsigned          tokens_allowed = 1;
      int unsigned          tokens_started = 0;
      int unsigned          start_epoch;
      axi_mgr_read_data_seq cur_r_seq;

      axi_seq_lock_mgr::acquire_ar_issue(m_read_request_sequencer);
      start_epoch = m_read_response_router.get_reset_epoch();
      m_read_response_router.register_waiter(m_req.m_id, start_epoch);

      fork begin
        forever begin
          wait (reset_seen ||
                (m_read_response_router.get_reset_epoch() != start_epoch) ||
                (tokens_started < tokens_allowed) ||
                (done && (tokens_started >= tokens_allowed)));
          if (reset_seen ||
              (m_read_response_router.get_reset_epoch() != start_epoch) ||
              (done && (tokens_started >= tokens_allowed))) break;
          cur_r_seq = axi_mgr_read_data_seq::type_id::create($sformatf("r_seq_%0d", tokens_started));
          if (!cur_r_seq.randomize()) `uvm_fatal(get_full_name(), "Failed to randomize r_seq.")
          tokens_started++;
          cur_r_seq.start(m_read_data_sequencer);
          if (cur_r_seq.rsp != null) begin
            m_read_response_router.on_response(cur_r_seq.rsp.m_id, cur_r_seq.rsp);
            if (reset_seen ||
                (m_read_response_router.get_reset_epoch() != start_epoch) ||
                (done && (tokens_started >= tokens_allowed))) break;
          end else begin
            reset_seen = 1'b1;
            break; // Reset occurred
          end
        end
        r_loop_done = 1'b1;
      end join_none

      ar_seq.start(m_read_request_sequencer);
      axi_seq_lock_mgr::release_ar_issue(m_read_request_sequencer);

      if (ar_seq.rsp != null && ar_seq.rsp.m_sending_complete) begin
        for (int unsigned i = 0; i < num_beats; i++) begin
          uvm_sequence_item  raw_read_data;
          axi_read_data_item beat_item;
          bit                is_final_beat = (i + 1 == num_beats);
          m_read_response_router.wait_for_response(
              m_req.m_id, raw_read_data,
              .use_start_epoch(1'b1), .start_epoch(start_epoch),
              .pre_registered(1'b1), .release_waiter(is_final_beat));
          if (raw_read_data == null) begin
            reset_seen = 1'b1;
            break; // Reset occurred
          end
          if ($cast(beat_item, raw_read_data)) begin
            m_read_data_items.push_back(beat_item);
            if (beat_item.m_last && !is_final_beat) begin
              `uvm_error(get_full_name(), $sformatf("Early RLAST on beat %0d of %0d", i + 1, num_beats))
              tokens_allowed = i + 1;
              m_read_response_router.unregister_waiter(m_req.m_id);
              break;
            end else if (!beat_item.m_last && is_final_beat) begin
              `uvm_error(get_full_name(), $sformatf("Missing RLAST on final beat %0d", num_beats))
            end else if (!beat_item.m_last && !is_final_beat) begin
              tokens_allowed = i + 2;
            end
          end
        end
      end else begin
        reset_seen = 1'b1;
        m_read_response_router.unregister_waiter(m_req.m_id);
      end
      done = 1'b1;
      wait (r_loop_done || (m_read_response_router.get_reset_epoch() != start_epoch));
    end

    m_ar_status = ar_seq.rsp;
  endtask
endclass
