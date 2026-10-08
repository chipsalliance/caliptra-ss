// Copyright 2026 Google LLC  (chipsalliance project)
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

    // Spawn R-channel consumer tokens for each beat in the burst
    fork begin
      for (int unsigned i = 0; i < num_beats; i++) begin
        axi_mgr_read_data_seq r_seq = axi_mgr_read_data_seq::type_id::create($sformatf("r_seq_%0d", i));
        if (!r_seq.randomize()) `uvm_fatal(get_full_name(), "Failed to randomize r_seq.")
        r_seq.start(m_read_data_sequencer);
        if (r_seq.rsp != null) begin
          m_read_response_router.on_response(r_seq.rsp.m_id, r_seq.rsp);
        end else begin
          break; // Reset occurred
        end
      end
    end join_none

    fork
      ar_seq.start(m_read_request_sequencer);
      begin
        for (int unsigned i = 0; i < num_beats; i++) begin
          uvm_sequence_item raw_read_data;
          axi_read_data_item beat_item;
          m_read_response_router.wait_for_response(m_req.m_id, raw_read_data);
          if (raw_read_data == null) break; // Reset occurred
          if ($cast(beat_item, raw_read_data)) begin
            m_read_data_items.push_back(beat_item);
            if (beat_item.m_last && (i + 1 != num_beats)) begin
              `uvm_error(get_full_name(), $sformatf("Early RLAST on beat %0d of %0d", i + 1, num_beats))
            end else if (!beat_item.m_last && (i + 1 == num_beats)) begin
              `uvm_error(get_full_name(), $sformatf("Missing RLAST on final beat %0d", num_beats))
            end
          end
        end
      end
    join

    m_ar_status = ar_seq.rsp;
  endtask
endclass
