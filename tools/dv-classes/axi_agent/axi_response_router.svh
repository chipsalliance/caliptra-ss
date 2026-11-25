// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base class for routing responses from AXI Subordinates to Managers. These are routed based on
// RID / BID.

class axi_response_router extends uvm_component;
  `uvm_component_utils(axi_response_router)

  typedef uvm_sequence_item item_queue_t[$];
  typedef process           proc_queue_t[$];

  // An associative array that maps ID to a queue of response items that have been seen for that ID
  // (the FIFO works by pop_front and push_back), paired with a per-ID waiter process queue that
  // enforces strict FIFO wakeup ordering while automatically pruning killed/finished processes.
  local item_queue_t m_id_to_responses[int unsigned];
  local proc_queue_t m_id_waiters[int unsigned];

  // A flag that is set by assert_reset and cleared by clear_reset. When this is set,
  // m_id_to_responses will be empty and all calls to wait_for_response will return immediately.
  // m_reset_epoch increments on every reset assertion so waiters that wake after reset has
  // already deasserted still observe the reset and exit cleanly rather than hanging.
  local bit          m_in_reset;
  local int unsigned m_reset_epoch;

  // An event that triggers all waiting tasks. This runs when a new response is added to
  // m_id_to_responses or when a reset is asserted.
  local uvm_event m_update_event;

  // Optional interface handles / ID width used to mask response routing keys to the active wire ID width
  local virtual axi_read_request_if  m_read_req_vif;
  local virtual axi_write_request_if m_write_req_vif;
  local int unsigned                 m_id_width = 32;

  // An import for reset events (asserting or clearing reset)
  uvm_analysis_imp #(axi_reset_item, axi_response_router) reset_imp;

  extern function new (string name, uvm_component parent);

  extern function void set_read_request_vif(virtual axi_read_request_if vif);
  extern function void set_write_request_vif(virtual axi_write_request_if vif);
  extern function void set_id_width(int unsigned width);
  extern function int unsigned mask_id(int unsigned id);
  extern function int unsigned get_reset_epoch();
  extern function void register_waiter(int unsigned id, int unsigned expected_epoch);
  extern function void unregister_waiter(int unsigned id);
  extern local function void prune_dead_waiters(int unsigned masked_id);

  // The write function for reset_imp, which is called when a reset event is broadcast
  extern virtual function void write(axi_reset_item item);

  // Wait for a response to be seen with the given ID.
  //
  // This returns when such a response is seen, setting rsp. If there is a reset, this task will
  // return, setting rsp = null.
  // - use_start_epoch / start_epoch: when set, return rsp = null if a reset occurred since
  //   start_epoch even if reset has already deasserted before wait_for_response() is entered.
  // - pre_registered: when set, the caller already reserved its FIFO waiter slot via
  //   register_waiter() (preserving wire AR/AW order for concurrent same-ID transactions).
  // - release_waiter: when cleared, retain the caller at index 0 of m_id_waiters[masked_id] across
  //   subsequent beats of a multi-beat burst (pass release_waiter=1 on the final beat or call
  //   unregister_waiter() on early exit).
  extern task wait_for_response(int unsigned             id,
                                output uvm_sequence_item rsp,
                                input bit                use_start_epoch = 1'b0,
                                input int unsigned       start_epoch     = 0,
                                input bit                pre_registered  = 1'b0,
                                input bit                release_waiter  = 1'b1);

  // Notify the router that there has been the given response, for the supplied id.
  extern function void on_response(int unsigned id, uvm_sequence_item rsp);
endclass

function axi_response_router::new(string name, uvm_component parent);
  super.new(name, parent);
  m_update_event = new("m_update_event");
  reset_imp = new("reset_imp", this);
endfunction

function void axi_response_router::set_read_request_vif(virtual axi_read_request_if vif);
  m_read_req_vif = vif;
endfunction

function void axi_response_router::set_write_request_vif(virtual axi_write_request_if vif);
  m_write_req_vif = vif;
endfunction

function void axi_response_router::set_id_width(int unsigned width);
  m_id_width = (width > 32) ? 32 : width;
endfunction

function int unsigned axi_response_router::mask_id(int unsigned id);
  int unsigned width = m_id_width;
  if (m_read_req_vif != null)       width = m_read_req_vif.id_r_width;
  else if (m_write_req_vif != null) width = m_write_req_vif.id_w_width;
  if (width >= 32) return id;
  if (width == 0)  return 0;
  return id & ((32'h1 << width) - 1);
endfunction

function int unsigned axi_response_router::get_reset_epoch();
  return m_reset_epoch;
endfunction

function void axi_response_router::register_waiter(int unsigned id,
                                                   int unsigned expected_epoch);
  int unsigned masked_id = mask_id(id);
  process      self_proc = process::self();
  if (m_in_reset || (m_reset_epoch != expected_epoch)) return;
  if (!m_id_waiters.exists(masked_id)) begin
    m_id_waiters[masked_id] = '{};
  end
  m_id_waiters[masked_id].push_back(self_proc);
endfunction

function void axi_response_router::unregister_waiter(int unsigned id);
  int unsigned masked_id = mask_id(id);
  process      self_proc = process::self();
  if (!m_id_waiters.exists(masked_id)) return;
  for (int idx = 0; idx < m_id_waiters[masked_id].size(); idx++) begin
    if (m_id_waiters[masked_id][idx] == self_proc) begin
      m_id_waiters[masked_id].delete(idx);
      break;
    end
  end
  prune_dead_waiters(masked_id);
  if (m_id_to_responses.exists(masked_id) && m_id_waiters.exists(masked_id)) begin
    m_update_event.trigger();
  end
endfunction

function void axi_response_router::prune_dead_waiters(int unsigned masked_id);
  if (!m_id_waiters.exists(masked_id)) return;
  while (m_id_waiters[masked_id].size() > 0) begin
    process p = m_id_waiters[masked_id][0];
    if (p == null || p.status() == process::FINISHED || p.status() == process::KILLED) begin
      void'(m_id_waiters[masked_id].pop_front());
    end else begin
      break;
    end
  end
  if (m_id_waiters[masked_id].size() == 0) begin
    m_id_waiters.delete(masked_id);
  end
endfunction

function void axi_response_router::write(axi_reset_item item);
  if (item.m_in_reset) begin
    // Reset is being asserted. If we don't know about it already, set a flag, bump reset epoch,
    // clear m_id_to_responses and m_id_waiters, and trigger the event to wake all waiters.
    if (!m_in_reset) begin
      m_in_reset = 1'b1;
      m_reset_epoch++;
      m_id_to_responses.delete();
      m_id_waiters.delete();
      m_update_event.trigger();
    end
  end else begin
    // Reset is being cleared. All we have to do is clear m_in_reset.
    m_in_reset = 1'b0;
  end
endfunction

task axi_response_router::wait_for_response(int unsigned             id,
                                            output uvm_sequence_item rsp,
                                            input bit                use_start_epoch,
                                            input int unsigned       start_epoch,
                                            input bit                pre_registered,
                                            input bit                release_waiter);
  int unsigned masked_id      = mask_id(id);
  process      self_proc      = process::self();
  int unsigned eff_epoch      = use_start_epoch ? start_epoch : m_reset_epoch;
  bit          already_queued = 1'b0;

  if (m_in_reset || (m_reset_epoch != eff_epoch)) begin
    rsp = null;
    if (pre_registered) unregister_waiter(id);
    return;
  end

  if (pre_registered && m_id_waiters.exists(masked_id)) begin
    foreach (m_id_waiters[masked_id][idx]) begin
      if (m_id_waiters[masked_id][idx] == self_proc) begin
        already_queued = 1'b1;
        break;
      end
    end
  end
  if (!already_queued) begin
    if (!m_id_waiters.exists(masked_id)) begin
      m_id_waiters[masked_id] = '{};
    end
    m_id_waiters[masked_id].push_back(self_proc);
  end

  forever begin
    prune_dead_waiters(masked_id);
    if (m_in_reset || (m_reset_epoch != eff_epoch)) break;
    if (m_id_to_responses.exists(masked_id) &&
        m_id_waiters.exists(masked_id) &&
        m_id_waiters[masked_id].size() > 0 &&
        m_id_waiters[masked_id][0] == self_proc) begin
      break;
    end
    if (m_id_waiters.exists(masked_id) &&
        m_id_waiters[masked_id].size() > 0 &&
        m_id_waiters[masked_id][0] != self_proc) begin
      process head_proc = m_id_waiters[masked_id][0];
      fork : wait_head_or_ev begin
        fork
          m_update_event.wait_trigger();
          if (head_proc != null) head_proc.await();
        join_any
        disable fork;
      end join
    end else begin
      m_update_event.wait_trigger();
    end
  end

  if (m_in_reset || (m_reset_epoch != eff_epoch)) begin
    rsp = null;
    unregister_waiter(id);
  end else begin
    if (m_id_to_responses[masked_id].size() == 0) begin
      `uvm_fatal(get_full_name(),
                 $sformatf("m_id_to_responses[0x%0h] is an empty queue.", masked_id))
    end

    rsp = m_id_to_responses[masked_id].pop_front();
    if (m_id_to_responses[masked_id].size() == 0) begin
      m_id_to_responses.delete(masked_id);
    end

    if (release_waiter) begin
      if (m_id_waiters.exists(masked_id) &&
          m_id_waiters[masked_id].size() > 0 &&
          m_id_waiters[masked_id][0] == self_proc) begin
        void'(m_id_waiters[masked_id].pop_front());
      end
      prune_dead_waiters(masked_id);

      // If additional responses are already queued for another live waiter on this ID, notify it.
      if (m_id_to_responses.exists(masked_id) && m_id_waiters.exists(masked_id)) begin
        m_update_event.trigger();
      end
    end
  end
endtask

function void axi_response_router::on_response(int unsigned id, uvm_sequence_item rsp);
  int unsigned masked_id = mask_id(id);
  if (rsp == null) `uvm_fatal(get_full_name(), "rsp must not be null.")

  if (!m_in_reset) begin
    if (!m_id_to_responses.exists(masked_id)) begin
      m_id_to_responses[masked_id] = '{};
    end
    m_id_to_responses[masked_id].push_back(rsp);
    m_update_event.trigger();
  end
endfunction
