// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package axi_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // The possible encodings of the AxBURST signal
  typedef enum bit [1:0] {
    BurstFixed = 0,
    BurstIncr  = 1,
    BurstWrap  = 2
  } burst_e;

  `include "axi_txn_request_item.svh"
  `include "axi_read_data_item.svh"

  `include "axi_write_data_item.svh"
  `include "axi_write_response_item.svh"

  `include "axi_response_accept_item.svh"

  `include "axi_status_item.svh"

  `include "axi_reset_item.svh"
  `include "axi_response_router.svh"

  `include "axi_mgr_write_request_driver.svh"
  `include "axi_mgr_write_data_driver.svh"
  `include "axi_mgr_write_response_driver.svh"

  `include "axi_mgr_read_request_driver.svh"
  `include "axi_mgr_read_data_driver.svh"

  `include "axi_sub_write_request_driver.svh"
  `include "axi_sub_write_data_driver.svh"
  `include "axi_sub_write_response_driver.svh"
  `include "axi_sub_read_request_driver.svh"
  `include "axi_sub_read_data_driver.svh"

  // Reset monitors for the five interfaces
  `include "axi_reset_monitor_aw.svh"
  `include "axi_reset_monitor_w.svh"
  `include "axi_reset_monitor_b.svh"
  `include "axi_reset_monitor_ar.svh"
  `include "axi_reset_monitor_r.svh"

  `include "axi_agent_cfg.svh"

  // Transaction and functional coverage monitors for the five interfaces
  `include "axi_monitor_aw.svh"
  `include "axi_monitor_w.svh"
  `include "axi_monitor_b.svh"
  `include "axi_monitor_ar.svh"
  `include "axi_monitor_r.svh"

  `include "axi_reg_op_item.svh"
  `include "axi_reg_adapter.svh"

  // Manager sequencer typedefs
  typedef uvm_sequencer#(axi_txn_request_item, axi_status_item)       write_request_sequencer_t;
  typedef uvm_sequencer#(axi_write_data_item, axi_status_item)        write_data_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) write_response_sequencer_t;
  typedef uvm_sequencer#(axi_txn_request_item, axi_status_item)       read_request_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) read_data_sequencer_t;
  typedef uvm_sequencer#(axi_reg_op_item, uvm_sequence_item)          reg_op_sequencer_t;

  // Subordinate sequencer typedefs
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) sub_write_request_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) sub_write_data_sequencer_t;
  typedef uvm_sequencer#(axi_write_response_item, axi_status_item)    sub_write_response_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) sub_read_request_sequencer_t;
  typedef uvm_sequencer#(axi_read_data_item, axi_status_item)         sub_read_data_sequencer_t;

  // Process-aware mutex that automatically reclaims ownership if the holding process is
  // terminated abnormally (e.g., via `disable fork` or `stop_sequences()` during random reset).
  class axi_proc_mutex;
    local process   m_waiters[$];
    local uvm_event m_release_ev;

    function new(string name = "axi_proc_mutex");
      m_release_ev = new(name);
    endfunction

    local function void prune_dead_front();
      while (m_waiters.size() > 0) begin
        process p = m_waiters[0];
        if (p == null || p.status() == process::FINISHED || p.status() == process::KILLED) begin
          void'(m_waiters.pop_front());
        end else begin
          break;
        end
      end
    endfunction

    task acquire();
      process self_proc = process::self();
      m_waiters.push_back(self_proc);
      forever begin
        prune_dead_front();
        if (m_waiters.size() > 0 && m_waiters[0] == self_proc) return;
        begin
          process head_proc = m_waiters[0];
          fork : wait_lock_fork begin
            fork
              m_release_ev.wait_trigger();
              if (head_proc != null) head_proc.await();
            join_any
            disable fork;
          end join
        end
      end
    endtask

    function void release_lock();
      process self_proc = process::self();
      prune_dead_front();
      if (m_waiters.size() > 0 && m_waiters[0] == self_proc) begin
        void'(m_waiters.pop_front());
        m_release_ev.trigger();
      end else begin
        foreach (m_waiters[i]) begin
          if (m_waiters[i] == self_proc) begin
            m_waiters.delete(i);
            m_release_ev.trigger();
            break;
          end
        end
      end
    endfunction
  endclass

  // Shared per-sequencer process-safe lock registry preserving AXI4 AW/W issue ordering,
  // per-ID AR/router registration ordering, and preventing W-beat interleaving across all
  // sequences on the same agent.
  class axi_seq_lock_mgr;
    local static axi_proc_mutex s_aw_w_issue_locks[uvm_sequencer_base];
    local static axi_proc_mutex s_w_burst_locks[uvm_sequencer_base];
    local static axi_proc_mutex s_ar_issue_locks[uvm_sequencer_base];

    static task acquire_aw_w_issue(uvm_sequencer_base aw_sqr);
      if (aw_sqr == null) return;
      if (!s_aw_w_issue_locks.exists(aw_sqr)) begin
        s_aw_w_issue_locks[aw_sqr] = new("aw_w_issue_mutex");
      end
      s_aw_w_issue_locks[aw_sqr].acquire();
    endtask

    static function void release_aw_w_issue(uvm_sequencer_base aw_sqr);
      if (aw_sqr != null && s_aw_w_issue_locks.exists(aw_sqr)) begin
        s_aw_w_issue_locks[aw_sqr].release_lock();
      end
    endfunction

    static task acquire_w_burst(uvm_sequencer_base w_sqr);
      if (w_sqr == null) return;
      if (!s_w_burst_locks.exists(w_sqr)) begin
        s_w_burst_locks[w_sqr] = new("w_burst_mutex");
      end
      s_w_burst_locks[w_sqr].acquire();
    endtask

    static function void release_w_burst(uvm_sequencer_base w_sqr);
      if (w_sqr != null && s_w_burst_locks.exists(w_sqr)) begin
        s_w_burst_locks[w_sqr].release_lock();
      end
    endfunction

    static task acquire_ar_issue(uvm_sequencer_base ar_sqr);
      if (ar_sqr == null) return;
      if (!s_ar_issue_locks.exists(ar_sqr)) begin
        s_ar_issue_locks[ar_sqr] = new("ar_issue_mutex");
      end
      s_ar_issue_locks[ar_sqr].acquire();
    endtask

    static function void release_ar_issue(uvm_sequencer_base ar_sqr);
      if (ar_sqr != null && s_ar_issue_locks.exists(ar_sqr)) begin
        s_ar_issue_locks[ar_sqr].release_lock();
      end
    endfunction
  endclass

  `include "seq_lib/axi_mgr_txn_request_seq.svh"
  `include "seq_lib/axi_mgr_write_data_seq.svh"
  `include "seq_lib/axi_mgr_write_single_data_seq.svh"
  `include "seq_lib/axi_mgr_write_response_seq.svh"
  `include "seq_lib/axi_mgr_read_data_seq.svh"

  `include "seq_lib/axi_sub_txn_accept_seq.svh"
  `include "seq_lib/axi_sub_write_data_accept_seq.svh"
  `include "seq_lib/axi_sub_write_response_seq.svh"
  `include "seq_lib/axi_sub_read_data_seq.svh"

  `include "axi_fixed_write_req_item.svh"
  `include "axi_fixed_write_rsp_item.svh"
  `include "seq_lib/axi_mgr_write_fixed_vseq.svh"
  `include "seq_lib/axi_mgr_write_burst_vseq.svh"

  `include "axi_fixed_read_req_item.svh"
  `include "axi_fixed_read_rsp_item.svh"
  `include "seq_lib/axi_mgr_read_fixed_vseq.svh"
  `include "seq_lib/axi_mgr_read_burst_vseq.svh"

  `include "seq_lib/axi_mgr_register_layer_vseq.svh"
  `include "axi_mgr_agent.svh"
  `include "axi_sub_agent.svh"
endpackage
