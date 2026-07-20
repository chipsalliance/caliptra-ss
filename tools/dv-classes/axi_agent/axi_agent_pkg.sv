// Copyright lowRISC contributors
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


  // Reset monitors for the five interfaces (all essentially the same thing, but the interface types
  // are different so we have to copy-paste the classes)
  `include "axi_reset_monitor_aw.svh"
  `include "axi_reset_monitor_w.svh"
  `include "axi_reset_monitor_b.svh"
  `include "axi_reset_monitor_ar.svh"
  `include "axi_reset_monitor_r.svh"

  `include "axi_reg_op_item.svh"
  `include "axi_reg_adapter.svh"

  typedef uvm_sequencer#(axi_txn_request_item, axi_status_item)       write_request_sequencer_t;
  typedef uvm_sequencer#(axi_write_data_item, axi_status_item)        write_data_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) write_response_sequencer_t;
  typedef uvm_sequencer#(axi_txn_request_item, axi_status_item)       read_request_sequencer_t;
  typedef uvm_sequencer#(axi_response_accept_item, uvm_sequence_item) read_data_sequencer_t;
  typedef uvm_sequencer#(axi_reg_op_item, uvm_sequence_item)          reg_op_sequencer_t;

  `include "seq_lib/axi_mgr_txn_request_seq.svh"
  `include "seq_lib/axi_mgr_write_data_seq.svh"
  `include "seq_lib/axi_mgr_write_single_data_seq.svh"
  `include "seq_lib/axi_mgr_write_response_seq.svh"
  `include "seq_lib/axi_mgr_read_data_seq.svh"

  `include "axi_fixed_write_req_item.svh"
  `include "axi_fixed_write_rsp_item.svh"
  `include "seq_lib/axi_mgr_write_fixed_vseq.svh"

  `include "axi_fixed_read_req_item.svh"
  `include "axi_fixed_read_rsp_item.svh"
  `include "seq_lib/axi_mgr_read_fixed_vseq.svh"

  `include "seq_lib/axi_mgr_register_layer_vseq.svh"

  `include "axi_agent_cfg.svh"
  `include "axi_mgr_agent.svh"
endpackage
