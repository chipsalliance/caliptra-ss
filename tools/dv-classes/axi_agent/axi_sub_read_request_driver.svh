// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate (Device) driver for axi_read_request_if, accepting AR transfers.

class axi_sub_read_request_driver extends uvm_driver#(axi_response_accept_item, uvm_sequence_item);
  `uvm_component_utils(axi_sub_read_request_driver)

  local virtual axi_read_request_if m_vif;
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_read_request_if vif);
  extern local task get_and_drive();
  extern local task monitor_reset();
  extern local task drive_req();
endclass

function axi_sub_read_request_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_sub_read_request_driver::set_vif(virtual axi_read_request_if vif);
  if (m_vif != null) `uvm_fatal(get_full_name(), "Cannot call set_vif: there is already an interface.")
  if (vif.if_mode != dv_utils_pkg::Device) begin
    `uvm_fatal(get_full_name(), $sformatf("Cannot drive interface: mode is %0s, not Device.", vif.if_mode.name()))
  end
  m_vif = vif;
endfunction

task axi_sub_read_request_driver::run_phase(uvm_phase phase);
  if (m_vif == null) `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
  m_vif.sub_cb.arready <= 1'b0;
  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_sub_read_request_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    drive_req();
    seq_item_port.item_done(rsp);
  end
endtask

task axi_sub_read_request_driver::monitor_reset();
  wait(!$isunknown(m_vif.rst_ni));
  m_in_reset = !m_vif.rst_ni;
  forever begin
    wait (m_vif.rst_ni);
    m_in_reset = 0;
    wait (!m_vif.rst_ni);
    m_in_reset = 1;
    m_vif.sub_cb.arready <= 1'b0;
  end
endtask

task axi_sub_read_request_driver::drive_req();
  rsp = axi_status_item::type_id::create("rsp");
  rsp.set_id_info(req);
  if (m_in_reset) return;

  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        axi_txn_request_item txn_item;
        @(m_vif.sub_cb);
        while (m_vif.sub_cb.arvalid !== 1'b1) begin
          m_vif.sub_cb.arready <= $urandom_range(0, 99) < req.m_ready_without_valid_pct;
          @(m_vif.sub_cb);
        end
        if (m_vif.arready_internal !== 1'b1) begin
          repeat (req.m_valid_to_ready_delay) @(m_vif.sub_cb);
          m_vif.sub_cb.arready <= 1'b1;
          @(m_vif.sub_cb);
        end
        txn_item = axi_txn_request_item::type_id::create("txn_item");
        txn_item.m_id     = m_vif.sub_cb.arid;
        txn_item.m_addr   = m_vif.sub_cb.araddr;
        txn_item.m_region = m_vif.sub_cb.arregion;
        txn_item.m_len    = m_vif.sub_cb.arlen;
        txn_item.m_size   = m_vif.sub_cb.arsize;
        txn_item.m_burst  = burst_e'(m_vif.sub_cb.arburst);
        txn_item.m_lock   = m_vif.sub_cb.arlock;
        txn_item.m_cache  = m_vif.sub_cb.arcache;
        txn_item.m_prot   = m_vif.sub_cb.arprot;
        txn_item.m_qos    = m_vif.sub_cb.arqos;
        txn_item.m_user   = m_vif.sub_cb.aruser;
        rsp = txn_item;
        rsp.set_id_info(req);
        m_vif.sub_cb.arready <= 1'b0;
      end
    join_any
    disable fork;
  end join
endtask
