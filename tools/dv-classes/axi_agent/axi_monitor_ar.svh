// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction and coverage monitor for axi_read_request_if (the AXI AR channel)

class axi_monitor_ar extends uvm_monitor;
  `uvm_component_utils(axi_monitor_ar)

  uvm_analysis_port #(axi_txn_request_item) m_analysis_port;

  local virtual axi_read_request_if m_vif;
  local bit m_en_cov = 1'b1;
  local int unsigned m_stall_cycles;

  covergroup ar_cg with function sample(axi_txn_request_item item, int unsigned stall_cycles);
    option.per_instance = 1;
    cp_burst: coverpoint item.m_burst {
      bins fixed = {BurstFixed};
      bins incr  = {BurstIncr};
      bins wrap  = {BurstWrap};
    }
    cp_size: coverpoint item.m_size {
      bins size_1b   = {0};
      bins size_2b   = {1};
      bins size_4b   = {2};
      bins size_8b   = {3};
      bins size_wide = {[4:7]};
    }
    cp_len: coverpoint item.m_len {
      bins single     = {0};
      bins short_brst = {[1:15]};
      bins long_brst  = {[16:255]};
    }
    cp_lock: coverpoint item.m_lock;
    cp_stall: coverpoint stall_cycles {
      bins zero_wait  = {0};
      bins short_wait = {[1:4]};
      bins long_wait  = {[5:$]};
    }
    cx_burst_len: cross cp_burst, cp_len;
  endgroup

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_read_request_if vif);
  extern function void set_en_cov(bit en_cov);
endclass

function axi_monitor_ar::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
  ar_cg = new();
endfunction

function void axi_monitor_ar::set_vif(virtual axi_read_request_if vif);
  m_vif = vif;
endfunction

function void axi_monitor_ar::set_en_cov(bit en_cov);
  m_en_cov = en_cov;
endfunction

task axi_monitor_ar::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  m_stall_cycles = 0;
  forever begin
    @(m_vif.mon_cb);
    if (!m_vif.rst_ni) begin
      m_stall_cycles = 0;
    end else if (m_vif.mon_cb.arvalid === 1'b1) begin
      if (m_vif.mon_cb.arready === 1'b1) begin
        axi_txn_request_item item = axi_txn_request_item::type_id::create("item");
        item.m_id     = m_vif.mon_cb.arid;
        item.m_addr   = m_vif.mon_cb.araddr;
        item.m_region = m_vif.mon_cb.arregion;
        item.m_len    = m_vif.mon_cb.arlen;
        item.m_size   = m_vif.mon_cb.arsize;
        item.m_burst  = burst_e'(m_vif.mon_cb.arburst);
        item.m_lock   = m_vif.mon_cb.arlock;
        item.m_cache  = m_vif.mon_cb.arcache;
        item.m_prot   = m_vif.mon_cb.arprot;
        item.m_qos    = m_vif.mon_cb.arqos;
        item.m_user   = m_vif.mon_cb.aruser;
        if (m_en_cov) ar_cg.sample(item, m_stall_cycles);
        m_analysis_port.write(item);
        m_stall_cycles = 0;
      end else begin
        m_stall_cycles++;
      end
    end
  end
endtask
