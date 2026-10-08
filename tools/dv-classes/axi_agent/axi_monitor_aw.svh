// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction and coverage monitor for axi_write_request_if (the AXI AW channel)

class axi_monitor_aw extends uvm_monitor;
  `uvm_component_utils(axi_monitor_aw)

  uvm_analysis_port #(axi_txn_request_item) m_analysis_port;

  local virtual axi_write_request_if m_vif;
  local bit m_en_cov = 1'b1;
  local int unsigned m_stall_cycles;

  covergroup aw_cg with function sample(axi_txn_request_item item, int unsigned stall_cycles);
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
    cx_burst_len: cross cp_burst, cp_len {
      ignore_bins illegal_wrap  = binsof(cp_burst.wrap)  && (binsof(cp_len.single) || binsof(cp_len.long_brst));
      ignore_bins illegal_fixed = binsof(cp_burst.fixed) && binsof(cp_len.long_brst);
    }
  endgroup

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_write_request_if vif);
  extern function void set_en_cov(bit en_cov);
endclass

function axi_monitor_aw::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
  aw_cg = new();
endfunction

function void axi_monitor_aw::set_vif(virtual axi_write_request_if vif);
  m_vif = vif;
endfunction

function void axi_monitor_aw::set_en_cov(bit en_cov);
  m_en_cov = en_cov;
endfunction

task axi_monitor_aw::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  m_stall_cycles = 0;
  forever begin
    @(m_vif.mon_cb);
    if (!m_vif.rst_ni) begin
      m_stall_cycles = 0;
    end else if (m_vif.mon_cb.awvalid === 1'b1) begin
      if (m_vif.mon_cb.awready === 1'b1) begin
        axi_txn_request_item item = axi_txn_request_item::type_id::create("item");
        item.m_id     = m_vif.mon_cb.awid;
        item.m_addr   = m_vif.mon_cb.awaddr;
        item.m_region = m_vif.mon_cb.awregion;
        item.m_len    = m_vif.mon_cb.awlen;
        item.m_size   = m_vif.mon_cb.awsize;
        item.m_burst  = burst_e'(m_vif.mon_cb.awburst);
        item.m_lock   = m_vif.mon_cb.awlock;
        item.m_cache  = m_vif.mon_cb.awcache;
        item.m_prot   = m_vif.mon_cb.awprot;
        item.m_qos    = m_vif.mon_cb.awqos;
        item.m_user   = m_vif.mon_cb.awuser;
        if (m_en_cov) aw_cg.sample(item, m_stall_cycles);
        m_analysis_port.write(item);
        m_stall_cycles = 0;
      end else begin
        m_stall_cycles++;
      end
    end
  end
endtask
