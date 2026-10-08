// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction and coverage monitor for axi_write_data_if (the AXI W channel)

class axi_monitor_w extends uvm_monitor;
  `uvm_component_utils(axi_monitor_w)

  uvm_analysis_port #(axi_write_data_item) m_analysis_port;

  local virtual axi_write_data_if m_vif;
  local bit m_en_cov = 1'b1;
  local int unsigned m_stall_cycles;

  covergroup w_cg with function sample(axi_write_data_item item, int unsigned stall_cycles);
    option.per_instance = 1;
    cp_last: coverpoint item.m_last;
    cp_strb_low: coverpoint item.m_strb[3:0] {
      bins none = {4'h0};
      bins full = {4'hF};
      bins part = default;
    }
    cp_stall: coverpoint stall_cycles {
      bins zero_wait  = {0};
      bins short_wait = {[1:4]};
      bins long_wait  = {[5:$]};
    }
  endgroup

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_write_data_if vif);
  extern function void set_en_cov(bit en_cov);
endclass

function axi_monitor_w::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
  w_cg = new();
endfunction

function void axi_monitor_w::set_vif(virtual axi_write_data_if vif);
  m_vif = vif;
endfunction

function void axi_monitor_w::set_en_cov(bit en_cov);
  m_en_cov = en_cov;
endfunction

task axi_monitor_w::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  m_stall_cycles = 0;
  forever begin
    @(m_vif.mon_cb);
    if (!m_vif.rst_ni) begin
      m_stall_cycles = 0;
    end else if (m_vif.mon_cb.wvalid === 1'b1) begin
      if (m_vif.mon_cb.wready === 1'b1) begin
        axi_write_data_item item = axi_write_data_item::type_id::create("item");
        item.m_data = m_vif.mon_cb.wdata;
        item.m_strb = m_vif.mon_cb.wstrb;
        item.m_last = m_vif.mon_cb.wlast;
        item.m_user = m_vif.mon_cb.wuser;
        if (m_en_cov) w_cg.sample(item, m_stall_cycles);
        m_analysis_port.write(item);
        m_stall_cycles = 0;
      end else begin
        m_stall_cycles++;
      end
    end
  end
endtask
