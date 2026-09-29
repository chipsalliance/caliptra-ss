// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction and coverage monitor for axi_read_data_if (the AXI R channel)

class axi_monitor_r extends uvm_monitor;
  `uvm_component_utils(axi_monitor_r)

  uvm_analysis_port #(axi_read_data_item) m_analysis_port;

  local virtual axi_read_data_if m_vif;
  local bit m_en_cov = 1'b1;
  local int unsigned m_stall_cycles;

  covergroup r_cg with function sample(axi_read_data_item item, int unsigned stall_cycles);
    option.per_instance = 1;
    cp_resp: coverpoint item.m_resp {
      bins okay   = {axi_read_data_item::RRespOkay};
      bins exokay = {axi_read_data_item::RRespExOkay};
      bins slverr = {axi_read_data_item::RRespSlverr};
      bins decerr = {axi_read_data_item::RRespDecErr};
    }
    cp_last: coverpoint item.m_last;
    cp_stall: coverpoint stall_cycles {
      bins zero_wait  = {0};
      bins short_wait = {[1:4]};
      bins long_wait  = {[5:$]};
    }
  endgroup

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_read_data_if vif);
  extern function void set_en_cov(bit en_cov);
endclass

function axi_monitor_r::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
  r_cg = new();
endfunction

function void axi_monitor_r::set_vif(virtual axi_read_data_if vif);
  m_vif = vif;
endfunction

function void axi_monitor_r::set_en_cov(bit en_cov);
  m_en_cov = en_cov;
endfunction

task axi_monitor_r::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  m_stall_cycles = 0;
  forever begin
    @(m_vif.mon_cb);
    if (!m_vif.rst_ni) begin
      m_stall_cycles = 0;
    end else if (m_vif.mon_cb.rvalid === 1'b1) begin
      if (m_vif.mon_cb.rready === 1'b1) begin
        axi_read_data_item item = axi_read_data_item::type_id::create("item");
        item.m_id   = m_vif.mon_cb.rid;
        item.m_data = m_vif.mon_cb.rdata;
        item.m_resp = axi_read_data_item::rresp_e'(m_vif.mon_cb.rresp);
        item.m_last = m_vif.mon_cb.rlast;
        item.m_user = m_vif.mon_cb.ruser;
        if (m_en_cov) r_cg.sample(item, m_stall_cycles);
        m_analysis_port.write(item);
        m_stall_cycles = 0;
      end else begin
        m_stall_cycles++;
      end
    end
  end
endtask
