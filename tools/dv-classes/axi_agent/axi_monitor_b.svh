// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction and coverage monitor for axi_write_response_if (the AXI B channel)

class axi_monitor_b extends uvm_monitor;
  `uvm_component_utils(axi_monitor_b)

  uvm_analysis_port #(axi_write_response_item) m_analysis_port;

  local virtual axi_write_response_if m_vif;
  local bit m_en_cov = 1'b1;
  local int unsigned m_stall_cycles;

  covergroup b_cg with function sample(axi_write_response_item item, int unsigned stall_cycles);
    option.per_instance = 1;
    cp_resp: coverpoint item.m_resp {
      bins okay   = {axi_write_response_item::BRespOkay};
      ignore_bins exokay = {axi_write_response_item::BRespExOkay};
      bins slverr = {axi_write_response_item::BRespSlverr};
      ignore_bins decerr = {axi_write_response_item::BRespDecErr};
    }
    cp_stall: coverpoint stall_cycles {
      bins zero_wait  = {0};
      bins short_wait = {[1:4]};
      bins long_wait  = {[5:$]};
    }
  endgroup

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_write_response_if vif);
  extern function void set_en_cov(bit en_cov);
endclass

function axi_monitor_b::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
  b_cg = new();
endfunction

function void axi_monitor_b::set_vif(virtual axi_write_response_if vif);
  m_vif = vif;
endfunction

function void axi_monitor_b::set_en_cov(bit en_cov);
  m_en_cov = en_cov;
endfunction

task axi_monitor_b::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  m_stall_cycles = 0;
  forever begin
    @(m_vif.mon_cb);
    if (!m_vif.rst_ni) begin
      m_stall_cycles = 0;
    end else if (m_vif.mon_cb.bvalid === 1'b1) begin
      if (m_vif.mon_cb.bready === 1'b1) begin
        axi_write_response_item item = axi_write_response_item::type_id::create("item");
        item.m_id   = m_vif.mon_cb.bid;
        item.m_resp = axi_write_response_item::bresp_e'(m_vif.mon_cb.bresp);
        item.m_user = m_vif.mon_cb.buser;
        if (m_en_cov) b_cg.sample(item, m_stall_cycles);
        m_analysis_port.write(item);
        m_stall_cycles = 0;
      end else begin
        m_stall_cycles++;
      end
    end
  end
endtask
