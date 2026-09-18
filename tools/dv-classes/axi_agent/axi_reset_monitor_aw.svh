// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A monitor for an axi_write_request_if (the AXI AW channel)

class axi_reset_monitor_aw extends uvm_monitor;
  `uvm_component_utils(axi_reset_monitor_aw);

  // A port that broadcasts an item on every reset state change.
  uvm_analysis_port #(axi_reset_item) m_analysis_port;

  // The interface being tracked. Set this with set_vif before run_phase.
  local virtual axi_write_request_if m_vif;

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);

  extern function void set_vif(virtual axi_write_request_if vif);
endclass

function axi_reset_monitor_aw::new(string name, uvm_component parent);
  super.new(name, parent);
  m_analysis_port = new("m_analysis_port", this);
endfunction

task axi_reset_monitor_aw::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot monitor interface: vif is null.")
    return;
  end

  wait(!$isunknown(m_vif.rst_ni));
  forever begin
    axi_reset_item rst_item;
    bit rst_n_bit = bit'(m_vif.rst_ni);

    rst_item = axi_reset_item::type_id::create("rst_item");
    rst_item.m_in_reset = !rst_n_bit;
    m_analysis_port.write(rst_item);

    wait(m_vif.rst_ni === !rst_n_bit);
  end
endtask


function void axi_reset_monitor_aw::set_vif(virtual axi_write_request_if vif);
  m_vif = vif;
endfunction
