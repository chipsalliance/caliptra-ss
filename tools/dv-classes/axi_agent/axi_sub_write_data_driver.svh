// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate (Device) driver for axi_write_data_if, accepting W transfers.

class axi_sub_write_data_driver extends uvm_driver#(axi_response_accept_item, uvm_sequence_item);
  `uvm_component_utils(axi_sub_write_data_driver)

  local virtual axi_write_data_if m_vif;
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_write_data_if vif);
  extern local task get_and_drive();
  extern local task monitor_reset();
  extern local task drive_req();
endclass

function axi_sub_write_data_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_sub_write_data_driver::set_vif(virtual axi_write_data_if vif);
  if (m_vif != null) `uvm_fatal(get_full_name(), "Cannot call set_vif: there is already an interface.")
  if (vif.if_mode != dv_utils_pkg::Device) begin
    `uvm_fatal(get_full_name(), $sformatf("Cannot drive interface: mode is %0s, not Device.", vif.if_mode.name()))
  end
  m_vif = vif;
endfunction

task axi_sub_write_data_driver::run_phase(uvm_phase phase);
  if (m_vif == null) `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
  m_vif.sub_cb.wready <= 1'b0;
  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_sub_write_data_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    drive_req();
    seq_item_port.item_done(rsp);
  end
endtask

task axi_sub_write_data_driver::monitor_reset();
  wait(!$isunknown(m_vif.rst_ni));
  m_in_reset = !m_vif.rst_ni;
  forever begin
    wait (m_vif.rst_ni);
    m_in_reset = 0;
    wait (!m_vif.rst_ni);
    m_in_reset = 1;
    m_vif.sub_cb.wready <= 1'b0;
  end
endtask

task axi_sub_write_data_driver::drive_req();
  rsp = axi_status_item::type_id::create("rsp");
  rsp.set_id_info(req);
  if (m_in_reset) return;

  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        axi_write_data_item w_item;
        @(m_vif.sub_cb);
        while (m_vif.sub_cb.wvalid !== 1'b1) begin
          m_vif.sub_cb.wready <= $urandom_range(0, 99) < req.m_ready_without_valid_pct;
          @(m_vif.sub_cb);
        end
        if (m_vif.wready_internal !== 1'b1) begin
          repeat (req.m_valid_to_ready_delay) @(m_vif.sub_cb);
          m_vif.sub_cb.wready <= 1'b1;
          @(m_vif.sub_cb);
        end
        w_item = axi_write_data_item::type_id::create("w_item");
        w_item.m_data = m_vif.sub_cb.wdata;
        w_item.m_strb = m_vif.sub_cb.wstrb;
        w_item.m_last = m_vif.sub_cb.wlast;
        w_item.m_user = m_vif.sub_cb.wuser;
        rsp = w_item;
        rsp.set_id_info(req);
        m_vif.sub_cb.wready <= 1'b0;
      end
    join_any
    disable fork;
  end join
endtask
