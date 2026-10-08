// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A Subordinate (Device) driver for axi_read_data_if, sending R transfers.

class axi_sub_read_data_driver extends uvm_driver#(axi_read_data_item, axi_status_item);
  `uvm_component_utils(axi_sub_read_data_driver)

  local virtual axi_read_data_if m_vif;
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_read_data_if vif);
  extern local task get_and_drive();
  extern local task monitor_reset();
  extern local task clear_data();
  extern local task drive_req(input bit aligned, output bit item_sent);
  extern local task set_data_from_req();
endclass

function axi_sub_read_data_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_sub_read_data_driver::set_vif(virtual axi_read_data_if vif);
  if (m_vif != null) `uvm_fatal(get_full_name(), "Cannot call set_vif: there is already an interface.")
  if (vif.if_mode != dv_utils_pkg::Device) begin
    `uvm_fatal(get_full_name(), $sformatf("Cannot drive interface: mode is %0s, not Device.", vif.if_mode.name()))
  end
  m_vif = vif;
endfunction

task axi_sub_read_data_driver::run_phase(uvm_phase phase);
  if (m_vif == null) `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
  clear_data();
  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_sub_read_data_driver::get_and_drive();
  axi_status_item status_item;
  bit aligned = 1'b0;

  forever begin
    if (!aligned) begin
      seq_item_port.get_next_item(req);
    end
    status_item = axi_status_item::type_id::create("status_item");
    drive_req(aligned, status_item.m_sending_complete);
    status_item.set_id_info(req);
    seq_item_port.item_done(status_item);

    if (status_item.m_sending_complete && !m_in_reset) begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        aligned = 1'b1;
      end else begin
        clear_data();
        aligned = 1'b0;
      end
    end else begin
      clear_data();
      aligned = 1'b0;
    end
  end
endtask

task axi_sub_read_data_driver::monitor_reset();
  wait(!$isunknown(m_vif.rst_ni));
  m_in_reset = !m_vif.rst_ni;
  forever begin
    wait (m_vif.rst_ni);
    m_in_reset = 0;
    wait (!m_vif.rst_ni);
    m_in_reset = 1;
    clear_data();
  end
endtask

task axi_sub_read_data_driver::clear_data();
  m_vif.sub_cb.rvalid <= 1'b0;
  m_vif.sub_cb.rid    <= 'x;
  m_vif.sub_cb.rdata  <= 'x;
  m_vif.sub_cb.rresp  <= 'x;
  m_vif.sub_cb.rlast  <= 'x;
  m_vif.sub_cb.ruser  <= 'x;
endtask

task axi_sub_read_data_driver::drive_req(input bit aligned, output bit item_sent);
  if (m_in_reset) return;
  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        if (!aligned) @(m_vif.sub_cb);
        set_data_from_req();
        m_vif.sub_cb.rvalid <= 1'b1;

        do begin
          @(m_vif.sub_cb);
        end while (m_vif.sub_cb.rready !== 1'b1);

        item_sent = 1'b1;
      end
    join_any
    disable fork;
  end join
endtask

task axi_sub_read_data_driver::set_data_from_req();
  req.m_id   &= (32'b1 << m_vif.id_r_width) - 1;
  req.m_data &= (1024'b1 << m_vif.data_width) - 1;
  req.m_user &= (528'b1 << (m_vif.user_data_width + m_vif.user_resp_width)) - 1;
  m_vif.sub_cb.rid   <= req.m_id;
  m_vif.sub_cb.rdata <= req.m_data;
  m_vif.sub_cb.rresp <= req.m_resp;
  m_vif.sub_cb.rlast <= req.m_last;
  m_vif.sub_cb.ruser <= req.m_user;
endtask
