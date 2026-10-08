// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver for axi_write_request_if, used when the testbench is acting as an AXI Manager that is
// sending write requests.

class axi_mgr_write_request_driver extends uvm_driver#(axi_txn_request_item, axi_status_item);
  `uvm_component_utils(axi_mgr_write_request_driver)

  local virtual axi_write_request_if m_vif;

  // True if the interface is currently in reset. Maintained by monitor_reset().
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);
  extern function void set_vif(virtual axi_write_request_if vif);
  extern local task get_and_drive();
  extern local task monitor_reset();
  extern local task clear_data();
  extern local task drive_req(input bit aligned, output bit item_sent);
  extern local task set_data_from_req();
endclass

function axi_mgr_write_request_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_mgr_write_request_driver::set_vif(virtual axi_write_request_if vif);
  if (m_vif != null) begin
    `uvm_fatal(get_full_name(), "Cannot call set_vif: there is already an interface.")
    return;
  end

  if (vif.if_mode != dv_utils_pkg::Host) begin
    `uvm_fatal(get_full_name(),
               $sformatf("Cannot drive this interface: it has mode %0s, not Host.",
                         vif.if_mode.name()))
    return;
  end

  m_vif = vif;
endfunction

task axi_mgr_write_request_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
    return;
  end

  clear_data();

  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_mgr_write_request_driver::get_and_drive();
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

    // Check if another request is immediately ready for 0-bubble back-to-back driving
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

task axi_mgr_write_request_driver::monitor_reset();
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

task axi_mgr_write_request_driver::clear_data();
  m_vif.mgr_cb.awvalid  <= 1'b0;
  m_vif.mgr_cb.awid     <= 'x;
  m_vif.mgr_cb.awaddr   <= 'x;
  m_vif.mgr_cb.awregion <= 'x;
  m_vif.mgr_cb.awlen    <= 'x;
  m_vif.mgr_cb.awsize   <= 'x;
  m_vif.mgr_cb.awburst  <= 'x;
  m_vif.mgr_cb.awlock   <= 'x;
  m_vif.mgr_cb.awcache  <= 'x;
  m_vif.mgr_cb.awprot   <= 'x;
  m_vif.mgr_cb.awqos    <= 'x;
  m_vif.mgr_cb.awuser   <= 'x;
endtask

task axi_mgr_write_request_driver::drive_req(input bit aligned, output bit item_sent);
  if (m_in_reset) return;

  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        if (!aligned) @(m_vif.mgr_cb);
        set_data_from_req();
        m_vif.mgr_cb.awvalid <= 1'b1;

        do begin
          @(m_vif.mgr_cb);
        end while (m_vif.mgr_cb.awready !== 1'b1);

        item_sent = 1'b1;
      end
    join_any
    disable fork;
  end join
endtask

task axi_mgr_write_request_driver::set_data_from_req();
  req.m_id   &= (32'b1 << m_vif.id_w_width) - 1;
  req.m_addr &= (64'b1 << m_vif.addr_width) - 1;
  req.m_user &= (128'b1 << m_vif.user_req_width) - 1;

  if (|(req.m_id >> m_vif.id_w_width)) begin
    `uvm_error(get_full_name(),
               $sformatf("Cannot represent req.m_id = 0x%0h. The interface ID_W_WIDTH is %0d.",
                         req.m_id, m_vif.id_w_width))
  end
  if (|(req.m_addr >> m_vif.addr_width)) begin
    `uvm_error(get_full_name(),
               $sformatf("Cannot represent req.m_addr = 0x%0h. The interface ADDR_WIDTH is %0d.",
                         req.m_addr, m_vif.addr_width))
  end
  if (|(req.m_user >> m_vif.user_req_width)) begin
    `uvm_error(get_full_name(),
               $sformatf({"Cannot represent req.m_user = 0x%0h. ",
                          "The interface USER_REQ_WIDTH is %0d."},
                         req.m_user, m_vif.user_req_width))
  end

  m_vif.mgr_cb.awid     <= req.m_id;
  m_vif.mgr_cb.awaddr   <= req.m_addr;
  m_vif.mgr_cb.awregion <= req.m_region;
  m_vif.mgr_cb.awlen    <= req.m_len;
  m_vif.mgr_cb.awsize   <= req.m_size;
  m_vif.mgr_cb.awburst  <= req.m_burst;
  m_vif.mgr_cb.awlock   <= req.m_lock;
  m_vif.mgr_cb.awcache  <= req.m_cache;
  m_vif.mgr_cb.awprot   <= req.m_prot;
  m_vif.mgr_cb.awqos    <= req.m_qos;
  m_vif.mgr_cb.awuser   <= req.m_user;
endtask
