// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver for axi_read_request_if, used when the testbench is acting as an AXI Manager that is
// requesting read transactions.
//
// Note: This is very similar to axi_mgr_write_request_driver (because the read and write request
// interfaces are very similar). Separating the interfaces and classes will allow future versions of
// the agent to support signals that only appear on one side, like the "stash" signals on the write
// side.

class axi_mgr_read_request_driver extends uvm_driver#(axi_txn_request_item, axi_status_item);
  `uvm_component_utils(axi_mgr_read_request_driver)

  local virtual axi_read_request_if m_vif;

  // True if the interface is currently in reset. Maintained by monitor_reset().
  //
  // At the very start of the simulation, rst_ni might be 'x or 'z. This isn't considered a "proper"
  // reset: in_reset can only be asserted by seeing rst_ni === 0 (and then cleared by seeing it
  // become 1).
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Set m_vif. This must be called before run_phase.
  extern function void set_vif(virtual axi_read_request_if vif);

  // Run forever, consuming and driving items from seq_item_port
  extern local task get_and_drive();

  // Run forever, tracking rst_ni and maintaining an in_reset class variable. Calls clear_data when
  // reset becomes asserted.
  extern local task monitor_reset();

  // A task that is called at the start of a reset and also at the end of driving an item.
  extern local task clear_data();

  // A task that drives the axi_txn_request_item in the req class variable
  //
  // This returns when the item is driven, setting item_sent=1, or returns early if a reset is
  // asserted, in which case it sets item_sent=0.
  extern local task drive_req(output bit item_sent);

  // Set data values in the interface based on the req item. This task runs in zero time (but uses
  // clocking block drives, so cannot be a function).
  //
  // This task also checks sizes against the ID_R_WIDTH, ADDR_WIDTH and USER_REQ_WIDTH properties
  // that are configured in the interface.
  extern local task set_data_from_req();
endclass

function axi_mgr_read_request_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_mgr_read_request_driver::set_vif(virtual axi_read_request_if vif);
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

task axi_mgr_read_request_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
    return;
  end

  // Start by clearing the data (and, importantly, setting m_vif.mgr_cb.arvalid = 0). From now,
  // arvalid will be zero unless $isunknown on all the data fields is false.
  clear_data();

  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_mgr_read_request_driver::get_and_drive();
  axi_status_item status_item;
  forever begin
    seq_item_port.get_next_item(req);
    status_item = axi_status_item::type_id::create("status_item");
    drive_req(status_item.m_sending_complete);
    seq_item_port.item_done(status_item);
  end
endtask

task axi_mgr_read_request_driver::monitor_reset();
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

task axi_mgr_read_request_driver::clear_data();
  m_vif.mgr_cb.arvalid  <= 1'b0;
  m_vif.mgr_cb.arid     <= 'x;
  m_vif.mgr_cb.araddr   <= 'x;
  m_vif.mgr_cb.arregion <= 'x;
  m_vif.mgr_cb.arlen    <= 'x;
  m_vif.mgr_cb.arsize   <= 'x;
  m_vif.mgr_cb.arburst  <= 'x;
  m_vif.mgr_cb.arlock   <= 'x;
  m_vif.mgr_cb.arcache  <= 'x;
  m_vif.mgr_cb.arprot   <= 'x;
  m_vif.mgr_cb.arqos    <= 'x;
  m_vif.mgr_cb.aruser   <= 'x;
endtask

task axi_mgr_read_request_driver::drive_req(output bit item_sent);
  // If we are currently in reset, there is nothing to do. This check avoids a possible race if
  // reset is asserted at the same time as the request appears: we don't want to set arvalid after
  // monitor_reset has called clear_data.
  if (m_in_reset) return;

  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        set_data_from_req();
        m_vif.mgr_cb.arvalid <= 1;

        do @(m_vif.mgr_cb); while (m_vif.mgr_cb.arready !== 1'b1);

        clear_data();

        // Because we finished sending the item, set item_sent to cause get_and_drive to set
        // m_sending_complete in its response.
        item_sent = 1'b1;
      end
    join_any
    disable fork;
  end join
endtask

task axi_mgr_read_request_driver::set_data_from_req();
  // Check that configurable-length item fields actually fit in the interface signals. Note: we can
  // safely drive all the bits in the clocking block here anyway: they will be truncated in the
  // interface when being reflected in the "*_internal" signal.
  if (|(req.m_id >> m_vif.id_r_width)) begin
    `uvm_error(get_full_name(),
               $sformatf("Cannot represent req.m_id = 0x%0h. The interface ID_R_WIDTH is %0d.",
                         req.m_id, m_vif.id_r_width))
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

  m_vif.mgr_cb.arid     <= req.m_id;
  m_vif.mgr_cb.araddr   <= req.m_addr;
  m_vif.mgr_cb.arregion <= req.m_region;
  m_vif.mgr_cb.arlen    <= req.m_len;
  m_vif.mgr_cb.arsize   <= req.m_size;
  m_vif.mgr_cb.arburst  <= req.m_burst;
  m_vif.mgr_cb.arlock   <= req.m_lock;
  m_vif.mgr_cb.arcache  <= req.m_cache;
  m_vif.mgr_cb.arprot   <= req.m_prot;
  m_vif.mgr_cb.arqos    <= req.m_qos;
  m_vif.mgr_cb.aruser   <= req.m_user;
endtask
