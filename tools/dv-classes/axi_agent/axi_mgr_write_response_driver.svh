// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver for axi_write_response_if, used when the testbench is acting as an AXI Manager that is
// accepting write responses.
//
// This will normally send an axi_write_response_item as a response to the sequencer. If sending the
// request is interrupted by a reset, this will instead return a axi_status_item with
// m_sending_complete == 0.

class axi_mgr_write_response_driver extends uvm_driver#(axi_response_accept_item,
                                                        uvm_sequence_item);
  `uvm_component_utils(axi_mgr_write_response_driver)

  local virtual axi_write_response_if m_vif;

  // True if the interface is currently in reset. Maintained by monitor_reset().
  //
  // At the very start of the simulation, rst_ni might be 'x or 'z. This isn't considered a "proper"
  // reset: in_reset can only be asserted by seeing rst_ni === 0 (and then cleared by seeing it
  // become 1).
  local bit m_in_reset;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Set m_vif. This must be called before run_phase.
  extern function void set_vif(virtual axi_write_response_if vif);

  // Run forever, consuming and driving items from seq_item_port
  extern local task get_and_drive();

  // Run forever, tracking rst_ni and maintaining an in_reset class variable. Clears bready in the
  // clocking block when a reset is seen.
  extern local task monitor_reset();

  // A task that drives the axi_response_accept_item in the req class variable
  //
  // This returns when the response has been accepted, setting rsp to be an axi_write_response_item
  // with its contents. If there is a reset, the task returns early and sets rsp to be an
  // axi_status_item with m_sending_complete == 0.
  extern local task drive_req();
endclass

function axi_mgr_write_response_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void axi_mgr_write_response_driver::set_vif(virtual axi_write_response_if vif);
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

task axi_mgr_write_response_driver::run_phase(uvm_phase phase);
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "Cannot drive interface: vif is null.")
    return;
  end

  // Clear bready (we only wish to assert that we are ready if we are driving an item)
  m_vif.mgr_cb.bready <= 1'b0;

  fork
    get_and_drive();
    monitor_reset();
  join
endtask

task axi_mgr_write_response_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    drive_req();
    if (rsp != null) rsp.set_id_info(req);
    seq_item_port.item_done(rsp);
  end
endtask

task axi_mgr_write_response_driver::monitor_reset();
  wait(!$isunknown(m_vif.rst_ni));
  m_in_reset = !m_vif.rst_ni;
  forever begin
    wait (m_vif.rst_ni);
    m_in_reset = 0;
    wait (!m_vif.rst_ni);
    m_in_reset = 1;
    m_vif.mgr_cb.bready <= 1'b0;
  end
endtask

task axi_mgr_write_response_driver::drive_req();
  // Create a default response, which is an axi_status_item with its default state
  // (m_sending_complete = 0). This will be overridden with an axi_write_response_item if a response
  // is read.
  rsp = axi_status_item::type_id::create("rsp");

  // If we are currently in reset, there is nothing to do. This check avoids a possible race if
  // reset is asserted at the same time as the response appears: we don't want to set bready after
  // monitor_reset has cleared it.
  if (m_in_reset) begin
    return;
  end

  fork : isolation_fork begin
    fork
      wait(m_in_reset);
      begin
        axi_write_response_item response;

        m_vif.mgr_cb.bready <= 1'b0;
        @(m_vif.mgr_cb);
        // For the time until bvalid is asserted, obey req.m_ready_without_valid_pct and assert
        // bready for some fraction of the total time.
        while (m_vif.mgr_cb.bvalid !== 1'b1) begin
          m_vif.mgr_cb.bready <= $urandom_range(0, 99) < req.m_ready_without_valid_pct;
          @(m_vif.mgr_cb);
        end

        // At this point, bvalid has been asserted. If bready is true, the transfer has gone
        // through. If not, wait req.m_valid_to_ready_delay cycles before we assert ready.
        //
        // Read bready from the clocking block to see the last value we wrote. Practically speaking,
        // mgr_cb.bready will not be true unless we had at least one cycle in the loop above: we set
        // mgr_cb.bready <= 0 at the end of this task and also when a reset is seen in monitor_reset.
        response = axi_write_response_item::type_id::create("response");
        response.m_id   = m_vif.mgr_cb.bid;
        response.m_resp = axi_write_response_item::bresp_e'(m_vif.mgr_cb.bresp);
        response.m_user = m_vif.mgr_cb.buser;

        if (m_vif.bready_internal !== 1'b1) begin
          repeat (req.m_valid_to_ready_delay) @(m_vif.mgr_cb);
          m_vif.mgr_cb.bready <= 1'b1;
          @(m_vif.mgr_cb);
        end

        // Set rsp, which will pass the response back to the sequencer.
        rsp = response;

        // Finally, clear bready (for next cycle).
        m_vif.mgr_cb.bready <= 1'b0;
      end
    join_any
    disable fork;
  end join
endtask
