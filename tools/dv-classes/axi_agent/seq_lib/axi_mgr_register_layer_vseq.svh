// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that sits behind an axi_reg_adapter and translates uvm_reg_bus_op items
// into AXI reads and writes.

class axi_mgr_register_layer_vseq extends uvm_sequence;
  `uvm_object_utils(axi_mgr_register_layer_vseq)

  local uvm_sequencer#(axi_reg_op_item) m_layered_sequencer;
  local write_request_sequencer_t       m_aw_sequencer;
  local write_data_sequencer_t          m_w_sequencer;
  local write_response_sequencer_t      m_b_sequencer;
  local read_request_sequencer_t        m_ar_sequencer;
  local read_data_sequencer_t           m_r_sequencer;

  local axi_response_router m_read_response_router;
  local axi_response_router m_write_response_router;
  local axi_agent_cfg       m_cfg;

  extern function new(string name="");
  extern task body();

  extern function void set_sequencers(uvm_sequencer#(axi_reg_op_item) layered_sequencer,
                                      write_request_sequencer_t       aw_sequencer,
                                      write_data_sequencer_t          w_sequencer,
                                      write_response_sequencer_t      b_sequencer,
                                      read_request_sequencer_t        ar_sequencer,
                                      read_data_sequencer_t           r_sequencer);

  extern function void set_response_routers(axi_response_router read_response_router,
                                            axi_response_router write_response_router);

  extern function void set_cfg(axi_agent_cfg cfg);

  // Send the request item through a layered sequence, passing any information back by modifying the
  // item argument (specifically, by modifying its m_rw field).
  extern local task send_op_item(axi_reg_op_item item);
endclass

function axi_mgr_register_layer_vseq::new(string name="");
  super.new(name);
endfunction

function void axi_mgr_register_layer_vseq::set_cfg(axi_agent_cfg cfg);
  m_cfg = cfg;
endfunction

task axi_mgr_register_layer_vseq::body();
  if (m_layered_sequencer == null ||
      m_aw_sequencer == null ||
      m_w_sequencer == null ||
      m_b_sequencer == null ||
      m_ar_sequencer == null ||
      m_r_sequencer == null ||
      m_read_response_router == null ||
      m_write_response_router == null) begin
    `uvm_fatal(get_full_name(),
               "Cannot run sequence because at least one sequencer or router is null.")
  end

  fork : isolation_fork begin
    forever begin
      axi_reg_op_item item;
      m_layered_sequencer.get(item);

      fork begin
        send_op_item(item);
        m_layered_sequencer.put(item);
      end join_none
    end
  end join
endtask

function void
  axi_mgr_register_layer_vseq::set_sequencers(uvm_sequencer#(axi_reg_op_item) layered_sequencer,
                                              write_request_sequencer_t       aw_sequencer,
                                              write_data_sequencer_t          w_sequencer,
                                              write_response_sequencer_t      b_sequencer,
                                              read_request_sequencer_t        ar_sequencer,
                                              read_data_sequencer_t           r_sequencer);
  if (layered_sequencer == null) `uvm_fatal(get_full_name(), "No layered sequencer")
  if (aw_sequencer == null) `uvm_fatal(get_full_name(), "No aw sequencer")
  if (w_sequencer == null)  `uvm_fatal(get_full_name(), "No w sequencer")
  if (b_sequencer == null)  `uvm_fatal(get_full_name(), "No b sequencer")
  if (ar_sequencer == null) `uvm_fatal(get_full_name(), "No ar sequencer")
  if (r_sequencer == null)  `uvm_fatal(get_full_name(), "No r sequencer")

  m_layered_sequencer = layered_sequencer;
  m_aw_sequencer      = aw_sequencer;
  m_w_sequencer       = w_sequencer;
  m_b_sequencer       = b_sequencer;
  m_ar_sequencer      = ar_sequencer;
  m_r_sequencer       = r_sequencer;
endfunction

function void
  axi_mgr_register_layer_vseq::set_response_routers(axi_response_router read_response_router,
                                                    axi_response_router write_response_router);
  if (read_response_router == null)  `uvm_fatal(get_full_name(), "No read response router.")
  if (write_response_router == null) `uvm_fatal(get_full_name(), "No write response router.")

  m_read_response_router  = read_response_router;
  m_write_response_router = write_response_router;
endfunction

task axi_mgr_register_layer_vseq::send_op_item(axi_reg_op_item item);
  int unsigned axsize;
  int unsigned bus_byte_width;
  int unsigned byte_offset;
  int unsigned id_width;
  bit          en_user_strb;
  bit [127:0]  strb_from_size;
  bit [127:0]  unshifted_strb;
  bit [127:0]  byte_mask;

  axsize = $clog2((item.m_rw.n_bits + 7) / 8);

  if (axsize > 7) begin
    `uvm_error(get_full_name(),
               $sformatf({"Cannot generate a sequence to represent an access with n_bits = %d: ",
                          "for a single transfer, this would need an AxSIZE of %0d."},
                         item.m_rw.n_bits, axsize))
    item.m_rw.status = UVM_NOT_OK;
    return;
  end

  // Determine interface bus byte width, ID width limit, and user strobe policy from m_cfg
  bus_byte_width = 4;
  id_width       = 8;
  en_user_strb   = 1'b1;
  if (m_cfg != null) begin
    id_width     = m_cfg.reg_layer_id_width;
    en_user_strb = m_cfg.en_caliptra_user_strb;
    if (item.m_rw.kind == UVM_READ && m_cfg.read_data_vif != null) begin
      bus_byte_width = (m_cfg.read_data_vif.data_width + 7) / 8;
      if (m_cfg.read_request_vif != null && m_cfg.read_request_vif.id_r_width < id_width) begin
        id_width = m_cfg.read_request_vif.id_r_width;
      end
    end else if (item.m_rw.kind == UVM_WRITE && m_cfg.write_data_vif != null) begin
      bus_byte_width = (m_cfg.write_data_vif.data_width + 7) / 8;
      if (m_cfg.write_request_vif != null && m_cfg.write_request_vif.id_w_width < id_width) begin
        id_width = m_cfg.write_request_vif.id_w_width;
      end
    end
  end

  // Compute unshifted strobe from access size and optional UVM RAL byte_en mask
  strb_from_size = (128'd1 << (1 << axsize)) - 1;
  unshifted_strb = (item.m_rw.byte_en != '0) ? (strb_from_size & 128'(item.m_rw.byte_en)) : strb_from_size;

  // Compute AXI byte-lane offset for narrow/unaligned transfers on the bus
  byte_offset = int'(item.m_rw.addr) & (bus_byte_width - 1);
  byte_mask   = unshifted_strb << byte_offset;

  case (item.m_rw.kind)
    UVM_READ: begin
      axi_mgr_read_fixed_vseq read_vseq = axi_mgr_read_fixed_vseq::type_id::create("read_vseq");
      bit          ar_complete, r_complete;
      bit [1023:0] bit_mask;

      read_vseq.set_sequencers(m_ar_sequencer, m_r_sequencer);
      read_vseq.set_read_response_router(m_read_response_router);

      if (!read_vseq.randomize() with {
            m_fixed_req.m_addr == local::item.m_rw.addr;
            m_fixed_req.m_size == local::axsize;
            (local::id_width < 32) -> (m_fixed_req.m_id < (32'd1 << local::id_width));
            local::en_user_strb -> (m_fixed_req.m_user[21:18] == local::byte_mask[3:0]);
          }) begin
        `uvm_fatal(get_full_name(), "Failed to randomise read_vseq.")
      end

      read_vseq.start(null);

      // Convert byte_mask into a bit mask that can be used with rdata
      bit_mask = '0;
      for (int unsigned i = 0; i < 128; i++) begin
        if (byte_mask[i]) bit_mask |= 1024'hff << (8 * i);
      end

      ar_complete = (read_vseq.rsp.m_ar_status != null &&
                     read_vseq.rsp.m_ar_status.m_sending_complete);
      r_complete = (read_vseq.rsp.m_read_data != null);

      item.m_rw.status = (ar_complete && r_complete &&
                          read_vseq.rsp.m_read_data.m_resp inside {axi_read_data_item::RRespOkay, axi_read_data_item::RRespExOkay}) ?
                         UVM_IS_OK :
                         UVM_NOT_OK;
      item.m_rw.data   = r_complete ? ((read_vseq.rsp.m_read_data.m_data & bit_mask) >> (8 * byte_offset)) : 0;
    end

    UVM_WRITE: begin
      axi_mgr_write_fixed_vseq write_vseq = axi_mgr_write_fixed_vseq::type_id::create("write_vseq");
      bit          aw_complete, w_complete, b_complete;
      bit [1023:0] shifted_data;

      shifted_data = 1024'(item.m_rw.data) << (8 * byte_offset);

      write_vseq.set_sequencers(m_aw_sequencer, m_w_sequencer, m_b_sequencer);
      write_vseq.set_write_response_router(m_write_response_router);

      if (!write_vseq.randomize() with {
            m_fixed_req.m_addr == local::item.m_rw.addr;
            m_fixed_req.m_size == local::axsize;
            (local::id_width < 32) -> (m_fixed_req.m_id < (32'd1 << local::id_width));

            m_fixed_req.m_write_data_item.m_data == local::shifted_data;
            m_fixed_req.m_write_data_item.m_strb == local::byte_mask;
            m_fixed_req.m_write_data_item.m_last == 1'b1;
            m_fixed_req.m_write_data_item.m_user == 512'h0;
            local::en_user_strb -> (m_fixed_req.m_user[21:18] == local::byte_mask[3:0]);
          }) begin
        `uvm_fatal(get_full_name(), "Failed to randomise write_vseq.")
      end

      write_vseq.start(null);

      aw_complete = (write_vseq.rsp.m_aw_status != null &&
                     write_vseq.rsp.m_aw_status.m_sending_complete);
      w_complete = (write_vseq.rsp.m_w_status != null &&
                    write_vseq.rsp.m_w_status.m_sending_complete);
      b_complete = (write_vseq.rsp.m_write_response != null);

      item.m_rw.status = (aw_complete && w_complete && b_complete &&
                          write_vseq.rsp.m_write_response.m_resp inside {axi_write_response_item::BRespOkay, axi_write_response_item::BRespExOkay}) ?
                         UVM_IS_OK :
                         UVM_NOT_OK;
    end

    default: begin
      `uvm_error(get_full_name(),
                 $sformatf("Cannot send this uvm_reg_op. kind is %0s, which is not supported.",
                           item.m_rw.kind.name()))
      item.m_rw.status = UVM_NOT_OK;
      return;
    end
  endcase
endtask
