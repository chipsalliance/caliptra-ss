// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An extremely simple uvm_reg_adapter that wraps a uvm_reg_op in an axi_reg_op_item or copies the
// response fields back from that item.

class axi_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(axi_reg_adapter)

  static bit        m_use_next_byte_en    = 1'b0;
  static bit [31:0] m_subword_target_addr = 32'h0000_001c;
  static bit [3:0]  m_next_byte_en        = 4'b0001;
  static bit [3:0]  m_last_byte_en        = 4'b1111;
  static uvm_reg    m_next_byte_en_reg    = null;

  extern function new(string name="");
  extern function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
  extern function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
endclass

function axi_reg_adapter::new(string name="");
  super.new(name);
  supports_byte_enable = 1;

  // Setting this to true means that the "bus driver" (here, axi_mgr_register_layer_vseq) sends a
  // response to the sequencer.
  provides_responses   = 1;
endfunction

function uvm_sequence_item axi_reg_adapter::reg2bus(const ref uvm_reg_bus_op rw);
  axi_reg_op_item bus_item = axi_reg_op_item::type_id::create("bus_item");
  uvm_reg_item    reg_item = get_item();
  uvm_reg         cur_reg  = (reg_item != null && $cast(cur_reg, reg_item.element)) ? cur_reg : null;
  axi_reg_op_item ext_item;
  bit             is_target_reg = 1'b0;

  // Take a copy of the uvm_reg_bus_op (which will be a deep copy because uvm_reg_bus_op is a
  // struct)
  bus_item.m_rw = rw;

  if (m_next_byte_en_reg != null) begin
    is_target_reg = (cur_reg == m_next_byte_en_reg) ||
                    (rw.addr == m_next_byte_en_reg.get_address());
  end else if (cur_reg != null) begin
    is_target_reg = (cur_reg.get_name() inside {"wdata", "txdata"}) ||
                    (rw.addr == m_subword_target_addr);
  end else begin
    is_target_reg = (rw.addr == m_subword_target_addr);
  end

  // Allow sequences to override byte_en per-access via uvm_reg_item::extension (concurrency-safe)
  // or via static m_use_next_byte_en / m_next_byte_en_reg (compatible with uart & spi_host DV).
  if (reg_item != null && reg_item.extension != null && $cast(ext_item, reg_item.extension)) begin
    bus_item.m_rw.byte_en = ext_item.m_rw.byte_en;
    if (rw.kind == UVM_WRITE && is_target_reg) begin
      m_last_byte_en = ext_item.m_rw.byte_en[3:0];
    end
  end else if (rw.kind == UVM_WRITE && is_target_reg) begin
    if (m_use_next_byte_en) begin
      bus_item.m_rw.byte_en = m_next_byte_en;
      m_last_byte_en        = m_next_byte_en;
      m_use_next_byte_en    = 1'b0;
      m_next_byte_en_reg    = null;
    end else begin
      m_last_byte_en        = bus_item.m_rw.byte_en[3:0];
    end
  end

  return bus_item;
endfunction

function void axi_reg_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
  axi_reg_op_item local_bus_item;
  if (!$cast(local_bus_item, bus_item)) begin
    `uvm_fatal(get_full_name(), "bus_item is not of type axi_reg_op_item")
  end
  // Replace all the fields in rw that bus2reg would normally populate (kind, addr, data and status)
  rw.kind = local_bus_item.m_rw.kind;
  rw.addr = local_bus_item.m_rw.addr;
  rw.data = local_bus_item.m_rw.data;
  rw.byte_en = local_bus_item.m_rw.byte_en;
  rw.status = local_bus_item.m_rw.status;
endfunction
