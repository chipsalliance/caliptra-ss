// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An extremely simple uvm_reg_adapter that wraps a uvm_reg_op in an axi_reg_op_item or copies the
// response fields back from that item.

class axi_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(axi_reg_adapter)

  extern function new(string name="");
  extern function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
  extern function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op op);
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
  axi_reg_op_item ext_item;

  // Take a copy of the uvm_reg_bus_op (which will be a deep copy because uvm_reg_bus_op is a
  // struct)
  bus_item.m_rw = rw;

  // Allow sequences to override byte_en via uvm_reg_item::extension (e.g. for sub-word FIFO writes
  // or sub-word CSR write error tests).
  if (reg_item != null && reg_item.extension != null && $cast(ext_item, reg_item.extension)) begin
    bus_item.m_rw.byte_en = ext_item.m_rw.byte_en;
  end

  return bus_item;
endfunction

function void axi_reg_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op op);
  axi_reg_op_item local_bus_item;
  if (!$cast(local_bus_item, bus_item)) begin
    `uvm_fatal(get_full_name(), "bus_item is not of type axi_reg_op_item")
  end
  // Replace all the fields in op that bus2reg would normally populate (kind, addr, data, byte_en and status)
  op.kind    = local_bus_item.m_rw.kind;
  op.addr    = local_bus_item.m_rw.addr;
  op.data    = local_bus_item.m_rw.data;
  op.byte_en = local_bus_item.m_rw.byte_en;
  op.status  = local_bus_item.m_rw.status;
endfunction
