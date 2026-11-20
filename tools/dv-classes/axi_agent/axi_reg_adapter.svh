// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Per-transaction byte-enable extension attached to uvm_reg_item::extension so concurrent
// frontdoor RAL accesses and multi-agent testbenches propagate explicit strobes without
// static globals or IP-specific register names.
class axi_reg_byte_en_ext extends uvm_object;
  `uvm_object_utils(axi_reg_byte_en_ext)

  bit [`UVM_REG_BYTENABLE_WIDTH-1:0] byte_en          = 'hF;
  bit                                override_byte_en = 1'b1;
  int unsigned                       n_bits           = `UVM_REG_DATA_WIDTH;
  bit                                override_n_bits  = 1'b0;

  function new(string name = "axi_reg_byte_en_ext");
    super.new(name);
  endfunction
endclass

// An extremely simple uvm_reg_adapter that wraps a uvm_reg_op in an axi_reg_op_item or copies the
// response fields back from that item.

class axi_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(axi_reg_adapter)

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
  axi_reg_op_item     bus_item = axi_reg_op_item::type_id::create("bus_item");
  uvm_reg_item        item     = get_item();
  axi_reg_byte_en_ext ext;
  axi_reg_op_item     ext_op_item;
  uvm_reg             reg_h;
  uvm_reg_field       fld_h;

  // Take a copy of the uvm_reg_bus_op (which will be a deep copy because uvm_reg_bus_op is a
  // struct)
  bus_item.m_rw               = rw;
  bus_item.m_override_byte_en = 1'b0;
  bus_item.m_reg_n_bytes      = 0;

  // Record parent register byte width so single-field writes to upper bytes of a 32-bit CSR
  // retain their byte_en lanes while default all-ones byte_en stays bounded to the CSR width.
  if (item != null && item.element != null) begin
    if ($cast(reg_h, item.element)) begin
      bus_item.m_reg_n_bytes = reg_h.get_n_bytes();
    end else if ($cast(fld_h, item.element) && fld_h.get_parent() != null) begin
      bus_item.m_reg_n_bytes = fld_h.get_parent().get_n_bytes();
    end
  end

  if (item == null) begin
    // Direct adapter.reg2bus(rw) invocation without a uvm_reg_item wrapper: treat non-all-ones
    // byte_en masks as explicit caller overrides while keeping default '1 bounded by n_bits.
    bus_item.m_override_byte_en = (rw.byte_en != '1);
  end else if (item.extension != null && $cast(ext, item.extension)) begin
    if (ext.override_byte_en) begin
      bus_item.m_rw.byte_en       = ext.byte_en;
      bus_item.m_override_byte_en = 1'b1;
    end
    if (ext.override_n_bits) begin
      bus_item.m_rw.n_bits = ext.n_bits;
    end
  end else if (item.extension != null && $cast(ext_op_item, item.extension)) begin
    bus_item.m_rw.byte_en       = ext_op_item.m_rw.byte_en;
    bus_item.m_override_byte_en = 1'b1;
  end else if (item.extension == null && rw.kind == UVM_WRITE) begin
    ext                  = axi_reg_byte_en_ext::type_id::create("ext");
    ext.byte_en          = bus_item.m_rw.byte_en;
    ext.override_byte_en = 1'b0;
    ext.n_bits           = bus_item.m_rw.n_bits;
    item.extension       = ext;
  end

  return bus_item;
endfunction

function void axi_reg_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
  axi_reg_op_item local_bus_item;
  if (!$cast(local_bus_item, bus_item)) begin
    `uvm_fatal(get_full_name(), "bus_item is not of type axi_reg_op_item")
  end
  // Replace all the fields in rw that bus2reg would normally populate (kind, addr, data and status)
  rw.kind    = local_bus_item.m_rw.kind;
  rw.addr    = local_bus_item.m_rw.addr;
  rw.data    = local_bus_item.m_rw.data;
  rw.byte_en = local_bus_item.m_rw.byte_en;
  rw.status  = local_bus_item.m_rw.status;
endfunction
