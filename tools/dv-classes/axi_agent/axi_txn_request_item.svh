// Copyright lowRISC contributors
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents a message sent by an AXI Manager to request a transaction (using
// either the AR or AW channel)

class axi_txn_request_item extends uvm_sequence_item;
  `uvm_object_utils(axi_txn_request_item)

  // Transaction identifier for the read or write channel
  //
  // This is sent over the AxID signal, whose width is configurable, based on the ID_x_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bit [31:0] m_id;

  // Transaction address
  //
  // This is sent over the AxADDR signal, whose width is configurable, based on the ADDR_WIDTH
  // property. The representation in the item uses a max footprint approach but the driver will fail
  // with an error if bits above the top of the signal are nonzero.
  rand bit [63:0] m_addr;

  // Region identifier
  rand bit [3:0]  m_region;

  // Number of data transfers in the transaction
  rand bit [7:0]  m_len;

  // Maximum number of bytes in each data transfer (encoded as log2(byte_size))
  rand bit [2:0]  m_size;

  // Burst attribute (FIXED, INCR or WRAP)
  rand burst_e    m_burst;

  // Request exclusive access
  rand bit        m_lock;

  // Memory attributes (applying to caches in the system)
  rand bit [3:0]  m_cache;

  // Memory access attributes
  rand bit [2:0]  m_prot;

  // Traffic stream QoS identifier
  rand bit [3:0]  m_qos;

  // Extra user bits
  //
  // This is sent over the ARUSER or AWUSER signal, whose widths are configurable, based on the
  // USER_REQ_WIDTH property. The representation in the item uses a max footprint approach but the
  // driver will fail with an error if bits above the top of the signal are nonzero.
  rand bit [127:0] m_user;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // If m_burst is BurstFixed, the AXI spec allows up to 16 transfers (so m_len <= 15). If it is
  // BurstWrap, the AXI spec requires the number of transfers to be 2, 4, 8 or 16.
  //
  // This constraint comes from AMBA AXI protocol specification, issue J, section A4.1.2.
  extern constraint burst_length_c;

  // A transaction may not cross a 4kb boundary
  //
  // This constraint comes from AMBA AXI protocol specification, issue J, section A4.1.2.
  extern constraint no_4kb_boundary_crossing_c;

  // If m_burst is BurstWrap, m_addr must be aligned to the size of each transfer.
  //
  // This constraint comes from AMBA AXI protocol specification, issue J, section A4.1.4.
  extern constraint wrap_alignment_c;
endclass

function axi_txn_request_item::new(string name = "");
  super.new(name);
endfunction

function void axi_txn_request_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_id", m_id, 32, UVM_HEX);
  printer.print_field("m_addr", m_addr, 64, UVM_HEX);
  printer.print_field_int("m_region", m_region, 4, UVM_HEX);
  printer.print_field_int("m_len", m_len, 8, UVM_DEC);
  printer.print_field_int("m_size", m_size, 3, UVM_DEC);
  printer.print_string("m_burst", m_burst.name());
  printer.print_field_int("m_lock", m_lock, 1, UVM_BIN);
  printer.print_field_int("m_cache", m_cache, 4, UVM_BIN);
  printer.print_field_int("m_prot", m_prot, 3, UVM_BIN);
  printer.print_field_int("m_qos", m_qos, 4, UVM_HEX);
  printer.print_field("m_user", m_user, 128, UVM_HEX);
endfunction

function void axi_txn_request_item::do_copy(uvm_object rhs);
  axi_txn_request_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_id     = rhs_.m_id;
  this.m_addr   = rhs_.m_addr;
  this.m_region = rhs_.m_region;
  this.m_len    = rhs_.m_len;
  this.m_size   = rhs_.m_size;
  this.m_burst  = rhs_.m_burst;
  this.m_lock   = rhs_.m_lock;
  this.m_cache  = rhs_.m_cache;
  this.m_prot   = rhs_.m_prot;
  this.m_qos    = rhs_.m_qos;
  this.m_user   = rhs_.m_user;
endfunction

function bit axi_txn_request_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  axi_txn_request_item rhs_;

  // These items are only equivalent if rhs is actually an axi_txn_request_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not an axi_txn_request_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_id", m_id, rhs_.m_id, 32, UVM_HEX) &
          comparer.compare_field("m_addr", m_addr, rhs_.m_addr, 64, UVM_HEX) &
          comparer.compare_field_int("m_region", m_region, rhs_.m_region, 4, UVM_HEX) &
          comparer.compare_field_int("m_len", m_len, rhs_.m_len, 8, UVM_DEC) &
          comparer.compare_field_int("m_size", m_size, rhs_.m_size, 3, UVM_DEC) &
          comparer.compare_field_int("m_burst", m_burst, rhs_.m_burst, 2, UVM_BIN) &
          comparer.compare_field_int("m_lock", m_lock, rhs_.m_lock, 1, UVM_BIN) &
          comparer.compare_field_int("m_cache", m_cache, rhs_.m_cache, 4, UVM_BIN) &
          comparer.compare_field_int("m_prot", m_prot, rhs_.m_prot, 3, UVM_BIN) &
          comparer.compare_field_int("m_qos", m_qos, rhs_.m_qos, 4, UVM_HEX) &
          comparer.compare_field("m_user", m_user, rhs_.m_user, 128, UVM_HEX));
endfunction

constraint axi_txn_request_item::burst_length_c {
  (m_burst == BurstFixed) -> (m_len <= 15);
  (m_burst == BurstWrap) -> (m_len inside {1, 3, 7, 15});
}

constraint axi_txn_request_item::no_4kb_boundary_crossing_c {
  // An incrementing burst steps forward for each of the (m_len + 1) transfers.
  //
  // The first such transfer starts at Aligned_Addr, which is defined in A4.1.6 of the specification
  // to be m_addr after rounding down to a multiple of 1 << m_size. Shifting right by m_size gives
  // the address in those units, rounding down. Add m_len + 1 to get the first address after the
  // burst, in the same units. Finally, shift left again by m_size and subtract one to get the
  // address of the final byte touched by the transfer.
  //
  // To check that this doesn't cross a 4kb boundary, compare that value with m_addr, after shifting
  // right by 12.
  (m_burst == BurstIncr) ->
    (((((m_addr >> m_size) + m_len + 1) << m_size) - 1) >> 12) == (m_addr >> 12);

  // There is no constraint needed for fixed bursts. Such a transaction will access the same set of
  // 1 << m_size bytes repeatedly, starting at Aligned_Addr (as defined above). Because m_size is
  // less than 12, the transfers will never cross a 4kb boundary.

  // There is also no constraint needed for wrapping bursts. The wrap region always has a length
  // that is a power of two and less than 2048. As such, it cannot cross 4kb boundaries.
}

constraint axi_txn_request_item::wrap_alignment_c {
  // The size of each transfer is (1 << m_size). m_addr is divisible by that value if its bottom
  // m_size bits are zero.
  (m_burst == BurstWrap) -> (m_addr & ((1 << m_size) - 1)) == '0;
}
