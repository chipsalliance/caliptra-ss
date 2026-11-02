// SPDX-License-Identifier: Apache-2.0

// Shared packet-memory ownership checks, supplementing native continuous USB
// checking. Reuses the endpoint/RAL byte-lane utilities for bulk and periodic IO.
class usb_packet_buffer_seq extends usb_base_seq;
  `uvm_object_utils(usb_packet_buffer_seq)

  localparam logic [31:0] BUFFER_SENTINEL = 32'heeee_eeee;
  localparam int unsigned PACKET_POINTER_BYTES = 64;
  localparam int unsigned GUARD_BYTES = 64;

  // Construct reusable packet-memory operations through the factory.
  function new(string name = "usb_packet_buffer_seq");
    super.new(name);
  endfunction

  // Integration Guide 4.2.3 p48 rounds packet-pointer advance to 64-byte units.
  function int unsigned packet_allocation_bytes(int unsigned bytes);
    return ((bytes + PACKET_POINTER_BYTES - 1) / PACKET_POINTER_BYTES) * PACKET_POINTER_BYTES;
  endfunction

  // Initialize complete packet allocations and guards; IN writes preserve tails.
  task prepare_packet_buffer(logic [31:0] address, int unsigned capacity, int unsigned bytes, logic [7:0] base, bit in_direction);
    capacity = packet_allocation_bytes(capacity);
    check_buffer_clear_of_endpoint_list("Packet buffer and guards", address - GUARD_BYTES, capacity + 2 * GUARD_BYTES);
    fill_endpoint_buffer(address - GUARD_BYTES, capacity + 2 * GUARD_BYTES, BUFFER_SENTINEL);
    if (in_direction) begin
      for (int unsigned offset = 0; offset < bytes; offset += 4) begin
        logic [31:0] word_value;
        for (int unsigned lane = 0; lane < 4; lane++) word_value[8*lane +: 8] = base + offset + lane;
        write_sram_bytes(USB_DEV0_SRAM, address + offset, word_value, bytes - offset);
      end
    end
  endtask

  // Compare exact payload and guards; IN stays strict. Without a finer tail
  // contract, conservatively omit OUT nonpayload in its final pointer allocation.
  task check_packet_buffer(logic [31:0] address, int unsigned capacity, int unsigned bytes,
                           logic [7:0] base, bit in_direction, string label);
    logic [31:0] observed;
    logic [31:0] expected;
    logic [31:0] compare_mask;
    int unsigned receive_allocation;
    int unsigned unchecked_tail;

    if (bytes > capacity) `uvm_fatal("USB_PACKET_BUFFER", "Payload exceeds packet buffer capacity")
    receive_allocation = packet_allocation_bytes(bytes);
    unchecked_tail = in_direction ? 0 : receive_allocation - bytes;
    capacity = packet_allocation_bytes(capacity);
    `uvm_info("USB_PACKET_BUFFER", $sformatf("%s checking %s payload=%0d allocation=%0d unasserted_OUT_tail=%0d; both guards strict",
      label, in_direction ? "IN" : "OUT", bytes, capacity, unchecked_tail), UVM_LOW)
    for (int offset = -int'(GUARD_BYTES); offset < int'(capacity + GUARD_BYTES); offset += 4) begin
      expected = BUFFER_SENTINEL;
      compare_mask = '1;
      for (int lane = 0; lane < 4; lane++) begin
        if (offset + lane >= 0 && offset + lane < int'(bytes)) expected[8*lane +: 8] = base + offset + lane;
      end
      // Guide 3.1 p10 and 5 p53 define RAM width/selectors, not receive-tail
      // preservation. Do not assume an 8-byte write boundary from bus width.
      if (!in_direction && offset >= 0 && offset < int'(receive_allocation)) begin
        compare_mask = byte_lane_mask(bytes > offset ? bytes - offset : 0);
      end
      if (compare_mask === 32'b0) continue;
      read32(USB_DEV0_SRAM, address + offset, observed);
      if (!((observed & compare_mask) === (expected & compare_mask))) begin
        `uvm_fatal("USB_PACKET_BUFFER", $sformatf("%s byte/guard mismatch at 0x%08h: actual=%08h expected=%08h mask=%08h",
          label, address + offset, observed, expected, compare_mask))
      end
    end
    `uvm_info("USB_PACKET_BUFFER", $sformatf("%s verified payload=%0d preserved_nonpayload=%0d guard_bytes=%0d unasserted_OUT_tail=%0d",
      label, bytes, capacity - bytes - unchecked_tail, 2 * GUARD_BYTES, unchecked_tail), UVM_LOW)
  endtask

  // Poll writeback using one bounded deadline, then compare the entire entry.
  // Integration Guide 4.2.3 pp47-48: address advances by ceil(packet_bytes/64).
  task check_packet_retired(usb_endpoint_cfg endpoint, usb_ep_entry_t armed, int unsigned bytes,
                           time timeout, string label, int unsigned buffer_select = 0);
    usb_ep_entry_t observed;
    usb_ep_entry_t expected;
    realtime deadline;
    realtime next_progress;

    expected = armed;
    expected.active = 1'b0;
    expected.nbytes -= bytes;
    expected.buffer_offset += (bytes + 63) / 64;
    deadline = $realtime + timeout;
    next_progress = $realtime + 500us;
    `uvm_info("USB_PACKET_BUFFER", $sformatf("Waiting for %s buffer=%0d bytes=%0d timeout=%0t",
      label, buffer_select, bytes, timeout), UVM_LOW)
    do begin
      read_endpoint_entry(endpoint, observed, buffer_select);
      if (observed.active === 1'b0) break;
      if ($realtime >= next_progress) begin
        `uvm_info("USB_PACKET_BUFFER", $sformatf("%s awaiting retirement: buffer=%0d observed=%s",
          label, buffer_select, describe_entry(observed)), UVM_LOW)
        next_progress += 500us;
      end
      #500ns;
    end while ($realtime < deadline);
    if (!(observed === expected)) begin
      `uvm_fatal("USB_PACKET_BUFFER", $sformatf("%s writeback mismatch: observed=%s expected=%s",
        label, describe_entry(observed), describe_entry(expected)))
    end
    `uvm_info("USB_PACKET_BUFFER", $sformatf("%s buffer=%0d exact writeback verified", label, buffer_select), UVM_LOW)
  endtask
endclass
