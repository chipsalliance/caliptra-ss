// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Forces high-speed bulk OUT flow control through NAK and PING before ACK.
class usb_bulk_ping_seq extends usb_base_seq;
  `uvm_object_utils(usb_bulk_ping_seq)

  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 64;
  logic [7:0] payload_base = 8'h50;
  time ping_timeout = 500us;
  bit completed;

  function new(string name = "usb_bulk_ping_seq");
    super.new(name);
  endfunction

  // Check endpoint retirement and all received bytes.
  task verify_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_BULK_PING", $sformatf("Bulk OUT did not retire after PING flow control: %s", describe_entry(entry)))
    end
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_BULK_PING",
          $sformatf("Bulk OUT payload mismatch at offset %0d: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
  endtask

  // Enumerate, force a PING retry, then complete and verify the transfer.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t inactive_entry;
    usb_ep_entry_t active_entry;
    bit ping_seen;
    int unsigned ping_count;
    int unsigned nak_count;

    completed = 1'b0;
    `uvm_info("USB_BULK_PING", "Starting bulk OUT PING flow-control scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BULK_PING", "Enumeration did not complete")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list("Bulk PING", buffer_offset, payload_bytes);
    fill_endpoint_buffer(buffer_offset, payload_bytes, 32'heeee_eeee);
    inactive_entry = endpoint_entry(1'b0, 1'b0, payload_bytes, buffer_offset);
    write_endpoint_entry(endpoint, inactive_entry);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);

    host_sequence = usb_bulk_out_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = ping_timeout;
    host_sequence.transfer_label = "Bulk OUT after PING";

    p_sequencer.packet_monitor.start_window("Bulk OUT NAK/PING/ACK");
    `uvm_info("USB_BULK_PING", "EP1 OUT is inactive; starting bulk OUT and waiting for host PING", UVM_LOW)
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_BULK_PING", "Bulk OUT host sequence returned incomplete")
        end
      end
      begin
        p_sequencer.packet_monitor.wait_for_ping(ping_timeout, ping_seen);
        if (!ping_seen) begin
          `uvm_fatal("USB_BULK_PING", $sformatf("No host PING was observed within %0t", ping_timeout))
        end
        `uvm_info("USB_BULK_PING", "Observed host PING after endpoint NAK; arming EP1 OUT", UVM_LOW)
        arm_endpoint(endpoint, payload_bytes, buffer_offset, active_entry);
      end
    join
    p_sequencer.packet_monitor.stop_window();

    ping_count = p_sequencer.packet_monitor.count_pid(
      svt_usb_packet::PING,
      usb_packet_monitor_callback::USB_PACKET_TX
    );
    nak_count = p_sequencer.packet_monitor.count_pid(
      svt_usb_packet::NAK,
      usb_packet_monitor_callback::USB_PACKET_RX
    );
    if (ping_count == 0 || nak_count == 0) begin
      `uvm_fatal("USB_BULK_PING", $sformatf("Incomplete flow-control evidence: PING=%0d NAK=%0d", ping_count, nak_count))
    end
    wait_for_endpoint_interrupt(endpoint, ping_timeout);
    verify_transfer(endpoint);

    completed = 1'b1;
    `uvm_info(
      "USB_BULK_PING",
      $sformatf("Bulk OUT PING flow control verified: host PING=%0d device NAK=%0d payload_bytes=%0d", ping_count, nak_count, payload_bytes),
      UVM_LOW
    )
  endtask
endclass
