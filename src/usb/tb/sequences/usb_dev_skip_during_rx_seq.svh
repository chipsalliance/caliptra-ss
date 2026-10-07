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

// Sets EPSKIP during an observed OUT data packet and verifies delayed service.
class usb_dev_skip_during_rx_seq extends usb_dev_skip_seq;
  `uvm_object_utils(usb_dev_skip_during_rx_seq)

  logic [31:0] inflight_buffer_offset = 32'h0000_0200;
  int unsigned inflight_armed_bytes = 1024;
  int unsigned inflight_payload_bytes = 512;
  logic [7:0] inflight_payload_base = 8'h40;
  logic [31:0] inflight_sentinel = 32'hcaca_caca;

  function new(string name = "usb_dev_skip_during_rx_seq");
    super.new(name);
    skip_buffer_offset = 32'h0000_0800;
  endfunction

  // Compare the packet committed before the delayed skip writeback.
  task verify_inflight_packet();
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(skip_endpoint, observed_entry);
    if (observed_entry.active !== 1'b0 ||
        observed_entry.nbytes !== inflight_armed_bytes - inflight_payload_bytes ||
        entry_buffer_byte_offset(observed_entry) !== inflight_buffer_offset + inflight_payload_bytes) begin
      `uvm_fatal(
        "USB_SKIP_RX_SEQ",
        $sformatf(
          "Delayed skip writeback is invalid: observed %s, expected active=0 nbytes=%0d buffer=0x%03h",
          describe_entry(observed_entry),
          inflight_armed_bytes - inflight_payload_bytes,
          inflight_buffer_offset + inflight_payload_bytes
        )
      )
    end

    for (int unsigned offset = 0; offset < inflight_payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = inflight_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, inflight_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_SKIP_RX_SEQ",
          $sformatf(
            "In-flight payload mismatch at offset 0x%03h: data=0x%08h expected=0x%08h",
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
    `uvm_info("USB_SKIP_RX_SEQ", $sformatf("Delayed skip preserved and committed all %0d in-flight bytes", inflight_payload_bytes), UVM_LOW)
  endtask

  // Enumerate, overlap EPSKIP with an OUT token, then prove endpoint recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq inflight_host_sequence;
    usb_dev_skip_host_seq recovery_host_sequence;
    usb_ep_entry_t initial_entry;
    uvm_event data_packet_event;

    completed = 1'b0;
    `uvm_info("USB_SKIP_RX_SEQ", "Starting endpoint skip-during-receive scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_SKIP_RX_SEQ", "Enumeration did not complete")
    end

    skip_endpoint = get_endpoint(skip_target_ep_number, skip_target_direction);
    check_buffer_clear_of_endpoint_list("In-flight transfer", inflight_buffer_offset, inflight_armed_bytes);
    check_buffer_clear_of_endpoint_list("Recovery transfer", skip_buffer_offset, recovery_bytes);
    enable_endpoint_interrupt(skip_endpoint);
    clear_endpoint_interrupt(skip_endpoint);
    fill_endpoint_buffer(inflight_buffer_offset, inflight_armed_bytes, inflight_sentinel);
    arm_endpoint(skip_endpoint, inflight_armed_bytes, inflight_buffer_offset, initial_entry);

    inflight_host_sequence = usb_bulk_out_host_seq::type_id::create("inflight_host_sequence");
    inflight_host_sequence.target_endpoint = skip_endpoint;
    inflight_host_sequence.payload_byte_count = inflight_payload_bytes;
    inflight_host_sequence.payload_base = inflight_payload_base;
    inflight_host_sequence.device_address = p_sequencer.cfg.device_address;
    inflight_host_sequence.transfer_label = "In-flight bulk OUT";

    data_packet_event = uvm_event_pool::get_global(USB_UTMI_DATA_PACKET_EVENT);
    data_packet_event.reset();
    `uvm_info("USB_SKIP_RX_SEQ", "Armed DATA-packet observation; starting the bulk transfer", UVM_LOW)
    fork
      begin
        inflight_host_sequence.start(p_sequencer.host_sequencer);
        if (!inflight_host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_RX_SEQ", "In-flight host sequence returned incomplete")
        end
      end
      begin
        data_packet_event.wait_ptrigger();
        `uvm_info("USB_SKIP_RX_SEQ", "Observed the target DATA packet; writing EPSKIP while payload reception is active", UVM_LOW)
        request_endpoint_skip(skip_endpoint);
        wait_for_endpoint_skip_clear(skip_endpoint, skip_clear_timeout, skip_clear_poll_interval);
      end
    join

    wait_for_endpoint_interrupt(skip_endpoint, recovery_timeout, recovery_poll_interval);
    verify_inflight_packet();

    arm_recovery_transfer();
    recovery_host_sequence = usb_dev_skip_host_seq::type_id::create("recovery_host_sequence");
    recovery_host_sequence.target_endpoint = skip_endpoint;
    recovery_host_sequence.payload_byte_count = recovery_bytes;
    recovery_host_sequence.payload_base = recovery_payload_base;
    recovery_host_sequence.device_address = p_sequencer.cfg.device_address;
    fork
      begin
        recovery_host_sequence.start(p_sequencer.host_sequencer);
        if (!recovery_host_sequence.completed) begin
          `uvm_fatal("USB_SKIP_RX_SEQ", "Recovery host sequence returned incomplete")
        end
      end
      begin
        wait_for_endpoint_interrupt(skip_endpoint, recovery_timeout, recovery_poll_interval);
      end
    join
    verify_recovery_transfer();

    completed = 1'b1;
    `uvm_info("USB_SKIP_RX_SEQ", "Endpoint skip-during-receive scenario completed with delayed service and recovery verified", UVM_LOW)
  endtask
endclass
