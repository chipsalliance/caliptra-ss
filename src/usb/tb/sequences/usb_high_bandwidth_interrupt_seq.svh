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

// Exchanges three 1024-byte interrupt transactions in each direction.
class usb_high_bandwidth_interrupt_seq extends usb_base_seq;
  `uvm_object_utils(usb_high_bandwidth_interrupt_seq)

  int unsigned transaction_bytes = 1024;
  int unsigned transaction_count = 3;
  logic [31:0] out_buffer = 32'h0000_1000;
  logic [31:0] in_buffer = 32'h0000_2000;
  logic [7:0] out_payload_base = 8'h11;
  logic [7:0] in_payload_base = 8'h91;
  time transfer_timeout = 750us;
  bit completed;

  function new(string name = "usb_high_bandwidth_interrupt_seq");
    super.new(name);
  endfunction

  // Fill packet memory with packet-distinct IN data.
  task fill_in_payload();
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < transaction_count * transaction_bytes; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = in_payload_base + offset + lane + (offset / transaction_bytes);
      end
      write32(USB_DEV0_SRAM, in_buffer + offset, data_word);
    end
  endtask

  // Check the endpoint writeback after one transaction.
  task check_progress(
    usb_endpoint_cfg endpoint,
    int unsigned completed_transactions,
    logic [31:0] initial_buffer,
    string label
  );
    usb_ep_entry_t entry;
    int unsigned remaining_bytes;

    remaining_bytes = (transaction_count - completed_transactions) * transaction_bytes;
    read_endpoint_entry(endpoint, entry);
    if (entry.active !== (remaining_bytes != 0) ||
        entry.nbytes !== remaining_bytes ||
        entry_buffer_byte_offset(entry) !== initial_buffer + completed_transactions * transaction_bytes) begin
      `uvm_fatal(
        "USB_HB_INTERRUPT",
        $sformatf(
          "%s progress mismatch after %0d/%0d transactions: observed %s expected active=%0b nbytes=%0d buffer=0x%04h",
          label,
          completed_transactions,
          transaction_count,
          describe_entry(entry),
          remaining_bytes != 0,
          remaining_bytes,
          initial_buffer + completed_transactions * transaction_bytes
        )
      )
    end
    `uvm_info(
      "USB_HB_INTERRUPT",
      $sformatf("%s progress verified after %0d/%0d transactions: %s", label, completed_transactions, transaction_count, describe_entry(entry)),
      UVM_LOW
    )
  endtask

  // Compare one OUT packet at its packet-memory offset.
  task verify_out_transaction(int unsigned transaction_index);
    logic [31:0] observed_word;
    logic [31:0] expected_word;
    int unsigned stream_base;

    stream_base = transaction_index * transaction_bytes;
    for (int unsigned offset = 0; offset < transaction_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = out_payload_base + stream_base + offset + lane + transaction_index;
      end
      read32(USB_DEV0_SRAM, out_buffer + stream_base + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_HB_INTERRUPT",
          $sformatf(
            "Interrupt OUT transaction %0d mismatch at byte %0d: data=0x%08h expected=0x%08h",
            transaction_index,
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
  endtask

  // Enumerate and exercise high-bandwidth interrupt OUT and IN.
  virtual task body();
    usb_init_seq init_sequence;
    usb_interrupt_host_seq host_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t entry;
    int unsigned total_bytes;

    completed = 1'b0;
    total_bytes = transaction_count * transaction_bytes;
    `uvm_info("USB_HB_INTERRUPT", "Starting high-bandwidth interrupt scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_HB_INTERRUPT", "Enumeration did not complete")
    end

    out_endpoint = get_endpoint(2, USB_DIRECTION_OUT);
    in_endpoint = get_endpoint(2, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list("High-bandwidth interrupt OUT", out_buffer, total_bytes);
    check_buffer_clear_of_endpoint_list("High-bandwidth interrupt IN", in_buffer, total_bytes);
    enable_endpoint_interrupt(out_endpoint);
    enable_endpoint_interrupt(in_endpoint);

    fill_endpoint_buffer(out_buffer, total_bytes, 32'heeee_eeee);
    arm_endpoint(out_endpoint, total_bytes, out_buffer, entry);
    clear_endpoint_interrupt(out_endpoint);
    for (int unsigned transaction_index = 0; transaction_index < transaction_count; transaction_index++) begin
      host_sequence = usb_interrupt_host_seq::type_id::create($sformatf("out_host_sequence_%0d", transaction_index));
      host_sequence.target_endpoint = out_endpoint;
      host_sequence.payload_byte_count = transaction_bytes;
      host_sequence.payload_base = out_payload_base + transaction_index * transaction_bytes + transaction_index;
      host_sequence.device_address = p_sequencer.cfg.device_address;
      host_sequence.transfer_label = $sformatf("High-bandwidth interrupt OUT %0d/%0d", transaction_index + 1, transaction_count);
      host_sequence.start(p_sequencer.host_sequencer);
      if (!host_sequence.completed) begin
        `uvm_fatal("USB_HB_INTERRUPT", "Interrupt OUT host sequence returned incomplete")
      end
      check_progress(out_endpoint, transaction_index + 1, out_buffer, "Interrupt OUT");
      verify_out_transaction(transaction_index);
    end

    fill_in_payload();
    arm_endpoint(in_endpoint, total_bytes, in_buffer, entry);
    clear_endpoint_interrupt(in_endpoint);
    for (int unsigned transaction_index = 0; transaction_index < transaction_count; transaction_index++) begin
      host_sequence = usb_interrupt_host_seq::type_id::create($sformatf("in_host_sequence_%0d", transaction_index));
      host_sequence.target_endpoint = in_endpoint;
      host_sequence.payload_byte_count = transaction_bytes;
      host_sequence.payload_base = in_payload_base + transaction_index * transaction_bytes + transaction_index;
      host_sequence.device_address = p_sequencer.cfg.device_address;
      host_sequence.transfer_label = $sformatf("High-bandwidth interrupt IN %0d/%0d", transaction_index + 1, transaction_count);
      host_sequence.start(p_sequencer.host_sequencer);
      if (!host_sequence.completed) begin
        `uvm_fatal("USB_HB_INTERRUPT", "Interrupt IN host sequence returned incomplete")
      end
      check_progress(in_endpoint, transaction_index + 1, in_buffer, "Interrupt IN");
    end

    completed = 1'b1;
    `uvm_info("USB_HB_INTERRUPT", "High-bandwidth interrupt OUT and IN scenario completed with all progress checks verified", UVM_LOW)
  endtask
endclass
