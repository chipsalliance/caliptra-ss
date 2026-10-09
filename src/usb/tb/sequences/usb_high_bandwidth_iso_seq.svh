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

// Exchanges three 1024-byte isochronous transactions per service interval.
class usb_high_bandwidth_iso_seq extends usb_base_seq;
  `uvm_object_utils(usb_high_bandwidth_iso_seq)

  int unsigned payload_bytes = 3 * 1024;
  logic [31:0] out_buffer = 32'h0000_1000;
  logic [31:0] in_buffer = 32'h0000_2000;
  logic [7:0] out_payload_base = 8'h10;
  logic [7:0] in_payload_base = 8'h90;
  time transfer_timeout = 750us;
  bit completed;

  function new(string name = "usb_high_bandwidth_iso_seq");
    super.new(name);
  endfunction

  // Fill the IN buffer with the host sequence's expected byte stream.
  task fill_in_payload();
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = in_payload_base + offset + lane;
      end
      write32(USB_DEV0_SRAM, in_buffer + offset, data_word);
    end
  endtask

  // Verify the complete OUT payload committed to packet memory.
  task verify_out_payload();
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = out_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, out_buffer + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf("ISO OUT mismatch at offset 0x%04h: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
    `uvm_info("USB_HB_ISO", $sformatf("Verified all %0d high-bandwidth ISO OUT bytes", payload_bytes), UVM_LOW)
  endtask

  // Enumerate and exercise high-bandwidth isochronous OUT followed by IN.
  virtual task body();
    usb_init_seq init_sequence;
    usb_iso_host_seq host_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t entry;

    completed = 1'b0;
    `uvm_info("USB_HB_ISO", "Starting high-bandwidth isochronous scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", "Enumeration did not complete")
    end

    out_endpoint = get_endpoint(2, USB_DIRECTION_OUT);
    in_endpoint = get_endpoint(2, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list("High-bandwidth ISO OUT", out_buffer, payload_bytes);
    check_buffer_clear_of_endpoint_list("High-bandwidth ISO IN", in_buffer, payload_bytes);
    enable_endpoint_interrupt(out_endpoint);
    enable_endpoint_interrupt(in_endpoint);

    fill_endpoint_buffer(out_buffer, payload_bytes, 32'heeee_eeee);
    arm_endpoint(out_endpoint, payload_bytes, out_buffer, entry);
    clear_endpoint_interrupt(out_endpoint);
    host_sequence = usb_iso_host_seq::type_id::create("out_host_sequence");
    host_sequence.target_endpoint = out_endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = out_payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label = "High-bandwidth ISO OUT";
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", "High-bandwidth ISO OUT returned incomplete")
    end
    wait_for_endpoint_interrupt(out_endpoint, transfer_timeout);
    verify_out_payload();

    fill_in_payload();
    arm_endpoint(in_endpoint, payload_bytes, in_buffer, entry);
    clear_endpoint_interrupt(in_endpoint);
    host_sequence = usb_iso_host_seq::type_id::create("in_host_sequence");
    host_sequence.target_endpoint = in_endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = in_payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label = "High-bandwidth ISO IN";
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", "High-bandwidth ISO IN returned incomplete")
    end
    read_endpoint_entry(in_endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_HB_ISO", $sformatf("High-bandwidth ISO IN entry did not retire: %s", describe_entry(entry)))
    end
    `uvm_info("USB_HB_ISO", "High-bandwidth ISO IN endpoint entry retired after all three transactions", UVM_LOW)

    completed = 1'b1;
    `uvm_info("USB_HB_ISO", "High-bandwidth ISO OUT and IN scenario completed with payloads verified", UVM_LOW)
  endtask
endclass
