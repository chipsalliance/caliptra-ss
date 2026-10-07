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

// Exchanges two packets in each direction through double-buffered EP1.
class usb_double_buffer_bulk_seq extends usb_base_seq;
  `uvm_object_utils(usb_double_buffer_bulk_seq)

  localparam int unsigned BUFFER_SELECT_1 = 1;

  int unsigned bytes_per_buffer = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
  logic [31:0] out_buffer_0 = 32'h0000_0200;
  logic [31:0] out_buffer_1 = 32'h0000_0400;
  logic [31:0] in_buffer_0 = 32'h0000_0600;
  logic [31:0] in_buffer_1 = 32'h0000_0800;
  logic [7:0] out_payload_base = 8'h20;
  logic [7:0] in_payload_base = 8'h80;
  time transfer_timeout = 500us;
  bit completed;

  function new(string name = "usb_double_buffer_bulk_seq");
    super.new(name);
  endfunction

  // Fill one device-to-host buffer with an incrementing byte stream.
  task fill_incrementing_buffer(logic [31:0] buffer_offset, int unsigned stream_offset);
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < bytes_per_buffer; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = in_payload_base + stream_offset + offset + lane;
      end
      write32(USB_DEV0_SRAM, buffer_offset + offset, data_word);
    end
  endtask

  // Require both endpoint-list buffers to be fully retired.
  task check_both_entries_retired(usb_endpoint_cfg endpoint, string label);
    usb_ep_entry_t entry_0;
    usb_ep_entry_t entry_1;

    read_endpoint_entry(endpoint, entry_0);
    read_endpoint_entry(endpoint, entry_1, BUFFER_SELECT_1);
    if (entry_0.active !== 1'b0 || entry_0.nbytes !== 0 ||
        entry_1.active !== 1'b0 || entry_1.nbytes !== 0) begin
      `uvm_fatal(
        "USB_DOUBLE_BUFFER",
        $sformatf("%s entries did not both retire: buffer0=%s buffer1=%s", label, describe_entry(entry_0), describe_entry(entry_1))
      )
    end
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("%s retired both endpoint-list buffers", label), UVM_LOW)
  endtask

  // Wait until hardware has consumed both active buffers.
  task wait_for_both_entries_retired(usb_endpoint_cfg endpoint, string label);
    usb_ep_entry_t entry_0;
    usb_ep_entry_t entry_1;
    realtime deadline;
    bit retired;

    deadline = $realtime + transfer_timeout;
    retired = 1'b0;
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("Waiting for %s to consume both buffers", label), UVM_LOW)
    while (!retired && $realtime < deadline) begin
      read_endpoint_entry(endpoint, entry_0);
      read_endpoint_entry(endpoint, entry_1, BUFFER_SELECT_1);
      retired = entry_0.active === 1'b0 && entry_0.nbytes === 0 &&
                entry_1.active === 1'b0 && entry_1.nbytes === 0;
      if (!retired) begin
        #1us;
      end
    end
    if (!retired) begin
      `uvm_fatal(
        "USB_DOUBLE_BUFFER",
        $sformatf("%s did not consume both buffers: buffer0=%s buffer1=%s", label, describe_entry(entry_0), describe_entry(entry_1))
      )
    end
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("%s consumed both data buffers", label), UVM_LOW)
  endtask

  // Compare the two OUT buffers against the contiguous host payload.
  task verify_out_payload();
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    for (int unsigned stream_offset = 0; stream_offset < 2 * bytes_per_buffer; stream_offset += 4) begin
      logic [31:0] buffer_offset;

      buffer_offset = (stream_offset < bytes_per_buffer) ?
                      out_buffer_0 + stream_offset :
                      out_buffer_1 + stream_offset - bytes_per_buffer;
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = out_payload_base + stream_offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_DOUBLE_BUFFER",
          $sformatf("OUT payload mismatch at stream offset %0d: data=0x%08h expected=0x%08h", stream_offset, observed_word, expected_word)
        )
      end
    end
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("Verified both OUT buffers and all %0d payload bytes", 2 * bytes_per_buffer), UVM_LOW)
  endtask

  // Enumerate and exchange two bulk packets through each endpoint direction.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq out_host_sequence;
    usb_bulk_in_host_seq in_host_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t entry;
    logic [31:0] double_buffer_mask;

    completed = 1'b0;
    `uvm_info("USB_DOUBLE_BUFFER", "Starting double-buffer bulk scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "Enumeration did not complete")
    end

    out_endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    in_endpoint = get_endpoint(1, USB_DIRECTION_IN);
    if (out_endpoint.max_packet_size != bytes_per_buffer ||
        in_endpoint.max_packet_size != bytes_per_buffer) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "EP1 IN and OUT maximum packet sizes must match bytes_per_buffer")
    end
    check_buffer_clear_of_endpoint_list("Double-buffer OUT0", out_buffer_0, bytes_per_buffer);
    check_buffer_clear_of_endpoint_list("Double-buffer OUT1", out_buffer_1, bytes_per_buffer);
    check_buffer_clear_of_endpoint_list("Double-buffer IN0", in_buffer_0, bytes_per_buffer);
    check_buffer_clear_of_endpoint_list("Double-buffer IN1", in_buffer_1, bytes_per_buffer);

    double_buffer_mask = out_endpoint.csr_bit_mask() | in_endpoint.csr_bit_mask();
    ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, double_buffer_mask);
    ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, 32'h0);
    enable_endpoint_interrupt(out_endpoint);
    enable_endpoint_interrupt(in_endpoint);

    fill_endpoint_buffer(out_buffer_0, bytes_per_buffer, 32'heeee_eeee);
    fill_endpoint_buffer(out_buffer_1, bytes_per_buffer, 32'heeee_eeee);
    arm_endpoint(out_endpoint, bytes_per_buffer, out_buffer_0, entry);
    arm_endpoint(out_endpoint, bytes_per_buffer, out_buffer_1, entry, BUFFER_SELECT_1);
    clear_endpoint_interrupt(out_endpoint);
    out_host_sequence = usb_bulk_out_host_seq::type_id::create("out_host_sequence");
    out_host_sequence.target_endpoint = out_endpoint;
    out_host_sequence.payload_byte_count = 2 * bytes_per_buffer;
    out_host_sequence.payload_base = out_payload_base;
    out_host_sequence.device_address = p_sequencer.cfg.device_address;
    out_host_sequence.transfer_label = "Double-buffer bulk OUT";
    out_host_sequence.start(p_sequencer.host_sequencer);
    if (!out_host_sequence.completed) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "Double-buffer bulk OUT returned incomplete")
    end
    wait_for_endpoint_interrupt(out_endpoint, transfer_timeout);
    check_both_entries_retired(out_endpoint, "Bulk OUT");
    verify_out_payload();

    fill_incrementing_buffer(in_buffer_0, 0);
    fill_incrementing_buffer(in_buffer_1, bytes_per_buffer);
    arm_endpoint(in_endpoint, bytes_per_buffer, in_buffer_0, entry);
    arm_endpoint(in_endpoint, bytes_per_buffer, in_buffer_1, entry, BUFFER_SELECT_1);
    clear_endpoint_interrupt(in_endpoint);
    in_host_sequence = usb_bulk_in_host_seq::type_id::create("in_host_sequence");
    in_host_sequence.target_endpoint = in_endpoint;
    in_host_sequence.payload_byte_count = 2 * bytes_per_buffer;
    in_host_sequence.payload_base = in_payload_base;
    in_host_sequence.device_address = p_sequencer.cfg.device_address;
    in_host_sequence.transfer_label = "Double-buffer bulk IN";
    in_host_sequence.expect_zero_length_termination = 1'b1;
    fork
      begin
        in_host_sequence.start(p_sequencer.host_sequencer);
        if (!in_host_sequence.completed) begin
          `uvm_fatal("USB_DOUBLE_BUFFER", "Double-buffer bulk IN returned incomplete")
        end
      end
      begin
        // Two full-size packets need a terminating short packet. Once both
        // data buffers retire, reuse buffer 0 for the terminating ZLP.
        wait_for_both_entries_retired(in_endpoint, "Bulk IN data");
        arm_endpoint(in_endpoint, 0, in_buffer_0, entry);
        `uvm_info("USB_DOUBLE_BUFFER", "Re-armed IN buffer 0 with a terminating ZLP", UVM_LOW)
      end
    join
    wait_for_endpoint_interrupt(in_endpoint, transfer_timeout);
    check_both_entries_retired(in_endpoint, "Bulk IN");

    completed = 1'b1;
    `uvm_info("USB_DOUBLE_BUFFER", "Double-buffer bulk IN and OUT scenario completed with both buffers verified", UVM_LOW)
  endtask
endclass
