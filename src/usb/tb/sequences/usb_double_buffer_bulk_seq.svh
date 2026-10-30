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
//
// Relies on the Synopsys SVT USB VIP's built-in BULK_OUT_TRANSFER and
// BULK_IN_TRANSFER sequences (transaction/class_svt_usb_transfer.html) and
// built-in protocol/link/physical checks (enabled by default via
// register_default_chks = 1, enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html,
// coverage/class_svt_usb_link_20_sc.html, and
// coverage/class_svt_usb_physical_20_sc.html):
//   - svt_usb_transfer::results_status[5]:
//     Verifies the 2-packet (1024 B) bulk IN transfer is terminated by a
//     zero-length DATA0 packet when aligned_transfer_ends_with_zero_length == 1.
//   - svt_usb_protocol_ep_sc:
//     * data_toggle_check: Checks DATA0 -> DATA1 toggle alternation across
//       buffers 0 and 1 (and DATA0 on the terminating IN ZLP).
//     * packet_error_check: Checks PID, CRC5, CRC16, bitstuff, and framing.
//     * valid_device_data_check: Checks IN packet lengths against 512 B
//       wMaxPacketSize and expected transfer byte counts.
//     * valid_device_response_check & valid_host_response_check: Checks
//       accepting handshakes across both double-buffered packets.
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
  logic [7:0] packet_tag_stride = 8'h31;
  time transfer_timeout = 500us;
  bit completed;

  function new(string name = "usb_double_buffer_bulk_seq");
    super.new(name);
  endfunction

  function logic [7:0] stream_payload_byte(
      logic [7:0] payload_base,
      int unsigned stream_offset
  );
    return payload_base + stream_offset +
           (stream_offset / bytes_per_buffer) * packet_tag_stride;
  endfunction

  // Fill one device-to-host buffer with an incrementing byte stream.
  task fill_incrementing_buffer(logic [31:0] buffer_offset, int unsigned stream_offset);
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < bytes_per_buffer; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] =
            stream_payload_byte(
                in_payload_base,
                stream_offset + offset + lane);
      end
      write32(USB_DEV0_SRAM, buffer_offset + offset, data_word);
    end
  endtask

  // Require both endpoint-list buffers to have exact post-transfer writeback.
  task check_both_entries_retired(
      usb_endpoint_cfg endpoint,
      usb_ep_entry_t armed_entry_0,
      usb_ep_entry_t armed_entry_1,
      string label
  );
    usb_ep_entry_t expected_entry_0;
    usb_ep_entry_t expected_entry_1;

    expected_entry_0 = armed_entry_0;
    expected_entry_0.active = 1'b0;
    expected_entry_0.nbytes = 0;
    expected_entry_0.buffer_offset += bytes_per_buffer >> 6;
    expected_entry_1 = armed_entry_1;
    expected_entry_1.active = 1'b0;
    expected_entry_1.nbytes = 0;
    expected_entry_1.buffer_offset += bytes_per_buffer >> 6;
    check_endpoint_entry_writeback(
        endpoint,
        expected_entry_0,
        {label, " buffer 0 writeback mismatch"});
    check_endpoint_entry_writeback(
        endpoint,
        expected_entry_1,
        {label, " buffer 1 writeback mismatch"},
        BUFFER_SELECT_1);
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("%s retired both endpoint-list buffers with exact address writeback", label), UVM_LOW)
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

  // Wait until hardware has retired a single endpoint-list entry.
  task wait_for_entry_retired(
      usb_endpoint_cfg endpoint,
      string label,
      int unsigned buffer_select = 0
  );
    usb_ep_entry_t entry;
    realtime deadline;
    bit retired;

    deadline = $realtime + transfer_timeout;
    retired = 1'b0;
    while (!retired && $realtime < deadline) begin
      read_endpoint_entry(endpoint, entry, buffer_select);
      retired = entry.active === 1'b0 && entry.nbytes === 0;
      if (!retired) begin
        #(EP_POLL_INTERVAL);
      end
    end
    if (!retired) begin
      `uvm_fatal(
        "USB_DOUBLE_BUFFER",
        $sformatf(
          "%s did not retire buffer %0d within %0t: entry=%s",
          label,
          buffer_select,
          transfer_timeout,
          describe_entry(entry)
        )
      )
    end
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
        expected_word[8*lane +: 8] =
            stream_payload_byte(out_payload_base, stream_offset + lane);
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
    usb_ep_entry_t out_entry_0;
    usb_ep_entry_t out_entry_1;
    usb_ep_entry_t in_entry_0;
    usb_ep_entry_t in_entry_1;
    usb_ep_entry_t zlp_entry;
    logic [31:0] double_buffer_mask;
    logic [31:0] epinuse_val;

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
    arm_endpoint(out_endpoint, bytes_per_buffer, out_buffer_0, out_entry_0);
    arm_endpoint(out_endpoint, bytes_per_buffer, out_buffer_1, out_entry_1, BUFFER_SELECT_1);
    clear_endpoint_interrupt(out_endpoint);
    out_host_sequence = usb_bulk_out_host_seq::type_id::create("out_host_sequence");
    out_host_sequence.target_endpoint = out_endpoint;
    out_host_sequence.payload_byte_count = 2 * bytes_per_buffer;
    out_host_sequence.payload_base = out_payload_base;
    out_host_sequence.payload_packet_bytes = bytes_per_buffer;
    out_host_sequence.payload_packet_stride = packet_tag_stride;
    out_host_sequence.device_address = p_sequencer.cfg.device_address;
    out_host_sequence.transfer_label = "Double-buffer bulk OUT";
    out_host_sequence.start(p_sequencer.host_sequencer);
    if (!out_host_sequence.completed) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "Double-buffer bulk OUT returned incomplete")
    end
    wait_for_endpoint_interrupt(out_endpoint, transfer_timeout);
    wait_for_both_entries_retired(out_endpoint, "Bulk OUT");
    check_both_entries_retired(
        out_endpoint,
        out_entry_0,
        out_entry_1,
        "Bulk OUT");
    ral_read32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, epinuse_val);
    if ((epinuse_val & out_endpoint.csr_bit_mask()) !== 32'h0) begin
      `uvm_fatal(
        "USB_DOUBLE_BUFFER",
        $sformatf(
          "EPINUSE for %s did not return to buffer 0 after 2 OUT packets: EPINUSE=0x%08h",
          out_endpoint.convert2string(),
          epinuse_val
        )
      )
    end
    verify_out_payload();

    fill_incrementing_buffer(in_buffer_0, 0);
    fill_incrementing_buffer(in_buffer_1, bytes_per_buffer);
    arm_endpoint(in_endpoint, bytes_per_buffer, in_buffer_0, in_entry_0);
    arm_endpoint(in_endpoint, bytes_per_buffer, in_buffer_1, in_entry_1, BUFFER_SELECT_1);
    clear_endpoint_interrupt(in_endpoint);
    in_host_sequence = usb_bulk_in_host_seq::type_id::create("in_host_sequence");
    in_host_sequence.target_endpoint = in_endpoint;
    in_host_sequence.payload_byte_count = 2 * bytes_per_buffer;
    in_host_sequence.payload_base = in_payload_base;
    in_host_sequence.payload_packet_bytes = bytes_per_buffer;
    in_host_sequence.payload_packet_stride = packet_tag_stride;
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
        // data buffers retire, clear the latched data-retirement interrupt and
        // reuse buffer 0 for the terminating ZLP.
        wait_for_both_entries_retired(in_endpoint, "Bulk IN data");
        check_both_entries_retired(
            in_endpoint,
            in_entry_0,
            in_entry_1,
            "Bulk IN data");
        clear_endpoint_interrupt(in_endpoint);
        arm_endpoint(in_endpoint, 0, in_buffer_0, zlp_entry);
        zlp_entry.active = 1'b0;
        `uvm_info("USB_DOUBLE_BUFFER", "Re-armed IN buffer 0 with a terminating ZLP", UVM_LOW)
      end
    join
    wait_for_endpoint_interrupt(in_endpoint, transfer_timeout);
    wait_for_entry_retired(in_endpoint, "Bulk IN terminating ZLP");
    check_endpoint_entry_writeback(
        in_endpoint,
        zlp_entry,
        "Bulk IN terminating ZLP writeback mismatch");
    ral_read32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, epinuse_val);
    if ((epinuse_val & in_endpoint.csr_bit_mask()) !== in_endpoint.csr_bit_mask()) begin
      `uvm_fatal(
        "USB_DOUBLE_BUFFER",
        $sformatf(
          "EPINUSE for %s did not advance to buffer 1 after 3 IN packets: EPINUSE=0x%08h",
          in_endpoint.convert2string(),
          epinuse_val
        )
      )
    end
    ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, 32'h0);
    ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, 32'h0);

    completed = 1'b1;
    `uvm_info("USB_DOUBLE_BUFFER", "Double-buffer bulk IN and OUT scenario completed with both buffers verified", UVM_LOW)
  endtask
endclass
