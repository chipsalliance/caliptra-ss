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
// Optional response stress then reuses EP1 with one buffer and multiple items.
//
// Uses native BULK_OUT_TRANSFER/BULK_IN_TRANSFER (transaction/class_svt_usb_transfer.html)
// and supported link/physical checking. Endpoint protocol checks are unsupported
// in this UTMI 4-stack topology and are not credited here.
// Host helpers validate routed responses, completion and payload; this sequence
// checks descriptor writeback and buffer contents. The native IN result records
// the terminating ZLP when aligned_transfer_ends_with_zero_length is enabled.
class usb_double_buffer_bulk_seq extends usb_packet_buffer_seq;
  `uvm_object_utils(usb_double_buffer_bulk_seq)

  localparam int unsigned BUFFER_SELECT_1 = 1;
  localparam int unsigned RESPONSE_STRESS_BYTES = 16;
  localparam int unsigned BUFFER_POINTER_BYTES = 64;
  localparam int unsigned SHORT_PACKET_BYTES = 13;

  int unsigned bytes_per_buffer = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
  logic [31:0] out_buffer_0 = 32'h0000_0200;
  logic [31:0] out_buffer_1 = 32'h0000_0400;
  logic [31:0] in_buffer_0 = 32'h0000_0600;
  logic [31:0] in_buffer_1 = 32'h0000_0800;
  logic [7:0] out_payload_base = 8'h20;
  logic [7:0] in_payload_base = 8'h80;
  logic [7:0] packet_tag_stride = 8'h31;
  time transfer_timeout = 500us;
  // Zero preserves the original two-buffer scenario; nine exceeds UVM's
  // default response depth within each single active host sequence.
  int unsigned response_stress_count = 0;
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
    // Integration Guide 4.2.3 pp47-48: round packet-pointer advance to 64-byte units.
    expected_entry_0.buffer_offset += (bytes_per_buffer + BUFFER_POINTER_BYTES - 1) / BUFFER_POINTER_BYTES;
    expected_entry_1 = armed_entry_1;
    expected_entry_1.active = 1'b0;
    expected_entry_1.nbytes = 0;
    expected_entry_1.buffer_offset += (bytes_per_buffer + BUFFER_POINTER_BYTES - 1) / BUFFER_POINTER_BYTES;
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
        // Poll interval between SRAM descriptor reads while waiting for both OUT buffers to retire.
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

  // Compare the full OUT stream, or a requested prefix, against host intent.
  task verify_out_payload(int unsigned payload_bytes = 0);
    logic [31:0] observed_word;
    logic [31:0] expected_word;
    int unsigned checked_bytes;

    checked_bytes = (payload_bytes == 0) ? 2 * bytes_per_buffer : payload_bytes;
    if (checked_bytes > 2 * bytes_per_buffer || checked_bytes % 4 != 0) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", "OUT payload check requires a word-aligned prefix within the two buffers")
    end
    for (int unsigned stream_offset = 0; stream_offset < checked_bytes; stream_offset += 4) begin
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
    `uvm_info("USB_DOUBLE_BUFFER",
              $sformatf("Verified %s and all %0d payload bytes", (payload_bytes == 0) ? "both OUT buffers" : "OUT buffer prefix", checked_bytes),
              UVM_LOW)
  endtask

  // Rearm single buffer zero between checked stress transfers.
  task arm_response_stress_buffer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] buffer_offset;

    buffer_offset = (endpoint.direction == USB_DIRECTION_OUT) ? out_buffer_0 : in_buffer_0;
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      fill_endpoint_buffer(buffer_offset, RESPONSE_STRESS_BYTES, 32'heeee_eeee);
    end
    clear_endpoint_interrupt(endpoint);
    arm_endpoint(endpoint, RESPONSE_STRESS_BYTES, buffer_offset, entry);
  endtask

  // Observe each retirement and rearm while one host sequence remains active.
  task service_response_stress_buffers(usb_endpoint_cfg endpoint);
    usb_ep_entry_t expected_entry;
    logic [31:0] buffer_offset;

    buffer_offset = (endpoint.direction == USB_DIRECTION_OUT) ? out_buffer_0 : in_buffer_0;
    expected_entry = endpoint_entry(1'b0, 1'b0, 0, buffer_offset);
    // Programmers Guide 4.2.3 encodes the next buffer in 64-byte units.
    expected_entry.buffer_offset += (RESPONSE_STRESS_BYTES + 63) / 64;
    for (int unsigned transfer_index = 0; transfer_index < response_stress_count; transfer_index++) begin
      wait_for_endpoint_interrupt(endpoint, transfer_timeout);
      check_endpoint_entry_writeback(endpoint, expected_entry, "Response-stress transfer did not retire");
      if (endpoint.direction == USB_DIRECTION_OUT) verify_out_payload(RESPONSE_STRESS_BYTES);
      `uvm_info("USB_BULK_RESPONSE_STRESS",
                $sformatf("%s retired transfer %0d/%0d", endpoint.short_name(), transfer_index + 1, response_stress_count), UVM_LOW)
      if (transfer_index + 1 < response_stress_count) arm_response_stress_buffer(endpoint);
    end
  endtask

  // Reuse the bulk helpers for nine or more items per active IN/OUT sequence.
  // Native VIP transfer checking remains active; packet count is not response count.
  task run_response_stress(
    usb_endpoint_cfg out_endpoint, usb_endpoint_cfg in_endpoint,
    usb_bulk_out_host_seq out_host_sequence, usb_bulk_in_host_seq in_host_sequence
  );
    if (response_stress_count <= 8) begin
      `uvm_fatal("USB_BULK_RESPONSE_STRESS", "Response stress requires at least nine transfers per active sequence")
    end
    `uvm_info("USB_BULK_RESPONSE_STRESS",
              $sformatf("Starting same-sequence response stress: transfers_per_direction=%0d bytes=%0d",
                        response_stress_count, RESPONSE_STRESS_BYTES), UVM_LOW)

    // The original scenario has already returned EPBUFCFG/EPINUSE to zero.
    out_host_sequence.transfer_count = response_stress_count;
    out_host_sequence.payload_byte_count = RESPONSE_STRESS_BYTES;
    out_host_sequence.transfer_label = "Response-stress bulk OUT";
    arm_response_stress_buffer(out_endpoint);
    fork
      out_host_sequence.start(p_sequencer.host_sequencer);
      service_response_stress_buffers(out_endpoint);
    join
    if (!out_host_sequence.completed ||
        out_host_sequence.completed_transfer_count !== response_stress_count ||
        out_host_sequence.routed_response_count !== response_stress_count) begin
      `uvm_fatal("USB_BULK_RESPONSE_STRESS", "OUT stress did not validate all routed responses in one active sequence")
    end

    in_host_sequence.transfer_count = response_stress_count;
    in_host_sequence.payload_byte_count = RESPONSE_STRESS_BYTES;
    in_host_sequence.expect_zero_length_termination = 1'b0;
    in_host_sequence.transfer_label = "Response-stress bulk IN";
    fill_incrementing_buffer(in_buffer_0, 0);
    arm_response_stress_buffer(in_endpoint);
    fork
      in_host_sequence.start(p_sequencer.host_sequencer);
      service_response_stress_buffers(in_endpoint);
    join
    if (!in_host_sequence.completed ||
        in_host_sequence.completed_transfer_count !== response_stress_count ||
        in_host_sequence.routed_response_count !== response_stress_count) begin
      `uvm_fatal("USB_BULK_RESPONSE_STRESS", "IN stress did not validate all routed responses in one active sequence")
    end
    `uvm_info("USB_BULK_RESPONSE_STRESS",
              $sformatf("Same-sequence response stress complete: OUT=%0d IN=%0d routed responses checked",
                        out_host_sequence.routed_response_count, in_host_sequence.routed_response_count), UVM_LOW)
  endtask

  // Exchange a full/short pair using existing native transfers and packet checks.
  task run_full_short_pair(usb_endpoint_cfg endpoint);
    usb_bulk_out_host_seq out_host_sequence;
    usb_bulk_in_host_seq in_host_sequence;
    usb_ep_entry_t entry_0;
    usb_ep_entry_t entry_1;
    logic [31:0] buffer_0;
    logic [31:0] buffer_1;
    logic [31:0] epinuse;
    logic [7:0] payload_base;
    logic [7:0] second_packet_base;
    bit in_direction;
    string label;

    in_direction = endpoint.direction === USB_DIRECTION_IN;
    buffer_0 = in_direction ? in_buffer_0 : out_buffer_0;
    buffer_1 = in_direction ? in_buffer_1 : out_buffer_1;
    payload_base = in_direction ? in_payload_base : out_payload_base;
    second_packet_base = stream_payload_byte(payload_base, bytes_per_buffer);
    label = $sformatf("Full/%0d bulk %s", SHORT_PACKET_BYTES, in_direction ? "IN" : "OUT");
    if (SHORT_PACKET_BYTES >= bytes_per_buffer) `uvm_fatal("USB_DOUBLE_BUFFER", "Short packet must be smaller than the full buffer")
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("Starting %s: full_bytes=%0d total_bytes=%0d timeout=%0t",
      label, bytes_per_buffer, bytes_per_buffer + SHORT_PACKET_BYTES, transfer_timeout), UVM_LOW)
    read_endpoint_entry(endpoint, entry_0);
    read_endpoint_entry(endpoint, entry_1, BUFFER_SELECT_1);
    if (!(entry_0.active === 1'b0) || !(entry_1.active === 1'b0) ||
        !(entry_0.disabled === 1'b0) || !(entry_1.disabled === 1'b0)) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", $sformatf("%s requires enabled software-owned buffers before reuse: buffer0=%s buffer1=%s",
        label, describe_entry(entry_0), describe_entry(entry_1)))
    end
    // Both prior directions are idle before changing the next-buffer selection.
    ral_write32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, 32'h0);
    prepare_packet_buffer(buffer_0, bytes_per_buffer, bytes_per_buffer, payload_base, in_direction);
    prepare_packet_buffer(buffer_1, bytes_per_buffer, SHORT_PACKET_BYTES, second_packet_base, in_direction);
    clear_endpoint_interrupt(endpoint);
    arm_endpoint(endpoint, bytes_per_buffer, buffer_0, entry_0);
    // OUT retains capacity above the short payload to check residual retirement.
    arm_endpoint(endpoint, in_direction ? SHORT_PACKET_BYTES : bytes_per_buffer, buffer_1, entry_1, BUFFER_SELECT_1);
    if (in_direction) begin
      in_host_sequence = usb_bulk_in_host_seq::type_id::create("short_in_host_sequence");
      in_host_sequence.target_endpoint = endpoint;
      in_host_sequence.payload_byte_count = bytes_per_buffer + SHORT_PACKET_BYTES;
      in_host_sequence.payload_base = payload_base;
      in_host_sequence.payload_packet_bytes = bytes_per_buffer;
      in_host_sequence.payload_packet_stride = packet_tag_stride;
      in_host_sequence.device_address = p_sequencer.cfg.device_address;
      in_host_sequence.bulk_transfer_timeout = transfer_timeout;
      in_host_sequence.transfer_label = label;
      in_host_sequence.expect_zero_length_termination = 1'b0;
      in_host_sequence.start(p_sequencer.host_sequencer);
      if (!(in_host_sequence.completed === 1'b1)) `uvm_fatal("USB_DOUBLE_BUFFER", {label, " returned incomplete"})
    end else begin
      out_host_sequence = usb_bulk_out_host_seq::type_id::create("short_out_host_sequence");
      out_host_sequence.target_endpoint = endpoint;
      out_host_sequence.payload_byte_count = bytes_per_buffer + SHORT_PACKET_BYTES;
      out_host_sequence.payload_base = payload_base;
      out_host_sequence.payload_packet_bytes = bytes_per_buffer;
      out_host_sequence.payload_packet_stride = packet_tag_stride;
      out_host_sequence.device_address = p_sequencer.cfg.device_address;
      out_host_sequence.bulk_transfer_timeout = transfer_timeout;
      out_host_sequence.transfer_label = label;
      out_host_sequence.start(p_sequencer.host_sequencer);
      if (!(out_host_sequence.completed === 1'b1)) `uvm_fatal("USB_DOUBLE_BUFFER", {label, " returned incomplete"})
    end
    wait_for_endpoint_interrupt(endpoint, transfer_timeout);
    check_packet_retired(endpoint, entry_0, bytes_per_buffer, transfer_timeout, {label, " full buffer"});
    check_packet_retired(endpoint, entry_1, SHORT_PACKET_BYTES, transfer_timeout, {label, " short buffer"}, BUFFER_SELECT_1);
    check_packet_buffer(buffer_0, bytes_per_buffer, bytes_per_buffer, payload_base, in_direction, {label, " full buffer"});
    check_packet_buffer(buffer_1, bytes_per_buffer, SHORT_PACKET_BYTES, second_packet_base, in_direction, {label, " short buffer"});
    ral_read32("EPINUSE", p_sequencer.reg_model.combo.dev0_csr.EPINUSE, epinuse);
    if (!((epinuse & endpoint.csr_bit_mask()) === 32'b0)) begin
      `uvm_fatal("USB_DOUBLE_BUFFER", $sformatf("%s did not return to buffer 0 after two packets: EPINUSE=0x%08h", label, epinuse))
    end
    `uvm_info("USB_DOUBLE_BUFFER", $sformatf("%s complete: both buffers/guards/selection verified, short residual=%0d",
      label, in_direction ? 0 : bytes_per_buffer - SHORT_PACKET_BYTES), UVM_LOW)
  endtask

  // Enumerate, retain full/full/ZLP, add FS full/short pairs, then optional response stress.
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
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) begin
      bytes_per_buffer = out_endpoint.max_packet_size;
      if (transfer_timeout < USB_FS_BULK_PAIR_TIMEOUT) transfer_timeout = USB_FS_BULK_PAIR_TIMEOUT;
      `uvm_info("USB_DOUBLE_BUFFER", $sformatf("FS double-buffer profile: bytes=%0d transfer/retirement bound=%0t",
        bytes_per_buffer, transfer_timeout), UVM_LOW)
    end
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
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) out_host_sequence.bulk_transfer_timeout = transfer_timeout;
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
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) in_host_sequence.bulk_transfer_timeout = transfer_timeout;
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
    if (p_sequencer.cfg.speed == USB_SPEED_FULL) begin
      run_full_short_pair(out_endpoint);
      run_full_short_pair(in_endpoint);
    end
    ral_write32("EPBUFCFG", p_sequencer.reg_model.combo.dev0_csr.EPBUFCFG, 32'h0);

    if (response_stress_count != 0) begin
      run_response_stress(out_endpoint, in_endpoint, out_host_sequence, in_host_sequence);
    end
    completed = 1'b1;
    `uvm_info("USB_DOUBLE_BUFFER", "Double-buffer bulk IN and OUT scenario completed with both buffers verified", UVM_LOW)
  endtask
endclass
