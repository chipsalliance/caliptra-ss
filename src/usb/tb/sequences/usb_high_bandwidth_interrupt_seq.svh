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

// Checks clean high-bandwidth interrupt bursts and partial descriptors retained
// across high-speed SOF boundaries using Synopsys SVT USB VIP transfers and
// built-in VIP checking.
//
// Relies on the Synopsys SVT USB VIP's built-in periodic microframe scheduling
// (svt_usb_transfer::start_uframe_bus_interval and end_uframe_bus_interval in
// transaction/class_svt_usb_transfer.html) and built-in protocol/link/physical
// checks (enabled by default via register_default_chks = 1,
// enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html,
// coverage/class_svt_usb_link_20_sc.html, and
// coverage/class_svt_usb_physical_20_sc.html):
//   - svt_usb_transfer::results_status[6]:
//     Ensures every scheduled 1-, 2-, or 3-transaction interrupt chunk
//     completes inside its single scheduled microframe service opportunity.
//   - svt_usb_protocol_ep_sc:
//     * data_toggle_check: Checks USB 2.0 Section 5.9.1 / 8.6 DATA0/DATA1
//       toggle alternation across all transactions within a microframe and
//       across microframe SOF boundaries (detecting any erroneous reset to
//       DATA0 at SOF).
//     * packet_error_check: Checks all tokens, data packets, and handshakes
//       for PID, CRC5, CRC16, bitstuff, and framing errors.
//     * valid_device_data_check: Checks IN data packet lengths against
//       endpoint wMaxPacketSize (1024 B) and expected transfer byte counts.
//     * valid_device_response_check & valid_host_response_check: Checks
//       accepting ACK handshakes for interrupt OUT and IN transactions.
//     * sof_not_received_in_tmicroframeinterval, sof_not_rcvd_at_end_of_uframe,
//       unexpected_sof_rcvd, received_unexpected_uframe_cnt: Enforces 125 us
//       HS microframe SOF timing and frame numbering.
//   - svt_usb_link_20_sc & svt_usb_physical_20_sc:
//     * unexpected_response_check, utmi_signal_X_Z_check, chk_utmi_byte_time,
//       chk_utmi_packet_begin_hs, chk_utmi_packet_end_hs, chk_utmi_rxerror.
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

  // Wait for the endpoint writeback after a serviced chunk.
  task wait_for_progress(
    usb_endpoint_cfg endpoint,
    int unsigned completed_transactions,
    logic [31:0] initial_buffer,
    string label
  );
    usb_ep_entry_t entry;
    int unsigned remaining_bytes;
    realtime deadline;
    bit matched;

    remaining_bytes = (transaction_count - completed_transactions) * transaction_bytes;
    deadline = $realtime + transfer_timeout;
    matched = 1'b0;
    `uvm_info("USB_HB_INTERRUPT",
              $sformatf("%s waiting for descriptor progress: transactions=%0d/%0d timeout=%0t",
                        label, completed_transactions, transaction_count, transfer_timeout), UVM_LOW)
    while (!matched && $realtime < deadline) begin
      read_endpoint_entry(endpoint, entry);
      matched = entry.active === (remaining_bytes != 0) &&
                entry.nbytes === remaining_bytes &&
                entry_buffer_byte_offset(entry) ===
                    initial_buffer + completed_transactions * transaction_bytes;
      if (!matched) begin
        #1us;
      end
    end
    if (!matched) begin
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

  // Check the endpoint's completion status without disturbing other endpoints.
  task check_interrupt_status(usb_endpoint_cfg endpoint, bit expected_set, string label);
    logic [31:0] status;
    logic [31:0] mask;

    mask = endpoint_intstat_mask(endpoint);
    if (expected_set) begin
      poll_csr_bits(label, p_sequencer.reg_model.combo.dev0_csr.INTSTAT, mask, 1'b1, transfer_timeout, status);
    end else begin
      ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, status);
    end
    if ((status & mask) !== (expected_set ? mask : 32'h0)) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s INTSTAT=%08h mask=%08h expected_set=%0b", label, status, mask, expected_set))
    end
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s verified endpoint interrupt=%0b", label, expected_set), UVM_LOW)
  endtask

  // Wait for the SVT host microframe counter to advance past target_microframe
  // (confirming an intervening HS SOF was transmitted by the VIP).
  task wait_for_microframe_after(int unsigned target_microframe, string label);
    svt_usb_status shared_status;
    realtime deadline;

    shared_status = p_sequencer.host_sequencer.get_shared_status(this);
    if (shared_status == null || shared_status.local_host_status == null) begin
      `uvm_fatal("USB_HB_INTERRUPT", "SVT host shared_status.local_host_status is unavailable")
    end
    deadline = $realtime + transfer_timeout;
    while (shared_status.local_host_status.micro_frame_count <= target_microframe &&
           $realtime < deadline) begin
      #1us;
    end
    if (shared_status.local_host_status.micro_frame_count <= target_microframe) begin
      `uvm_fatal(
        "USB_HB_INTERRUPT",
        $sformatf("%s timed out waiting for SOF after microframe %0d", label, target_microframe)
      )
    end
  endtask

  // Service a native VIP transfer chunk within one microframe and verify DUT descriptor progress.
  task service_chunk(
    usb_endpoint_cfg endpoint,
    int unsigned first_transaction,
    int unsigned packet_count,
    string label,
    output int unsigned scheduled_microframe
  );
    usb_interrupt_host_seq host_sequence;

    host_sequence = usb_interrupt_host_seq::type_id::create("chunk_host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = packet_count * transaction_bytes;
    host_sequence.payload_base = endpoint.direction == USB_DIRECTION_IN ? in_payload_base : out_payload_base;
    host_sequence.payload_packet_bytes = transaction_bytes;
    host_sequence.payload_packet_stride = 1;
    host_sequence.payload_stream_offset = first_transaction * transaction_bytes;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label = label;
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s host transfer returned incomplete", label))
    end
    scheduled_microframe = host_sequence.scheduled_microframe;
    wait_for_progress(endpoint, first_transaction + packet_count,
                      endpoint.direction == USB_DIRECTION_IN ? in_buffer : out_buffer, label);
  endtask

  // Deliberately incomplete host service across a microframe SOF boundary:
  // USB 2.0 Section 5.9.1 requires the interrupt endpoint to retain its active
  // residual descriptor and DATA0/DATA1 toggle state across SOF boundaries.
  task partial_service_case(usb_endpoint_cfg endpoint, int unsigned prefix_packets);
    usb_ep_entry_t armed_entry;
    usb_ep_entry_t partial_entry;
    usb_ep_entry_t observed_entry;
    logic [31:0] buffer_offset;
    string label;
    int unsigned prefix_microframe;
    int unsigned remainder_microframe;

    if (transaction_count != 3 || !(prefix_packets inside {1, 2})) begin
      `uvm_fatal("USB_HB_INTERRUPT", "Partial service requires a three-packet descriptor and one-/two-packet prefix")
    end
    label = $sformatf("Interrupt %s partial-service %0d+%0d",
                      endpoint.direction == USB_DIRECTION_IN ? "IN" : "OUT", prefix_packets, transaction_count - prefix_packets);
    buffer_offset = endpoint.direction == USB_DIRECTION_IN ? in_buffer : out_buffer;
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s starting; descriptor remains armed across SOF", label), UVM_LOW)
    if (endpoint.direction == USB_DIRECTION_IN) fill_in_payload();
    else fill_endpoint_buffer(buffer_offset, transaction_count * transaction_bytes, 32'heeee_eeee);
    clear_endpoint_interrupt(endpoint);
    arm_endpoint(endpoint, transaction_count * transaction_bytes, buffer_offset, armed_entry);
    if (armed_entry.active !== 1'b1 || armed_entry.nbytes !== transaction_count * transaction_bytes) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s did not arm a complete three-packet descriptor", label))
    end

    service_chunk(endpoint, 0, prefix_packets, {label, " prefix"}, prefix_microframe);
    read_endpoint_entry(endpoint, partial_entry);
    check_interrupt_status(endpoint, 1'b0, {label, " before SOF"});
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      for (int unsigned index = 0; index < prefix_packets; index++) verify_out_transaction(index);
    end

    wait_for_microframe_after(prefix_microframe, {label, " SOF boundary"});
    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry !== partial_entry || observed_entry.active !== 1'b1 ||
        observed_entry.nbytes !== (transaction_count - prefix_packets) * transaction_bytes ||
        entry_buffer_byte_offset(observed_entry) !== buffer_offset + prefix_packets * transaction_bytes) begin
      `uvm_fatal("USB_HB_INTERRUPT",
                 $sformatf("%s descriptor changed at SOF: before=%s after=%s", label, describe_entry(partial_entry), describe_entry(observed_entry)))
    end
    check_interrupt_status(endpoint, 1'b0, {label, " after SOF"});

    service_chunk(endpoint, prefix_packets, transaction_count - prefix_packets, {label, " remainder"}, remainder_microframe);
    if (remainder_microframe <= prefix_microframe) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s remainder did not execute in a later microframe (%0d <= %0d)", label, remainder_microframe, prefix_microframe))
    end
    check_interrupt_status(endpoint, 1'b1, {label, " completed"});
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      for (int unsigned index = 0; index < transaction_count; index++) verify_out_transaction(index);
    end
    clear_endpoint_interrupt(endpoint);
    check_interrupt_status(endpoint, 1'b0, {label, " cleared"});
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s completed across uframes %0d -> %0d with VIP toggle/payload checks and zero residual", label, prefix_microframe, remainder_microframe), UVM_LOW)
  endtask

  // Enumerate and exercise high-bandwidth interrupt OUT and IN.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t entry;
    int unsigned total_bytes;
    int unsigned scheduled_microframe;

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
    service_chunk(
      out_endpoint,
      0,
      transaction_count,
      "High-bandwidth interrupt OUT service opportunity",
      scheduled_microframe
    );
    for (int unsigned transaction_index = 0; transaction_index < transaction_count; transaction_index++) begin
      verify_out_transaction(transaction_index);
    end
    check_interrupt_status(out_endpoint, 1'b1, "Clean interrupt OUT completed");

    fill_in_payload();
    arm_endpoint(in_endpoint, total_bytes, in_buffer, entry);
    clear_endpoint_interrupt(in_endpoint);
    service_chunk(
      in_endpoint,
      0,
      transaction_count,
      "High-bandwidth interrupt IN service opportunity",
      scheduled_microframe
    );
    check_interrupt_status(in_endpoint, 1'b1, "Clean interrupt IN completed");

    // Order 2+1 before 1+2 so both resumptions require DATA1 and svt_usb_protocol_ep_sc::data_toggle_check
    // detects any erroneous SOF reset to DATA0.
    partial_service_case(out_endpoint, 2);
    partial_service_case(out_endpoint, 1);
    partial_service_case(in_endpoint, 2);
    partial_service_case(in_endpoint, 1);

    completed = 1'b1;
    `uvm_info("USB_HB_INTERRUPT", "Clean IN/OUT bursts and all four partial-service SOF-boundary cases verified", UVM_LOW)
  endtask
endclass
