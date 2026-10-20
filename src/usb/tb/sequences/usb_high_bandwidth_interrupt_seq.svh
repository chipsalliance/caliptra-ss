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

// Checks clean interrupt bursts and partial descriptors retained across SOF.
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

  // Wait for the endpoint writeback after one transaction.
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

  task align_service_opportunity(string label);
    bit observed;

    p_sequencer.packet_monitor.start_window(label);
    p_sequencer.packet_monitor.wait_for_sof(transfer_timeout, observed);
    if (!observed) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s did not observe a fresh SOF", label))
    end
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s aligned to a fresh SOF", label), UVM_LOW)
  endtask

  // USB 2.0 Section 5.9: the burst must fit one high-speed microframe,
  // independently of when software finishes checking descriptor progress.
  function void check_service_opportunity(
    string label,
    usb2_phy_packet_snapshot packets[$],
    realtime transfer_completed_at
  );
    usb_packet_monitor_callback::usb_packet_record_t records[$];
    int unsigned service_sof;
    int unsigned completion_sof;

    if (packets.size() != transaction_count) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s observed %0d packets, expected %0d", label, packets.size(), transaction_count))
    end
    p_sequencer.packet_monitor.get_records(records);
    service_sof = 0;
    completion_sof = 0;
    foreach (packets[index]) begin
      int unsigned start_sof;
      int unsigned end_sof;

      start_sof = 0;
      end_sof = 0;
      foreach (records[record_index]) begin
        if (records[record_index].direction == usb_packet_monitor_callback::USB_PACKET_TX &&
            records[record_index].pid_name == svt_usb_packet::SOF) begin
          if (records[record_index].observed_at <= packets[index].observed_at) start_sof++;
          if (records[record_index].observed_at <= packets[index].completed_at) end_sof++;
          if (index == 0 && records[record_index].observed_at <= transfer_completed_at) completion_sof++;
        end
      end
      if (index == 0) service_sof = start_sof;
      if (service_sof == 0 || start_sof != service_sof || end_sof != service_sof) begin
        `uvm_fatal(
          "USB_HB_INTERRUPT",
          $sformatf("%s packet %0d crosses service opportunities: first=%0d start=%0d end=%0d SOP=%0t EOP=%0t",
                    label, index, service_sof, start_sof, end_sof,
                    packets[index].observed_at, packets[index].completed_at)
        )
      end
      `uvm_info(
        "USB_HB_INTERRUPT",
        $sformatf("%s packet %0d in SOF window %0d: SOP=%0t EOP=%0t",
                  label, index, service_sof, packets[index].observed_at, packets[index].completed_at),
        UVM_LOW
      )
    end
    if (completion_sof != service_sof) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s completion crossed a SOF: packets=%0d completion=%0d", label, service_sof, completion_sof))
    end
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s: all %0d transactions completed in one service opportunity", label, packets.size()), UVM_LOW)
  endfunction

  // Correlate the public link records with full physical DATA snapshots.
  // USB 2.0 5.9.1 and December 2000 errata: interrupt uses DATA0/DATA1, not ISO sequencing.
  function void check_interrupt_trace(
    usb_endpoint_cfg endpoint,
    string label,
    usb2_phy_packet_snapshot packets[$],
    int unsigned first_transaction,
    int unsigned expected_packets,
    logic [7:0] first_pid,
    realtime transfer_completed_at
  );
    usb_packet_monitor_callback::usb_packet_record_t records[$];
    bit from_device;
    int unsigned stage;
    int unsigned accepted;
    int unsigned sof_count;
    int unsigned service_sof;
    int unsigned completion_sof;
    int unsigned packet_start_sof;
    int unsigned packet_end_sof;
    usb_packet_monitor_callback::usb_packet_direction_e data_direction;
    usb_packet_monitor_callback::usb_packet_direction_e ack_direction;
    logic [7:0] expected_pid;
    logic [7:0] expected_byte;
    logic [7:0] payload_base;

    from_device = endpoint.direction == USB_DIRECTION_IN;
    data_direction = from_device ? usb_packet_monitor_callback::USB_PACKET_RX : usb_packet_monitor_callback::USB_PACKET_TX;
    ack_direction = from_device ? usb_packet_monitor_callback::USB_PACKET_TX : usb_packet_monitor_callback::USB_PACKET_RX;
    payload_base = from_device ? in_payload_base : out_payload_base;
    if (packets.size() != expected_packets || expected_packets == 0 || !(first_pid inside {8'hc3, 8'h4b})) begin
      `uvm_fatal("USB_HB_INTERRUPT",
                 $sformatf("%s invalid DATA count/PID: count=%0d expected=%0d first_PID=%02h", label, packets.size(), expected_packets, first_pid))
    end
    stage = 0;
    accepted = 0;
    sof_count = 0;
    service_sof = 0;
    completion_sof = 0;
    expected_pid = first_pid;
    p_sequencer.packet_monitor.get_records(records);
    foreach (records[index]) begin
      if (records[index].direction === usb_packet_monitor_callback::USB_PACKET_TX &&
          records[index].pid_name === svt_usb_packet::SOF) begin
        if (stage != 0) begin
          `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s SOF interrupted token/DATA/ACK at stage %0d", label, stage))
        end
        sof_count++;
        if (records[index].observed_at <= transfer_completed_at) completion_sof++;
        continue;
      end
      case (stage)
        0: begin
          if (accepted >= expected_packets ||
              records[index].direction !== usb_packet_monitor_callback::USB_PACKET_TX ||
              records[index].pid_name !== (from_device ? svt_usb_packet::IN : svt_usb_packet::OUT) ||
              records[index].device_address !== p_sequencer.cfg.device_address ||
              records[index].endpoint_number !== 4'(endpoint.ep_number)) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s unexpected token/extra traffic at record %0d", label, index))
          end
          if (accepted == 0) service_sof = sof_count;
          if (service_sof == 0 || sof_count != service_sof) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s chunk not confined to one observed service period", label))
          end
          stage = 1;
        end
        1: begin
          if (records[index].direction !== data_direction ||
              records[index].pid_name !== (expected_pid === 8'hc3 ? svt_usb_packet::DATA0 : svt_usb_packet::DATA1) ||
              records[index].data_length !== transaction_bytes) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s DATA direction/PID/length mismatch for packet %0d", label, accepted))
          end
          if (packets[accepted] == null) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s missing physical DATA snapshot %0d", label, accepted))
          end
          if (packets[accepted].bytes.size() != transaction_bytes + 3 ||
              packets[accepted].bytes[0] !== expected_pid ||
              packets[accepted].observed_at >= packets[accepted].completed_at ||
              packets[accepted].completed_at > transfer_completed_at ||
              (accepted != 0 && packets[accepted].observed_at <= packets[accepted-1].completed_at)) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s physical DATA size/PID/order mismatch for packet %0d", label, accepted))
          end
          packet_start_sof = 0;
          packet_end_sof = 0;
          foreach (records[sof_index]) begin
            if (records[sof_index].direction === usb_packet_monitor_callback::USB_PACKET_TX &&
                records[sof_index].pid_name === svt_usb_packet::SOF) begin
              if (records[sof_index].observed_at <= packets[accepted].observed_at) packet_start_sof++;
              if (records[sof_index].observed_at <= packets[accepted].completed_at) packet_end_sof++;
            end
          end
          if (packet_start_sof != service_sof || packet_end_sof != service_sof) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s physical DATA %0d outside token service period", label, accepted))
          end
          for (int unsigned byte_index = 0; byte_index < transaction_bytes; byte_index++) begin
            expected_byte = payload_base + (first_transaction + accepted) * transaction_bytes +
                            byte_index + first_transaction + accepted;
            if (packets[accepted].bytes[byte_index + 1] !== expected_byte) begin
              `uvm_fatal("USB_HB_INTERRUPT",
                         $sformatf("%s packet %0d byte %0d=%02h expected=%02h",
                                   label, first_transaction + accepted, byte_index, packets[accepted].bytes[byte_index + 1], expected_byte))
            end
          end
          stage = 2;
        end
        2: begin
          if (records[index].direction !== ack_direction ||
              records[index].pid_name !== svt_usb_packet::ACK) begin
            `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s packet %0d missing accepting ACK", label, accepted))
          end
          accepted++;
          expected_pid = expected_pid === 8'hc3 ? 8'h4b : 8'hc3;
          stage = 0;
        end
        default: `uvm_fatal("USB_HB_INTERRUPT", "Invalid directed interrupt trace state")
      endcase
    end
    if (stage != 0 || accepted != expected_packets || completion_sof != service_sof) begin
      `uvm_fatal("USB_HB_INTERRUPT",
                 $sformatf("%s incomplete/late trace: stage=%0d accepted=%0d/%0d SOF=%0d completion_SOF=%0d",
                           label, stage, accepted, expected_packets, service_sof, completion_sof))
    end
    `uvm_info("USB_HB_INTERRUPT",
              $sformatf("%s verified %0d token/DATA/ACK transactions and all payload bytes; first_PID=%02h SOF=%0d",
                        label, accepted, first_pid, service_sof), UVM_LOW)
  endfunction

  // Check the endpoint's completion status without disturbing other endpoints.
  // Controller programming guide 4.2/4.2.3 and integration guide 4.2.2.9: completion clears Active and sets INTSTAT.
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

  // Service a native VIP transfer chunk; reuse its correlation, timeout, and payload checks.
  task service_chunk(
    usb_endpoint_cfg endpoint,
    int unsigned first_transaction,
    int unsigned packet_count,
    logic [7:0] first_pid,
    string label
  );
    usb_interrupt_host_seq host_sequence;
    usb2_phy_packet_snapshot packet;
    usb2_phy_packet_snapshot packets[$];
    realtime transfer_completed_at;

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
    transfer_completed_at = $realtime;
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s host transfer returned incomplete", label))
    end
    for (int unsigned index = 0; index < packet_count; index++) begin
      p_sequencer.physical_monitor.wait_for_data_packet(endpoint.direction == USB_DIRECTION_IN, transfer_timeout, packet);
      packets.push_back(packet);
    end
    // Descriptor readback also lets the final handshake observation drain before closing the window.
    wait_for_progress(endpoint, first_transaction + packet_count,
                      endpoint.direction == USB_DIRECTION_IN ? in_buffer : out_buffer, label);
    p_sequencer.packet_monitor.stop_window();
    check_interrupt_trace(endpoint, label, packets, first_transaction, packet_count, first_pid, transfer_completed_at);
  endtask

  // Deliberately incomplete host service is a negative scheduling stress, not a compliant bandwidth schedule.
  // USB 2.0 5.9.1 limits normal under-service; the device must nevertheless retain its unfinished interrupt buffer.
  task partial_service_case(usb_endpoint_cfg endpoint, int unsigned prefix_packets, logic [7:0] first_pid);
    usb_ep_entry_t armed_entry;
    usb_ep_entry_t partial_entry;
    usb_ep_entry_t observed_entry;
    logic [31:0] buffer_offset;
    logic [7:0] resume_pid;
    string label;
    bit sof_observed;
    usb_packet_monitor_callback::usb_packet_record_t boundary_records[$];
    realtime boundary_started_at;

    if (transaction_count != 3 || !(prefix_packets inside {1, 2})) begin
      `uvm_fatal("USB_HB_INTERRUPT", "Partial service requires a three-packet descriptor and one-/two-packet prefix")
    end
    label = $sformatf("Interrupt %s partial-service stress %0d+%0d",
                      endpoint.direction == USB_DIRECTION_IN ? "IN" : "OUT", prefix_packets, transaction_count - prefix_packets);
    buffer_offset = endpoint.direction == USB_DIRECTION_IN ? in_buffer : out_buffer;
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s starting; first_PID=%02h, descriptor remains armed across SOF", label, first_pid), UVM_LOW)
    if (endpoint.direction == USB_DIRECTION_IN) fill_in_payload();
    else fill_endpoint_buffer(buffer_offset, transaction_count * transaction_bytes, 32'heeee_eeee);
    clear_endpoint_interrupt(endpoint);
    arm_endpoint(endpoint, transaction_count * transaction_bytes, buffer_offset, armed_entry);
    if (armed_entry.active !== 1'b1 || armed_entry.nbytes !== transaction_count * transaction_bytes) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s did not arm a complete three-packet descriptor", label))
    end
    p_sequencer.physical_monitor.clear_packets();
    align_service_opportunity({label, " prefix"});
    service_chunk(endpoint, 0, prefix_packets, first_pid, {label, " prefix"});
    read_endpoint_entry(endpoint, partial_entry);
    check_interrupt_status(endpoint, 1'b0, {label, " before SOF"});
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      for (int unsigned index = 0; index < prefix_packets; index++) verify_out_transaction(index);
    end

    // A separate window resets the SOF latch without cancelling any inherited VIP worker.
    p_sequencer.packet_monitor.start_window({label, " retained boundary"});
    boundary_started_at = $realtime;
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s waiting for fresh SOF with residual=%0d", label, partial_entry.nbytes), UVM_LOW)
    p_sequencer.packet_monitor.wait_for_sof(transfer_timeout, sof_observed);
    if (!sof_observed) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s missing intervening SOF", label))
    end
    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry !== partial_entry || observed_entry.active !== 1'b1 ||
        observed_entry.nbytes !== (transaction_count - prefix_packets) * transaction_bytes ||
        entry_buffer_byte_offset(observed_entry) !== buffer_offset + prefix_packets * transaction_bytes) begin
      `uvm_fatal("USB_HB_INTERRUPT",
                 $sformatf("%s descriptor changed at SOF: before=%s after=%s", label, describe_entry(partial_entry), describe_entry(observed_entry)))
    end
    check_interrupt_status(endpoint, 1'b0, {label, " after SOF"});
    p_sequencer.packet_monitor.stop_window();
    p_sequencer.packet_monitor.get_records(boundary_records);
    if (boundary_records.size() == 0) begin
      `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s boundary window was a no-op", label))
    end
    foreach (boundary_records[index]) begin
      if (boundary_records[index].direction !== usb_packet_monitor_callback::USB_PACKET_TX ||
          boundary_records[index].pid_name !== svt_usb_packet::SOF ||
          boundary_records[index].observed_at <= boundary_started_at) begin
        `uvm_fatal("USB_HB_INTERRUPT", $sformatf("%s unexpected traffic or stale SOF while service withheld", label))
      end
    end
    `uvm_info("USB_HB_INTERRUPT",
              $sformatf("%s retained active descriptor across %0d observed SOF(s); resuming without rearm", label, boundary_records.size()), UVM_LOW)
    resume_pid = prefix_packets[0] ? (first_pid === 8'hc3 ? 8'h4b : 8'hc3) : first_pid;
    align_service_opportunity({label, " remainder"});
    service_chunk(endpoint, prefix_packets, transaction_count - prefix_packets, resume_pid, {label, " remainder"});
    check_interrupt_status(endpoint, 1'b1, {label, " completed"});
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      for (int unsigned index = 0; index < transaction_count; index++) verify_out_transaction(index);
    end
    clear_endpoint_interrupt(endpoint);
    check_interrupt_status(endpoint, 1'b0, {label, " cleared"});
    `uvm_info("USB_HB_INTERRUPT", $sformatf("%s completed with retained payload/PID continuity and zero residual", label), UVM_LOW)
  endtask

  // Enumerate and exercise high-bandwidth interrupt OUT and IN.
  virtual task body();
    usb_init_seq init_sequence;
    usb_interrupt_host_seq host_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;
    usb_ep_entry_t entry;
    usb2_phy_packet_snapshot observed_packet;
    usb2_phy_packet_snapshot observed_packets[$];
    realtime transfer_completed_at;
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
    p_sequencer.physical_monitor.clear_packets();
    host_sequence =
        usb_interrupt_host_seq::type_id::create("out_host_sequence");
    host_sequence.target_endpoint = out_endpoint;
    host_sequence.payload_byte_count = total_bytes;
    host_sequence.payload_base = out_payload_base;
    host_sequence.payload_packet_bytes = transaction_bytes;
    host_sequence.payload_packet_stride = 1;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label =
        "High-bandwidth interrupt OUT service opportunity";
    align_service_opportunity(host_sequence.transfer_label);
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        transfer_completed_at = $realtime;
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_HB_INTERRUPT", "Interrupt OUT host sequence returned incomplete")
        end
      end
      begin
        for (int unsigned transaction_index = 0;
             transaction_index < transaction_count;
             transaction_index++) begin
          p_sequencer.physical_monitor.wait_for_data_packet(
              1'b0, transfer_timeout, observed_packet);
          if (observed_packet.bytes.size() != transaction_bytes + 3) begin
            `uvm_fatal("USB_HB_INTERRUPT", "VIP observed an incorrectly sized OUT packet")
          end
          observed_packets.push_back(observed_packet);
          wait_for_progress(
              out_endpoint,
              transaction_index + 1,
              out_buffer,
              "Interrupt OUT");
          verify_out_transaction(transaction_index);
        end
      end
    join
    p_sequencer.packet_monitor.stop_window();
    check_service_opportunity(host_sequence.transfer_label, observed_packets, transfer_completed_at);
    check_interrupt_trace(out_endpoint, host_sequence.transfer_label, observed_packets, 0, transaction_count, 8'hc3, transfer_completed_at);
    check_interrupt_status(out_endpoint, 1'b1, "Clean interrupt OUT completed");

    fill_in_payload();
    arm_endpoint(in_endpoint, total_bytes, in_buffer, entry);
    clear_endpoint_interrupt(in_endpoint);
    p_sequencer.physical_monitor.clear_packets();
    observed_packets.delete();
    host_sequence =
        usb_interrupt_host_seq::type_id::create("in_host_sequence");
    host_sequence.target_endpoint = in_endpoint;
    host_sequence.payload_byte_count = total_bytes;
    host_sequence.payload_base = in_payload_base;
    host_sequence.payload_packet_bytes = transaction_bytes;
    host_sequence.payload_packet_stride = 1;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.transfer_label =
        "High-bandwidth interrupt IN service opportunity";
    align_service_opportunity(host_sequence.transfer_label);
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        transfer_completed_at = $realtime;
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_HB_INTERRUPT", "Interrupt IN host sequence returned incomplete")
        end
      end
      begin
        for (int unsigned transaction_index = 0;
             transaction_index < transaction_count;
             transaction_index++) begin
          p_sequencer.physical_monitor.wait_for_data_packet(
              1'b1, transfer_timeout, observed_packet);
          if (observed_packet.bytes.size() != transaction_bytes + 3) begin
            `uvm_fatal("USB_HB_INTERRUPT", "VIP observed an incorrectly sized IN packet")
          end
          observed_packets.push_back(observed_packet);
          wait_for_progress(
              in_endpoint,
              transaction_index + 1,
              in_buffer,
              "Interrupt IN");
        end
      end
    join
    p_sequencer.packet_monitor.stop_window();
    check_service_opportunity(host_sequence.transfer_label, observed_packets, transfer_completed_at);
    check_interrupt_trace(in_endpoint, host_sequence.transfer_label, observed_packets, 0, transaction_count, 8'hc3, transfer_completed_at);
    check_interrupt_status(in_endpoint, 1'b1, "Clean interrupt IN completed");

    // Order 2+1 before 1+2 so both resumptions require DATA1 and detect an erroneous SOF reset to DATA0.
    // Each three-packet descriptor flips the next expected PID, including across descriptor rearms.
    partial_service_case(out_endpoint, 2, 8'h4b);
    partial_service_case(out_endpoint, 1, 8'hc3);
    partial_service_case(in_endpoint, 2, 8'h4b);
    partial_service_case(in_endpoint, 1, 8'hc3);

    completed = 1'b1;
    `uvm_info("USB_HB_INTERRUPT", "Clean IN/OUT bursts and all four partial-service SOF-boundary cases verified", UVM_LOW)
  endtask
endclass
