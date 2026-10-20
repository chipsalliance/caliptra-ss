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

// Verifies clean and SOF-interrupted three-transaction high-bandwidth
// isochronous OUT and IN service intervals using native Synopsys SVT USB VIP
// transfers and built-in VIP checking.
//
// Governing specifications and VIP documentation references (paths relative to
// $DOC_ROOT/class_ref/usb_svt_uvm_class_reference/html/):
//   - USB 2.0 Sections 5.6.4, 5.9.2, 5.12.6, 5.12.7, and 8.4.3:
//     High-bandwidth isochronous endpoints support up to three 1024-byte
//     transactions per 125 us microframe (OUT: MDATA, MDATA, DATA2; IN: DATA2,
//     DATA1, DATA0), never issue handshakes or retries, and abandon missing
//     transactions at the next microframe SOF.
//   - configuration/class_svt_usb_endpoint_configuration.html:
//     isoc_mult = ISOC_MULT_TWO (3 transactions per microframe) and
//     usb_20_isoc_without_first_last_transaction = 0 enable per-transaction
//     first_isoc_transaction / last_isoc_transaction framing on svt_usb_transfer.
//   - transaction/class_svt_usb_transfer.html:
//     ISOCHRONOUS_OUT_TRANSFER and ISOCHRONOUS_IN_TRANSFER scheduled into a
//     single microframe via start_uframe_bus_interval / end_uframe_bus_interval
//     use {first_isoc_transaction, last_isoc_transaction} = {1,0}, {0,0}, {0,1}
//     for the three transactions in a service interval.
//   - status/class_svt_usb_endpoint_status.html:
//     set_isoc_toggle_state(ISOC_TOGGLE_RESET) resets the host endpoint's
//     per-interval PID state after an intentionally incomplete microframe so
//     the next microframe restarts PID sequencing per USB 2.0 Section 5.9.2.
//   - protocolChecks.html, coverage/class_svt_usb_protocol_ep_sc.html,
//     coverage/class_svt_usb_protocol_sc.html, coverage/class_svt_usb_link_20_sc.html,
//     and coverage/class_svt_usb_physical_20_sc.html (all enabled by default via
//     register_default_chks = 1, enable_default_chks = 1):
//       * packet_error_check: checks PID check field, CRC5, CRC16, bitstuff,
//         and EOP framing on every packet.
//       * data_toggle_check: checks legal DATA0/DATA1/DATA2/MDATA PID sequencing.
//       * valid_device_data_check & isoc_received_more_bytes_than_expected:
//         checks IN payload size against wMaxPacketSize (1024) and transfer size.
//       * valid_device_response_check, valid_host_response_check, and
//         unexpected_response_check: verifies no handshakes occur on ISO traffic.
//       * sof_not_received_in_tmicroframeinterval, sof_not_rcvd_at_end_of_uframe,
//         unexpected_sof_rcvd, and received_unexpected_uframe_cnt: checks 125 us
//         HS SOF cadence and microframe/frame-number progression.
//       * rx_packet_routed_check & received_data_packet_check: verifies all
//         received packets are claimed by an active transfer and checks data.
//       * utmi_signal_X_Z_check, chk_utmi_byte_time, chk_utmi_packet_begin_hs,
//         chk_utmi_packet_end_hs, chk_utmi_sof_eop_invalid, chk_utmi_rxerror:
//         checks UTMI physical-layer signaling.
//
// Because the VIP enforces wire-level PID, CRC, framing, handshake absence, and
// SOF cadence checks automatically, this sequence checks only the device-side
// architectural state (DEV0 CSRs, endpoint descriptors, SRAM payload/guards,
// and EPSKIP firmware recovery for SOF-invalidated ISO OUT intervals) and the
// end-to-end payload bytes returned in completed ISO IN transfers.

class usb_high_bandwidth_iso_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_high_bandwidth_iso_host_seq)

  localparam int unsigned PACKET_BYTES = 1024;
  localparam int unsigned PACKETS_PER_INTERVAL = 3;

  usb_endpoint_cfg target_endpoint;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  int unsigned packet_count = PACKETS_PER_INTERVAL;
  logic [7:0] interval_base = 8'h10;
  logic [7:0] packet_stride = 8'h40;
  time transfer_timeout = 750us;
  string transfer_label = "High-bandwidth ISO";

  function new(string name = "usb_high_bandwidth_iso_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_HB_ISO_HOST";
  endfunction

  // Generate packet- and interval-distinct byte patterns.
  function logic [7:0] expected_byte(int unsigned byte_index);
    int unsigned packet_index;

    packet_index = byte_index / PACKET_BYTES;
    return interval_base + 8'(byte_index) + packet_stride * packet_index;
  endfunction

  // Wait for automatic host SOF generation to advance past target_microframe.
  task wait_for_microframe_end(int unsigned target_microframe);
    bit advanced;

    advanced = 1'b0;
    fork
      begin
        wait (shared_status.local_host_status.micro_frame_count > target_microframe);
        advanced = 1'b1;
      end
      begin
        #(transfer_timeout);
      end
    join_any
    disable fork;
    if (!advanced) begin
      `uvm_fatal(
        report_id(),
        $sformatf(
          "%s did not advance past microframe %0d within %0t (current=%0d)",
          transfer_label,
          target_microframe,
          transfer_timeout,
          shared_status.local_host_status.micro_frame_count
        )
      )
    end
  endtask

  // Schedule packet_count 1024-byte transactions in one microframe and wait for
  // the next automatic 125 us SOF to close the service interval.
  virtual task body();
    int unsigned target_microframe;
    bit [3:0] target_ep_number;
    svt_usb_transfer::transfer_type_enum expected_xfer_type;

    completed = 1'b0;
    if (target_endpoint == null ||
        target_endpoint.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS ||
        !target_endpoint.anchor_index_valid ||
        packet_count == 0 ||
        packet_count > PACKETS_PER_INTERVAL) begin
      `uvm_fatal(report_id(), "Require a valid anchored ISO endpoint and packet_count in 1..3")
    end

    resolve_host_context(1'b1);
    if (shared_status.local_host_status == null) begin
      `uvm_fatal(report_id(), "SVT local_host_status is unavailable")
    end
    target_microframe = shared_status.local_host_status.micro_frame_count + 2;
    target_ep_number = 4'(target_endpoint.ep_number);
    expected_xfer_type = (target_endpoint.direction == USB_DIRECTION_IN) ?
                         svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER :
                         svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;

    `uvm_info(
      report_id(),
      $sformatf(
        "%s scheduling %0d/%0d transactions on %s in microframe %0d",
        transfer_label,
        packet_count,
        PACKETS_PER_INTERVAL,
        target_endpoint.convert2string(),
        target_microframe
      ),
      UVM_LOW
    )

    for (int unsigned index = 0; index < packet_count; index++) begin
      svt_usb_transfer transfer;
      svt_usb_transfer observed_transfer;
      uvm_object completion;
      bit first_transaction;
      bit last_transaction;
      string reason;

      first_transaction = (index == 0);
      last_transaction = (index == (PACKETS_PER_INTERVAL - 1));
      transfer = svt_usb_transfer::type_id::create($sformatf("iso_xfer_%0d", index));
      begin_transfer_watch($sformatf("%s transaction %0d", transfer_label, index + 1), transfer_timeout);
      start_item(transfer, -1, p_sequencer.xfer_sequencer);
      transfer.cfg = usb_cfg;
      if (target_endpoint.direction == USB_DIRECTION_OUT) begin
        transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
        transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
      end
      transfer.reasonable_start_uframe_bus_interval.constraint_mode(0);
      transfer.reasonable_end_uframe_bus_interval.constraint_mode(0);
      transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
      if (!transfer.randomize() with {
            xfer_type == local::expected_xfer_type;
            device_address == local::device_address;
            endpoint_number == local::target_ep_number;
            payload_intended_byte_count == PACKET_BYTES;
            first_isoc_transaction == local::first_transaction;
            last_isoc_transaction == local::last_transaction;
            start_uframe_bus_interval == int'(local::target_microframe);
            end_uframe_bus_interval == int'(local::target_microframe);
            inter_transfer_delay_longint == 0;
          }) begin
        `uvm_fatal(report_id(), $sformatf("Unable to randomize %s transaction %0d", transfer_label, index))
      end
      if (target_endpoint.direction == USB_DIRECTION_OUT) begin
        for (int unsigned offset = 0; offset < PACKET_BYTES; offset++) begin
          transfer.payload.data[offset] = expected_byte(index * PACKET_BYTES + offset);
        end
      end
      finish_item(transfer);
      end_transfer_watch(completion);
      check_transfer_correlation($sformatf("%s transaction %0d", transfer_label, index + 1), transfer, completion);
      if (!cast_completed_transfer(completion, observed_transfer, reason)) begin
        `uvm_fatal(report_id(), $sformatf("%s transaction %0d rejected: %s", transfer_label, index + 1, reason))
      end
      if (observed_transfer.status !== svt_sequence_item::ACCEPT ||
          observed_transfer.results_status !== '0 ||
          observed_transfer.xfer_type !== expected_xfer_type ||
          observed_transfer.device_address !== device_address ||
          observed_transfer.endpoint_number !== target_ep_number ||
          observed_transfer.payload == null ||
          observed_transfer.payload.byte_count !== PACKET_BYTES) begin
        `uvm_fatal(
          report_id(),
          $sformatf(
            "%s transaction %0d completion mismatch: status=%s results=0x%0h type=%s addr=%0d ep=%0d bytes=%0d",
            transfer_label,
            index + 1,
            observed_transfer.status.name(),
            observed_transfer.results_status,
            observed_transfer.xfer_type.name(),
            observed_transfer.device_address,
            observed_transfer.endpoint_number,
            (observed_transfer.payload == null) ? -1 : observed_transfer.payload.byte_count
          )
        )
      end
      if (target_endpoint.direction == USB_DIRECTION_IN) begin
        for (int unsigned offset = 0; offset < PACKET_BYTES; offset++) begin
          logic [7:0] observed_byte;
          logic [7:0] expected;

          observed_byte = observed_transfer.payload.get_byte_val(offset);
          expected = expected_byte(index * PACKET_BYTES + offset);
          if (observed_byte !== expected) begin
            `uvm_fatal(
              report_id(),
              $sformatf(
                "%s packet %0d byte %0d is 0x%02h, expected 0x%02h",
                transfer_label,
                index,
                offset,
                observed_byte,
                expected
              )
            )
          end
        end
      end
    end

    wait_for_microframe_end(target_microframe);
    if (packet_count < PACKETS_PER_INTERVAL) begin
      shared_status.remote_device_status[0]
          .endpoint_status[target_endpoint.anchor_index]
          .set_isoc_toggle_state(svt_usb_endpoint_status::ISOC_TOGGLE_RESET);
    end
    completed = 1'b1;
    `uvm_info(
      report_id(),
      $sformatf(
        "%s completed %0d/%0d transactions in microframe %0d and observed next SOF",
        transfer_label,
        packet_count,
        PACKETS_PER_INTERVAL,
        target_microframe
      ),
      UVM_LOW
    )
  endtask
endclass

class usb_high_bandwidth_iso_seq extends usb_base_seq;
  `uvm_object_utils(usb_high_bandwidth_iso_seq)

  localparam int unsigned PACKET_BYTES = 1024;
  localparam int unsigned PACKETS_PER_INTERVAL = 3;
  localparam int unsigned INTERVAL_BYTES = PACKET_BYTES * PACKETS_PER_INTERVAL;
  localparam logic [3:0] ERROR_NONE = 4'h0;
  localparam logic [3:0] ERROR_PACKET_UNEXPECTED = 4'h3;
  localparam int unsigned GUARD_BYTES = 64;

  logic [31:0] out_guard_before = 32'h0000_0fc0;
  logic [31:0] out_buffer = 32'h0000_1000;
  logic [31:0] out_guard_after = 32'h0000_1c00;
  logic [31:0] in_buffer = 32'h0000_2000;
  logic [7:0] packet_stride = 8'h40;
  time transfer_timeout = 750us;
  bit completed;

  function new(string name = "usb_high_bandwidth_iso_seq");
    super.new(name);
  endfunction

  // Generate packet- and interval-distinct data.
  function logic [7:0] expected_byte(
    logic [7:0] interval_base,
    int unsigned byte_index
  );
    int unsigned packet_index;

    packet_index = byte_index / PACKET_BYTES;
    return interval_base + 8'(byte_index) + packet_stride * packet_index;
  endfunction

  // Fill one complete device-to-host service-interval buffer.
  task fill_in_payload(logic [7:0] interval_base);
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < INTERVAL_BYTES; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = expected_byte(interval_base, offset + lane);
      end
      write32(USB_DEV0_SRAM, in_buffer + offset, data_word);
    end
  endtask

  // Clear the global last-error field before one isolated interval.
  task clear_info_error();
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
  endtask

  // Poll INFO.ERR_CODE until the expected controller status is observed.
  task wait_for_info_error(
    string label,
    logic [3:0] expected_error
  );
    uvm_reg_field error_field;
    logic [31:0] info_value;
    logic [3:0] observed_error;
    realtime deadline;

    error_field = p_sequencer.reg_model.combo.dev0_csr.INFO.ERR_CODE;
    observed_error = 4'hx;
    deadline = $realtime + transfer_timeout;
    do begin
      ral_read32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, info_value);
      observed_error = 4'(
          (info_value & ral_field_mask(error_field)) >>
          error_field.get_lsb_pos());
      if (observed_error !== expected_error) #500ns;
    end while (
      observed_error !== expected_error &&
      $realtime < deadline
    );
    if (observed_error !== expected_error) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s INFO.ERR_CODE is 0x%0h, expected 0x%0h",
          label,
          observed_error,
          expected_error
        )
      )
    end
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "%s observed INFO.ERR_CODE=0x%0h",
        label,
        observed_error
      ),
      UVM_LOW
    )
  endtask

  // Check one fixed sentinel region around the OUT payload buffer.
  task verify_out_guard(
    string label,
    logic [31:0] guard_address,
    logic [31:0] guard_word
  );
    logic [31:0] observed_word;

    for (int unsigned offset = 0; offset < GUARD_BYTES; offset += 4) begin
      read32(USB_DEV0_SRAM, guard_address + offset, observed_word);
      if (observed_word !== guard_word) begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf(
            "%s guard changed at 0x%08h: data=0x%08h expected=0x%08h",
            label,
            guard_address + offset,
            observed_word,
            guard_word
          )
        )
      end
    end
  endtask

  // Verify the OUT payload bytes committed to packet memory.
  task verify_out_payload(
    string label,
    logic [7:0] interval_base,
    int unsigned byte_count
  );
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    for (int unsigned offset = 0; offset < byte_count; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = expected_byte(interval_base, offset + lane);
      end
      read32(USB_DEV0_SRAM, out_buffer + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf(
            "%s mismatch at offset 0x%04h: data=0x%08h expected=0x%08h",
            label,
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
    `uvm_info(
      "USB_HB_ISO",
      $sformatf("%s verified all %0d packet-distinct bytes", label, byte_count),
      UVM_LOW
    )
  endtask

  // Require unwritten bytes beyond an interrupted prefix to retain the sentinel.
  task verify_out_tail_sentinel(
    string label,
    int unsigned first_offset,
    logic [31:0] sentinel
  );
    logic [31:0] observed_word;

    for (int unsigned offset = first_offset; offset < INTERVAL_BYTES; offset += 4) begin
      read32(USB_DEV0_SRAM, out_buffer + offset, observed_word);
      if (observed_word !== sentinel) begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf(
            "%s wrote beyond its final packet at offset 0x%04h: data=0x%08h expected=0x%08h",
            label,
            offset,
            observed_word,
            sentinel
          )
        )
      end
    end
  endtask

  // Require the hardware ownership transition for a completed interval entry.
  task verify_interval_retired(
    usb_endpoint_cfg endpoint,
    string label,
    int unsigned expected_nbytes,
    logic [31:0] expected_buffer,
    bit check_buffer
  );
    usb_ep_entry_t entry;
    logic [31:0] interrupt_status;
    logic [31:0] interrupt_mask;
    realtime deadline;
    bit retired;

    deadline = $realtime + transfer_timeout;
    retired = 1'b0;
    do begin
      read_endpoint_entry(endpoint, entry);
      retired =
          entry.active === 1'b0 &&
          entry.nbytes === expected_nbytes &&
          (!check_buffer || entry_buffer_byte_offset(entry) === expected_buffer);
      if (!retired) #1us;
    end while (!retired && $realtime < deadline);
    if (!retired) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf("%s did not retire the interval: %s", label, describe_entry(entry))
      )
    end

    interrupt_mask = endpoint_intstat_mask(endpoint);
    ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);
    if ((interrupt_status & interrupt_mask) === 0) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s retired its descriptor without the required endpoint interrupt: entry=%s INTSTAT=0x%08h",
          label,
          describe_entry(entry),
          interrupt_status
        )
      )
    end
    clear_endpoint_interrupt(endpoint);
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "%s retired with Active=0 NBytes=%0d buffer=0x%08h",
        label,
        expected_nbytes,
        entry_buffer_byte_offset(entry)
      ),
      UVM_LOW
    )
  endtask

  // Execute the firmware recovery procedure for an ISO OUT interval that was
  // invalidated by SOF before its final transaction arrived: confirm the
  // descriptor stayed Active without asserting INTSTAT, then reclaim ownership
  // via EPSKIP so the endpoint can be re-armed for future intervals.
  task recover_invalidated_out_interval(
    usb_endpoint_cfg endpoint,
    usb_ep_entry_t armed_entry,
    string label
  );
    usb_ep_entry_t expected_entry;
    logic [31:0] interrupt_status;
    logic [31:0] interrupt_mask;

    #1us;
    check_endpoint_entry_writeback(
      endpoint,
      armed_entry,
      {label, " invalidated ISO OUT descriptor should remain active until firmware recovery"}
    );
    interrupt_mask = endpoint_intstat_mask(endpoint);
    ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);
    if ((interrupt_status & interrupt_mask) !== 0) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s asserted INTSTAT before firmware skip recovery: INTSTAT=0x%08h",
          label,
          interrupt_status
        )
      )
    end

    expected_entry = armed_entry;
    expected_entry.active = 1'b0;
    request_endpoint_skip(endpoint);
    wait_for_endpoint_skip_clear(endpoint, transfer_timeout);
    check_endpoint_entry_writeback(
      endpoint,
      expected_entry,
      {label, " EPSKIP recovery writeback mismatch"}
    );
    ral_read32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, interrupt_status);
    if ((interrupt_status & interrupt_mask) === 0) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s EPSKIP recovery did not assert INTSTAT: INTSTAT=0x%08h",
          label,
          interrupt_status
        )
      )
    end
    clear_endpoint_interrupt(endpoint);
    clear_info_error();
    `uvm_info(
      "USB_HB_ISO",
      $sformatf("%s recovered invalidated OUT buffer via EPSKIP: entry=%s", label, describe_entry(expected_entry)),
      UVM_LOW
    )
  endtask

  // Run one OUT service interval using SVT USB VIP transfers on xfer_sequencer.
  task run_out_interval(
    usb_endpoint_cfg endpoint,
    string label,
    logic [7:0] interval_base,
    int unsigned packet_count,
    logic [3:0] expected_error
  );
    usb_ep_entry_t armed_entry;
    usb_high_bandwidth_iso_host_seq host_sequence;
    logic [31:0] payload_sentinel;
    logic [31:0] guard_before_sentinel;
    logic [31:0] guard_after_sentinel;

    payload_sentinel = 32'heeee_eeee;
    guard_before_sentinel = 32'ha5a5_5a5a;
    guard_after_sentinel = 32'h5a5a_a5a5;
    fill_endpoint_buffer(out_guard_before, GUARD_BYTES, guard_before_sentinel);
    fill_endpoint_buffer(out_buffer, INTERVAL_BYTES, payload_sentinel);
    fill_endpoint_buffer(out_guard_after, GUARD_BYTES, guard_after_sentinel);
    clear_endpoint_interrupt(endpoint);
    clear_info_error();
    arm_endpoint(endpoint, INTERVAL_BYTES, out_buffer, armed_entry);

    host_sequence = usb_high_bandwidth_iso_host_seq::type_id::create("iso_out_host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.packet_count = packet_count;
    host_sequence.interval_base = interval_base;
    host_sequence.packet_stride = packet_stride;
    host_sequence.transfer_timeout = transfer_timeout;
    host_sequence.transfer_label = label;
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", $sformatf("%s host sequence did not complete", label))
    end

    wait_for_info_error(label, expected_error);
    verify_out_payload(label, interval_base, packet_count * PACKET_BYTES);
    verify_out_tail_sentinel(label, packet_count * PACKET_BYTES, payload_sentinel);
    verify_out_guard(label, out_guard_before, guard_before_sentinel);
    verify_out_guard(label, out_guard_after, guard_after_sentinel);

    if (expected_error == ERROR_NONE) begin
      verify_interval_retired(
        endpoint,
        label,
        INTERVAL_BYTES - packet_count * PACKET_BYTES,
        out_buffer + packet_count * PACKET_BYTES,
        1'b1
      );
    end else begin
      recover_invalidated_out_interval(endpoint, armed_entry, label);
    end
  endtask

  // Run one IN service interval using SVT USB VIP transfers on xfer_sequencer.
  task run_in_interval(
    usb_endpoint_cfg endpoint,
    string label,
    logic [7:0] interval_base,
    int unsigned packet_count,
    logic [3:0] expected_error
  );
    usb_ep_entry_t armed_entry;
    usb_high_bandwidth_iso_host_seq host_sequence;

    fill_in_payload(interval_base);
    clear_endpoint_interrupt(endpoint);
    clear_info_error();
    arm_endpoint(endpoint, INTERVAL_BYTES, in_buffer, armed_entry);

    host_sequence = usb_high_bandwidth_iso_host_seq::type_id::create("iso_in_host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.packet_count = packet_count;
    host_sequence.interval_base = interval_base;
    host_sequence.packet_stride = packet_stride;
    host_sequence.transfer_timeout = transfer_timeout;
    host_sequence.transfer_label = label;
    host_sequence.start(p_sequencer.host_sequencer);
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", $sformatf("%s host sequence did not complete", label))
    end

    wait_for_info_error(label, expected_error);
    verify_interval_retired(endpoint, label, 0, 32'h0, 1'b0);
  endtask

  // Enumerate, exercise clean and SOF-interrupted OUT intervals (with EPSKIP
  // firmware recovery), then exercise clean and SOF-interrupted IN intervals.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;

    completed = 1'b0;
    `uvm_info("USB_HB_ISO", "Starting VIP-driven high-bandwidth ISO scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", "Enumeration did not complete")
    end
    out_endpoint = get_endpoint(2, USB_DIRECTION_OUT);
    in_endpoint = get_endpoint(2, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list("High-bandwidth ISO OUT", out_buffer, INTERVAL_BYTES);
    check_buffer_clear_of_endpoint_list("High-bandwidth ISO IN", in_buffer, INTERVAL_BYTES);
    enable_endpoint_interrupt(out_endpoint);
    enable_endpoint_interrupt(in_endpoint);

    // Clean 3-packet OUT interval: MDATA, MDATA, DATA2.
    run_out_interval(out_endpoint, "Clean high-bandwidth ISO OUT", 8'h10, 3, ERROR_NONE);

    // Interrupted OUT intervals: 1 or 2 MDATAs followed by SOF, recovered via EPSKIP.
    run_out_interval(out_endpoint, "One-packet interrupted ISO OUT", 8'h30, 1, ERROR_PACKET_UNEXPECTED);
    run_out_interval(out_endpoint, "Fresh OUT interval after one-packet recovery", 8'h71, 3, ERROR_NONE);
    run_out_interval(out_endpoint, "Two-packet interrupted ISO OUT", 8'h40, 2, ERROR_PACKET_UNEXPECTED);
    run_out_interval(out_endpoint, "Fresh OUT interval after two-packet recovery", 8'hb0, 3, ERROR_NONE);

    // Clean and interrupted IN intervals: DATA2, DATA1, DATA0.
    run_in_interval(in_endpoint, "Clean high-bandwidth ISO IN", 8'h20, 3, ERROR_NONE);
    run_in_interval(in_endpoint, "One-packet interrupted ISO IN", 8'h30, 1, ERROR_PACKET_UNEXPECTED);
    run_in_interval(in_endpoint, "Fresh IN interval after one-packet loss", 8'h71, 3, ERROR_NONE);
    run_in_interval(in_endpoint, "Two-packet interrupted ISO IN", 8'h40, 2, ERROR_PACKET_UNEXPECTED);
    run_in_interval(in_endpoint, "Fresh IN interval after two-packet loss", 8'hb0, 3, ERROR_NONE);

    completed = 1'b1;
    `uvm_info(
      "USB_HB_ISO",
      "Clean and SOF-interrupted high-bandwidth ISO OUT/IN intervals completed with VIP checking and firmware recovery",
      UVM_LOW
    )
  endtask
endclass
