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

// Verifies clean and SOF-interrupted three-transaction ISO service intervals.
// USB 2.0 Sections 5.6.5, 5.9.2, 5.12.6, and 5.12.7 require missing
// transactions to be abandoned, PID sequencing to restart next microframe,
// and the time-correlated data stream to advance without retry. Descriptor
// retirement is the controller-specific mapping for one interval per entry.
class usb_high_bandwidth_iso_seq extends usb_base_seq;
  `uvm_object_utils(usb_high_bandwidth_iso_seq)

  localparam int unsigned PACKET_BYTES = 1024;
  localparam int unsigned PACKETS_PER_INTERVAL = 3;
  localparam int unsigned INTERVAL_BYTES =
      PACKET_BYTES * PACKETS_PER_INTERVAL;
  localparam time HS_MICROFRAME_PERIOD = 125us;
  localparam logic [3:0] ERROR_NONE = 4'h0;
  localparam logic [3:0] ERROR_PACKET_UNEXPECTED = 4'h3;
  localparam int unsigned GUARD_BYTES = 64;

  logic [31:0] out_guard_before = 32'h0000_0fc0;
  logic [31:0] out_buffer = 32'h0000_1000;
  logic [31:0] out_guard_after = 32'h0000_1c00;
  logic [31:0] in_buffer = 32'h0000_2000;
  logic [7:0] packet_stride = 8'h40;
  time transfer_timeout = 750us;
  time endpoint_ready_delay = 10us;
  time tx_ready_delay = 1us;
  time inter_transaction_delay = 1us;
  time interval_end_delay = 1us;
  logic [10:0] next_frame_number;
  logic [2:0] next_microframe_index;
  realtime last_raw_packet_start;
  realtime last_sof_start;
  bit sof_started;
  bit run_interrupted_out_acceptance;
  bit completed;

  function new(string name = "usb_high_bandwidth_iso_seq");
    super.new(name);
    next_frame_number = 0;
    next_microframe_index = 0;
    last_raw_packet_start = 0;
    last_sof_start = 0;
    sof_started = 1'b0;
  endfunction

  // Generate packet- and interval-distinct data.
  function logic [7:0] expected_byte(
    logic [7:0] interval_base,
    int unsigned byte_index
  );
    int unsigned packet_index;

    packet_index = byte_index / PACKET_BYTES;
    return interval_base + 8'(byte_index) +
           packet_stride * packet_index;
  endfunction

  // Fill one complete device-to-host service-interval buffer.
  task fill_in_payload(logic [7:0] interval_base);
    logic [31:0] data_word;

    for (int unsigned offset = 0; offset < INTERVAL_BYTES; offset += 4) begin
      data_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] =
            expected_byte(interval_base, offset + lane);
      end
      write32(USB_DEV0_SRAM, in_buffer + offset, data_word);
    end
  endtask

  // Stop periodic SOFs so each interval boundary is controlled by this test.
  task stop_sof_generation();
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;

    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer
    );
    `uvm_info("USB_HB_ISO", "Stopped automatic SOF generation", UVM_LOW)
  endtask

  // Restart ordinary host SOFs after all controlled intervals complete.
  task start_sof_generation();
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;

    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer
    );
    `uvm_info("USB_HB_ISO", "Restarted automatic SOF generation", UVM_LOW)
  endtask

  // Calculate the USB CRC5 token field in packed token-bit order.
  function logic [4:0] usb_crc5(logic [10:0] protected_bits);
    logic [4:0] crc;
    logic [4:0] inverted_crc;
    logic feedback;
    logic [4:0] packed_crc;

    crc = 5'h1f;
    for (int unsigned bit_index = 0; bit_index < 11; bit_index++) begin
      feedback = crc[4] ^ protected_bits[bit_index];
      crc = {crc[3:0], 1'b0};
      if (feedback) crc ^= 5'h05;
    end
    inverted_crc = ~crc;
    for (int unsigned bit_index = 0; bit_index < 5; bit_index++) begin
      packed_crc[bit_index] = inverted_crc[4-bit_index];
    end
    return packed_crc;
  endfunction

  // Drive one complete host packet through the testbench-owned UTMI path.
  task inject_raw_rx_packet(byte unsigned packet_bytes[$]);
    if (packet_bytes.size() == 0) begin
      `uvm_fatal("USB_HB_ISO", "Cannot inject an empty UTMI packet")
    end
    @(negedge p_sequencer.ctrl_vif.utmi_clk);
    last_raw_packet_start = $realtime;
    p_sequencer.ctrl_vif.raw_utmi_inject_enable <= 1'b1;
    p_sequencer.ctrl_vif.raw_utmi_rxactive <= 1'b1;
    p_sequencer.ctrl_vif.raw_utmi_rxvalid <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxerror <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxdata <= packet_bytes[0];
    @(negedge p_sequencer.ctrl_vif.utmi_clk);
    p_sequencer.ctrl_vif.raw_utmi_rxvalid <= 1'b1;
    @(negedge p_sequencer.ctrl_vif.utmi_clk);
    for (int unsigned byte_index = 1;
         byte_index < packet_bytes.size();
         byte_index++) begin
      p_sequencer.ctrl_vif.raw_utmi_rxdata <= packet_bytes[byte_index];
      @(negedge p_sequencer.ctrl_vif.utmi_clk);
    end
    p_sequencer.ctrl_vif.raw_utmi_rxvalid <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxactive <= 1'b0;
    p_sequencer.ctrl_vif.raw_utmi_rxdata <= 8'h00;
    @(negedge p_sequencer.ctrl_vif.utmi_clk);
    p_sequencer.ctrl_vif.raw_utmi_inject_enable <= 1'b0;
  endtask

  // Inject the next valid SOF at the high-speed 125 us cadence.
  task inject_sof();
    byte unsigned packet_bytes[$];
    logic [15:0] token_bits;
    logic [10:0] frame_number;
    logic [2:0] microframe_index;
    realtime next_sof_start;

    if (sof_started) begin
      next_sof_start = last_sof_start + HS_MICROFRAME_PERIOD;
      if ($realtime < next_sof_start) #(next_sof_start - $realtime);
    end
    frame_number = next_frame_number;
    microframe_index = next_microframe_index;
    token_bits = {usb_crc5(frame_number), frame_number};
    packet_bytes.push_back(8'ha5);
    packet_bytes.push_back(token_bits[7:0]);
    packet_bytes.push_back(token_bits[15:8]);
    inject_raw_rx_packet(packet_bytes);
    last_sof_start = last_raw_packet_start;
    sof_started = 1'b1;
    if (next_microframe_index == 7) begin
      next_microframe_index = 0;
      next_frame_number++;
    end else begin
      next_microframe_index++;
    end
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "Injected valid SOF frame %0d microframe %0d at %0t",
        frame_number,
        microframe_index,
        last_sof_start
      ),
      UVM_LOW
    )
  endtask

  // Inject one EP2 IN token for the enumerated device address 1.
  task inject_in_token();
    byte unsigned packet_bytes[$];

    if (p_sequencer.cfg.device_address != 1) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "Raw EP2 IN token encoding requires device address 1, configured=%0d",
          p_sequencer.cfg.device_address
        )
      )
    end
    packet_bytes.push_back(8'h69);
    packet_bytes.push_back(8'h01);
    packet_bytes.push_back(8'hc1);
    inject_raw_rx_packet(packet_bytes);
  endtask

  // Inject one EP2 OUT token for the enumerated device address 1.
  task inject_out_token();
    byte unsigned packet_bytes[$];

    if (p_sequencer.cfg.device_address != 1) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "Raw EP2 OUT token encoding requires device address 1, configured=%0d",
          p_sequencer.cfg.device_address
        )
      )
    end
    packet_bytes.push_back(8'he1);
    packet_bytes.push_back(8'h01);
    packet_bytes.push_back(8'hc1);
    inject_raw_rx_packet(packet_bytes);
  endtask

  // Calculate the USB CRC16 transmitted after one data payload.
  function logic [15:0] usb_crc16(
    byte unsigned bytes[$],
    int unsigned first,
    int unsigned count
  );
    logic [15:0] crc;
    logic feedback;
    byte unsigned data_byte;

    crc = 16'hffff;
    for (int unsigned index = 0; index < count; index++) begin
      data_byte = bytes[first + index];
      repeat (8) begin
        feedback = crc[0] ^ data_byte[0];
        crc >>= 1;
        if (feedback) crc ^= 16'ha001;
        data_byte >>= 1;
      end
    end
    return ~crc;
  endfunction

  // Return the legal high-bandwidth ISO OUT PID for one transaction.
  function logic [7:0] expected_out_pid(
    int unsigned transaction_count,
    int unsigned packet_index
  );
    case (transaction_count)
      1: return 8'hc3;
      2: return packet_index == 0 ? 8'h0f : 8'h4b;
      3: return packet_index < 2 ? 8'h0f : 8'h87;
      default: begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf(
            "Unsupported ISO OUT transaction count %0d",
            transaction_count
          )
        )
        return 8'hxx;
      end
    endcase
  endfunction

  // Clear the global last-error field before one isolated interval.
  task clear_info_error();
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
  endtask

  // Require the expected controller error before starting later USB traffic.
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
        "%s observed INFO.ERR_CODE=0x%0h before subsequent traffic",
        label,
        observed_error
      ),
      UVM_LOW
    )
  endtask

  // Count actual endpoint descriptor writes at the packet-memory boundary.
  task count_endpoint_writebacks(
    usb_endpoint_cfg endpoint,
    ref bit stop_monitor,
    output int unsigned writeback_count
  );
    logic [31:0] expected_word_address;

    expected_word_address = endpoint_entry_address(endpoint) >> 3;
    writeback_count = 0;
    do begin
      @(posedge p_sequencer.ctrl_vif.clk);
      if (p_sequencer.ctrl_vif.dev0_memory_write &&
          p_sequencer.ctrl_vif.dev0_memory_address ===
              expected_word_address) begin
        writeback_count++;
      end
    end while (!stop_monitor);
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

  // Request one IN packet and return the passive UTMI reconstruction.
  task request_in_packet(
    string label,
    output usb_utmi_packet packet
  );
    uvm_event tx_packet_event;
    uvm_object observed_object;
    bit packet_seen;
    bit wait_expired;

    tx_packet_event =
        uvm_event_pool::get_global(USB_UTMI_TX_PACKET_EVENT);
    tx_packet_event.reset();
    packet_seen = 1'b0;
    wait_expired = 1'b0;
    fork
      begin
        fork
          begin
            tx_packet_event.wait_trigger_data(observed_object);
            packet_seen = 1'b1;
          end
          begin
            #(transfer_timeout);
            wait_expired = 1'b1;
          end
        join_none
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b0;
        inject_in_token();
        #(tx_ready_delay);
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b1;
        wait (packet_seen || wait_expired);
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b0;
        disable fork;
      end
    join
    if (!packet_seen) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf("%s did not receive a DUT packet within %0t", label, transfer_timeout)
      )
    end
    if (!$cast(packet, observed_object)) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf("%s event carried an unexpected object type", label)
      )
    end
  endtask

  // Check one 1024-byte data packet's PID, payload, and CRC16.
  function void check_data_packet(
    usb_utmi_packet packet,
    string label,
    logic [7:0] expected_pid,
    logic [7:0] interval_base,
    int unsigned packet_index
  );
    logic [15:0] expected_crc;
    logic [15:0] observed_crc;

    if (packet == null || packet.bytes.size() != PACKET_BYTES + 3) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s packet %0d has %0d bytes, expected %0d",
          label,
          packet_index,
          (packet == null) ? 0 : packet.bytes.size(),
          PACKET_BYTES + 3
        )
      )
    end
    if (packet.bytes[0] !== expected_pid) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s packet %0d PID is 0x%02h, expected 0x%02h",
          label,
          packet_index,
          packet.bytes[0],
          expected_pid
        )
      )
    end
    for (int unsigned offset = 0; offset < PACKET_BYTES; offset++) begin
      logic [7:0] expected;

      expected = expected_byte(
          interval_base,
          packet_index * PACKET_BYTES + offset);
      if (packet.bytes[offset + 1] !== expected) begin
        `uvm_fatal(
          "USB_HB_ISO",
          $sformatf(
            "%s packet %0d byte %0d is 0x%02h, expected 0x%02h",
            label,
            packet_index,
            offset,
            packet.bytes[offset + 1],
            expected
          )
        )
      end
    end
    expected_crc = usb_crc16(packet.bytes, 1, PACKET_BYTES);
    observed_crc = {
      packet.bytes[PACKET_BYTES + 2],
      packet.bytes[PACKET_BYTES + 1]
    };
    if (observed_crc !== expected_crc) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s packet %0d CRC16 is 0x%04h, expected 0x%04h",
          label,
          packet_index,
          observed_crc,
          expected_crc
        )
      )
    end
  endfunction

  // Submit one host-to-device transaction and return passive reconstruction.
  task request_out_packet(
    string label,
    logic [7:0] interval_base,
    int unsigned transaction_count,
    int unsigned packet_index,
    output usb_utmi_packet packet
  );
    uvm_event rx_packet_event;
    uvm_object observed_object;
    byte unsigned packet_bytes[$];
    logic [15:0] packet_crc;
    logic [7:0] packet_pid;
    bit packet_seen;
    bit wait_expired;

    rx_packet_event =
        uvm_event_pool::get_global(USB_UTMI_RX_DATA_PACKET_EVENT);
    rx_packet_event.reset();
    packet_seen = 1'b0;
    wait_expired = 1'b0;
    fork
      begin
        fork
          begin
            rx_packet_event.wait_trigger_data(observed_object);
            packet_seen = 1'b1;
          end
          begin
            #(transfer_timeout);
            wait_expired = 1'b1;
          end
        join_none
        inject_out_token();
        packet_pid = expected_out_pid(transaction_count, packet_index);
        packet_bytes.push_back(packet_pid);
        for (int unsigned byte_index = 0;
             byte_index < PACKET_BYTES;
             byte_index++) begin
          packet_bytes.push_back(expected_byte(
              interval_base,
              packet_index * PACKET_BYTES + byte_index));
        end
        packet_crc = usb_crc16(packet_bytes, 1, PACKET_BYTES);
        packet_bytes.push_back(packet_crc[7:0]);
        packet_bytes.push_back(packet_crc[15:8]);
        inject_raw_rx_packet(packet_bytes);
        wait (packet_seen || wait_expired);
        disable fork;
      end
    join
    if (!packet_seen) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s packet %0d was not observed within %0t",
          label,
          packet_index,
          transfer_timeout
        )
      )
    end
    if (!$cast(packet, observed_object)) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s packet %0d event carried an unexpected object type",
          label,
          packet_index
        )
      )
    end
  endtask

  // Verify the complete OUT payload committed to packet memory.
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
        expected_word[8*lane +: 8] =
            expected_byte(interval_base, offset + lane);
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
      $sformatf(
        "%s verified all %0d packet-distinct bytes",
        label,
        byte_count
      ),
      UVM_LOW
    )
  endtask

  // Require bytes beyond a legal reduced transfer to remain untouched.
  task verify_out_tail_sentinel(
    string label,
    int unsigned first_offset,
    logic [31:0] sentinel
  );
    logic [31:0] observed_word;

    for (int unsigned offset = first_offset;
         offset < INTERVAL_BYTES;
         offset += 4) begin
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

  // Require the programmer-guide ownership transition for one interval entry.
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
          (!check_buffer ||
           entry_buffer_byte_offset(entry) === expected_buffer);
      if (!retired) #1us;
    end while (!retired && $realtime < deadline);
    if (!retired) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s did not retire the complete interval: %s",
          label,
          describe_entry(entry)
        )
      )
    end

    interrupt_mask = endpoint_intstat_mask(endpoint);
    ral_read32(
      "INTSTAT",
      p_sequencer.reg_model.combo.dev0_csr.INTSTAT,
      interrupt_status
    );
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
    #5us;
    ral_read32(
      "INTSTAT",
      p_sequencer.reg_model.combo.dev0_csr.INTSTAT,
      interrupt_status
    );
    if ((interrupt_status & interrupt_mask) !== 0) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s endpoint interrupt reasserted after one retirement: INTSTAT=0x%08h",
          label,
          interrupt_status
        )
      )
    end
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "%s retired once with Active=0 NBytes=%0d buffer=0x%08h",
        label,
        expected_nbytes,
        entry_buffer_byte_offset(entry)
      ),
      UVM_LOW
    )
  endtask

  // Run one OUT service interval at a controlled phase relative to SOF.
  task run_out_interval(
    usb_endpoint_cfg endpoint,
    string label,
    logic [7:0] interval_base,
    int unsigned packet_count,
    int unsigned transaction_count,
    logic [3:0] expected_error
  );
    usb_ep_entry_t armed_entry;
    usb_ep_entry_t observed_entry;
    usb_utmi_packet packet;
    logic [7:0] expected_pid;
    logic [31:0] expected_buffer;
    int unsigned expected_nbytes;
    int unsigned writeback_count;
    bit stop_writeback_monitor;
    bit writeback_monitor_done;
    logic [31:0] payload_sentinel;
    logic [31:0] guard_before_sentinel;
    logic [31:0] guard_after_sentinel;

    if (packet_count == 0 ||
        packet_count > transaction_count ||
        transaction_count > PACKETS_PER_INTERVAL) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s has invalid packet_count=%0d transaction_count=%0d",
          label,
          packet_count,
          transaction_count
        )
      )
    end
    expected_nbytes = INTERVAL_BYTES - packet_count * PACKET_BYTES;
    expected_buffer = out_buffer + packet_count * PACKET_BYTES;
    payload_sentinel = 32'heeee_eeee;
    guard_before_sentinel = 32'ha5a5_5a5a;
    guard_after_sentinel = 32'h5a5a_a5a5;
    fill_endpoint_buffer(out_guard_before, GUARD_BYTES, guard_before_sentinel);
    fill_endpoint_buffer(out_buffer, INTERVAL_BYTES, payload_sentinel);
    fill_endpoint_buffer(out_guard_after, GUARD_BYTES, guard_after_sentinel);
    clear_endpoint_interrupt(endpoint);
    clear_info_error();
    inject_sof();
    #1us;
    arm_endpoint(
      endpoint,
      INTERVAL_BYTES,
      out_buffer,
      armed_entry
    );
    #(endpoint_ready_delay);
    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry.active !== 1'b1 ||
        observed_entry.nbytes !== INTERVAL_BYTES) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s descriptor changed before its first OUT token: %s",
          label,
          describe_entry(observed_entry)
        )
      )
    end
    stop_writeback_monitor = 1'b0;
    writeback_monitor_done = 1'b0;
    fork
      begin
        count_endpoint_writebacks(
          endpoint,
          stop_writeback_monitor,
          writeback_count
        );
        writeback_monitor_done = 1'b1;
      end
    join_none
    for (int unsigned packet_index = 0;
         packet_index < packet_count;
         packet_index++) begin
      if (packet_index != 0) #(inter_transaction_delay);
      request_out_packet(
        label,
        interval_base,
        transaction_count,
        packet_index,
        packet
      );
      expected_pid = expected_out_pid(transaction_count, packet_index);
      check_data_packet(
        packet,
        label,
        expected_pid,
        interval_base,
        packet_index
      );
    end
    #(interval_end_delay);
    inject_sof();
    wait_for_info_error(label, expected_error);
    verify_interval_retired(
      endpoint,
      label,
      expected_nbytes,
      expected_buffer,
      1'b1
    );
    stop_writeback_monitor = 1'b1;
    wait (writeback_monitor_done);
    if (writeback_count != 1) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s generated %0d descriptor writebacks, expected exactly one",
          label,
          writeback_count
        )
      )
    end
    if (expected_error == ERROR_NONE) begin
      verify_out_payload(
        label,
        interval_base,
        packet_count * PACKET_BYTES
      );
      verify_out_tail_sentinel(
        label,
        packet_count * PACKET_BYTES,
        payload_sentinel
      );
    end
    verify_out_guard(label, out_guard_before, guard_before_sentinel);
    verify_out_guard(label, out_guard_after, guard_after_sentinel);
    #1us;
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "%s completed with %0d/%0d packets: residual=%0d error=0x%0h writebacks=%0d",
        label,
        packet_count,
        transaction_count,
        expected_nbytes,
        expected_error,
        writeback_count
      ),
      UVM_LOW
    )
  endtask

  // Run one IN service interval at a controlled phase relative to SOF.
  task run_in_interval(
    usb_endpoint_cfg endpoint,
    string label,
    logic [7:0] interval_base,
    int unsigned packet_count
  );
    usb_ep_entry_t armed_entry;
    usb_ep_entry_t observed_entry;
    usb_utmi_packet packet;
    logic [7:0] expected_pid;

    fill_in_payload(interval_base);
    clear_endpoint_interrupt(endpoint);
    inject_sof();
    #1us;
    arm_endpoint(
      endpoint,
      INTERVAL_BYTES,
      in_buffer,
      armed_entry
    );
    #(endpoint_ready_delay);
    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry.active !== 1'b1 ||
        observed_entry.nbytes !== INTERVAL_BYTES) begin
      `uvm_fatal(
        "USB_HB_ISO",
        $sformatf(
          "%s descriptor changed before its first IN token: %s",
          label,
          describe_entry(observed_entry)
        )
      )
    end
    for (int unsigned packet_index = 0;
         packet_index < packet_count;
         packet_index++) begin
      if (packet_index != 0) #(inter_transaction_delay);
      request_in_packet(
        $sformatf("%s packet %0d", label, packet_index),
        packet
      );
      case (packet_index)
        0: expected_pid = 8'h87;
        1: expected_pid = 8'h4b;
        default: expected_pid = 8'hc3;
      endcase
      check_data_packet(
        packet,
        label,
        expected_pid,
        interval_base,
        packet_index
      );
    end
    #(interval_end_delay);
    inject_sof();
    verify_interval_retired(endpoint, label, 0, 32'h0, 1'b0);
    #1us;
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "%s completed with %0d/%0d packets and correct payload",
        label,
        packet_count,
        PACKETS_PER_INTERVAL
      ),
      UVM_LOW
    )
  endtask

  // Enumerate, prove clean completion, then prove one/two-packet abandonment.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg out_endpoint;
    usb_endpoint_cfg in_endpoint;

    completed = 1'b0;
    `uvm_info(
      "USB_HB_ISO",
      $sformatf(
        "Starting high-bandwidth ISO scenario: interrupted_out_acceptance=%0b; running enumeration first",
        run_interrupted_out_acceptance
      ),
      UVM_LOW
    )
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_HB_ISO", "Enumeration did not complete")
    end
    out_endpoint = get_endpoint(2, USB_DIRECTION_OUT);
    in_endpoint = get_endpoint(2, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list(
      "High-bandwidth ISO OUT",
      out_buffer,
      INTERVAL_BYTES
    );
    check_buffer_clear_of_endpoint_list(
      "High-bandwidth ISO IN",
      in_buffer,
      INTERVAL_BYTES
    );
    enable_endpoint_interrupt(out_endpoint);
    enable_endpoint_interrupt(in_endpoint);

    stop_sof_generation();

    if (run_interrupted_out_acceptance) begin
      // Run the first interruption before any successful EP2 OUT interval so
      // a stale completion count cannot accidentally satisfy the checker.
      run_out_interval(
        out_endpoint,
        "One-packet interrupted ISO OUT",
        8'h30,
        1,
        3,
        ERROR_PACKET_UNEXPECTED
      );
      run_out_interval(
        out_endpoint,
        "Fresh OUT interval after one-packet loss",
        8'h71,
        3,
        3,
        ERROR_NONE
      );
      run_out_interval(
        out_endpoint,
        "Two-packet interrupted ISO OUT",
        8'h40,
        2,
        3,
        ERROR_PACKET_UNEXPECTED
      );
      run_out_interval(
        out_endpoint,
        "Fresh OUT interval after two-packet loss",
        8'hb0,
        3,
        3,
        ERROR_NONE
      );
      run_out_interval(
        out_endpoint,
        "Legal one-transaction ISO OUT",
        8'h50,
        1,
        1,
        ERROR_NONE
      );
      run_out_interval(
        out_endpoint,
        "Legal two-transaction ISO OUT",
        8'h90,
        2,
        2,
        ERROR_NONE
      );
    end else begin
      // OUT uses MDATA, MDATA, DATA2 for three transactions per microframe.
      run_out_interval(
        out_endpoint,
        "Clean high-bandwidth ISO OUT",
        8'h10,
        3,
        3,
        ERROR_NONE
      );
    end

    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b1;

    // Clean interval: all three packets fit before the next SOF.
    run_in_interval(
      in_endpoint,
      "Clean high-bandwidth ISO IN",
      8'h20,
      3
    );

    // SOF after one packet: the remaining two packets are abandoned.
    run_in_interval(
      in_endpoint,
      "One-packet interrupted ISO IN",
      8'h30,
      1
    );
    run_in_interval(
      in_endpoint,
      "Fresh interval after one-packet loss",
      8'h71,
      3
    );

    // SOF after two packets: the final packet is abandoned.
    run_in_interval(
      in_endpoint,
      "Two-packet interrupted ISO IN",
      8'h40,
      2
    );
    run_in_interval(
      in_endpoint,
      "Fresh interval after two-packet loss",
      8'hb0,
      3
    );
    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b0;
    start_sof_generation();

    completed = 1'b1;
    if (run_interrupted_out_acceptance) begin
      `uvm_info(
        "USB_HB_ISO",
        "Clean and interrupted high-bandwidth ISO IN/OUT intervals completed with retirement and fresh-data checks",
        UVM_LOW
      )
    end else begin
      `uvm_info(
        "USB_HB_ISO",
        "Clean ISO IN/OUT and interrupted ISO IN intervals completed with retirement and fresh-data checks",
        UVM_LOW
      )
    end
  endtask
endclass
