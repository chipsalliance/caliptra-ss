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

// Starves one bulk IN packet and verifies exact abort and retry behavior.
class usb_tx_underrun_seq extends usb_base_seq;
  `uvm_object_utils(usb_tx_underrun_seq)

  localparam logic [3:0] ERROR_TIMEOUT = 4'h6;
  localparam logic [7:0] USB_PID_DATA0 = 8'hc3;
  localparam logic [7:0] USB_PID_ACK = 8'hd2;

  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 512;
  logic [7:0] payload_base = 8'h40;
  time scenario_timeout = 500us;
  time starvation_duration = 5us;
  time tx_ready_delay = 1us;
  bit completed;

  function new(string name = "usb_tx_underrun_seq");
    super.new(name);
  endfunction

  // Calculate the transmitted USB CRC16 over a payload byte range.
  function logic [15:0] usb_crc16(
    byte unsigned bytes[$],
    int unsigned first,
    int unsigned count
  );
    logic [15:0] crc;
    byte unsigned data_byte;
    logic feedback;

    crc = 16'hffff;
    for (int unsigned byte_index = 0;
         byte_index < count;
         byte_index++) begin
      data_byte = bytes[first + byte_index];
      repeat (8) begin
        feedback = crc[0] ^ data_byte[0];
        crc >>= 1;
        if (feedback) crc ^= 16'ha001;
        data_byte >>= 1;
      end
    end
    return ~crc;
  endfunction

  // Calculate USB token CRC5 in packed token-bit order.
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

  // Drive one complete packet through the controlled UTMI receive path.
  task inject_raw_packet(byte unsigned packet_bytes[$]);
    if (packet_bytes.size() == 0) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Cannot inject an empty UTMI packet")
    end
    @(negedge p_sequencer.ctrl_vif.utmi_clk);
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

  // Inject one valid IN token for the selected endpoint.
  task inject_in_token(usb_endpoint_cfg endpoint);
    byte unsigned token_packet[$];
    logic [10:0] token_bits;
    logic [15:0] token_word;

    token_bits = {
      4'(endpoint.ep_number),
      7'(p_sequencer.cfg.device_address)
    };
    token_word = {usb_crc5(token_bits), token_bits};
    token_packet.push_back(8'h69);
    token_packet.push_back(token_word[7:0]);
    token_packet.push_back(token_word[15:8]);
    inject_raw_packet(token_packet);
  endtask

  // Inject the host ACK only after a valid retry packet is checked.
  task inject_ack();
    byte unsigned ack_packet[$];

    ack_packet.push_back(USB_PID_ACK);
    inject_raw_packet(ack_packet);
  endtask

  // Request one IN packet and return its passive UTMI reconstruction.
  task request_in_packet(
    usb_endpoint_cfg endpoint,
    string label,
    output usb_utmi_packet packet
  );
    uvm_event tx_data_packet_event;
    uvm_object observed_object;
    bit packet_seen;
    bit wait_expired;

    tx_data_packet_event =
        uvm_event_pool::get_global(USB_UTMI_TX_DATA_PACKET_EVENT);
    tx_data_packet_event.reset();
    packet_seen = 1'b0;
    wait_expired = 1'b0;
    fork
      begin
        fork
          begin
            tx_data_packet_event.wait_trigger_data(observed_object);
            packet_seen = 1'b1;
          end
          begin
            #(scenario_timeout);
            wait_expired = 1'b1;
          end
        join_none
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b0;
        inject_in_token(endpoint);
        #(tx_ready_delay);
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b1;
        wait (packet_seen || wait_expired);
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b0;
        disable fork;
      end
    join
    if (!packet_seen || !$cast(packet, observed_object)) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "%s did not produce a DATA packet within %0t",
          label,
          scenario_timeout
        )
      )
    end
  endtask

  // Require the aborted packet's exact complemented CRC and initial toggle.
  function void check_corrupted_packet(usb_utmi_packet packet);
    logic [15:0] expected_crc;
    logic [15:0] observed_crc;
    int unsigned payload_count;

    if (packet == null || packet.bytes.size() < 3) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        "Underrun observation did not contain DATA framing and CRC16"
      )
      return;
    end
    if (packet.bytes[0] !== USB_PID_DATA0) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Underrun packet PID is 0x%02h, expected initial DATA0",
          packet.bytes[0]
        )
      )
    end
    payload_count = packet.bytes.size() - 3;
    expected_crc = usb_crc16(packet.bytes, 1, payload_count);
    observed_crc = {
      packet.bytes[packet.bytes.size() - 1],
      packet.bytes[packet.bytes.size() - 2]
    };
    if (observed_crc !== ~expected_crc) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Underrun CRC16 is 0x%04h, expected exact complement 0x%04h of valid 0x%04h",
          observed_crc,
          ~expected_crc,
          expected_crc
        )
      )
    end
    `uvm_info(
      "USB_TX_UNDERRUN",
      $sformatf(
        "Observed exact complemented CRC16 after %0d payload bytes: bad=0x%04h valid=0x%04h",
        payload_count,
        observed_crc,
        expected_crc
      ),
      UVM_LOW
    )
  endfunction

  // Require a complete retry of the original DATA0 packet from byte zero.
  function void check_retry_packet(usb_utmi_packet packet);
    logic [15:0] expected_crc;
    logic [15:0] observed_crc;

    if (packet == null || packet.bytes.size() != payload_bytes + 3) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Retry packet has %0d bytes, expected %0d",
          packet == null ? 0 : packet.bytes.size(),
          payload_bytes + 3
        )
      )
    end
    if (packet.bytes[0] !== USB_PID_DATA0) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Retry PID is 0x%02h, expected preserved DATA0",
          packet.bytes[0]
        )
      )
    end
    for (int unsigned byte_index = 0;
         byte_index < payload_bytes;
         byte_index++) begin
      logic [7:0] expected_byte;

      expected_byte = payload_base + byte_index;
      if (packet.bytes[byte_index + 1] !== expected_byte) begin
        `uvm_fatal(
          "USB_TX_UNDERRUN",
          $sformatf(
            "Retry byte %0d is 0x%02h, expected 0x%02h",
            byte_index,
            packet.bytes[byte_index + 1],
            expected_byte
          )
        )
      end
    end
    expected_crc = usb_crc16(packet.bytes, 1, payload_bytes);
    observed_crc = {
      packet.bytes[payload_bytes + 2],
      packet.bytes[payload_bytes + 1]
    };
    if (observed_crc !== expected_crc) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Retry CRC16 is 0x%04h, expected 0x%04h",
          observed_crc,
          expected_crc
        )
      )
    end
  endfunction

  // Wait for the underrun error code before any successful retry.
  task wait_for_error_code(logic [3:0] expected_error);
    uvm_reg_field error_field;
    logic [31:0] info_value;
    logic [3:0] observed_error;
    realtime deadline;

    error_field = p_sequencer.reg_model.combo.dev0_csr.INFO.ERR_CODE;
    observed_error = 4'h0;
    deadline = $realtime + scenario_timeout;
    while (observed_error !== expected_error && $realtime < deadline) begin
      ral_read32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, info_value);
      observed_error = 4'(
          (info_value & ral_field_mask(error_field)) >>
          error_field.get_lsb_pos());
      if (observed_error !== expected_error) #500ns;
    end
    if (observed_error !== expected_error) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "INFO.ERR_CODE did not reach 0x%0h; last=0x%0h",
          expected_error,
          observed_error
        )
      )
    end
  endtask

  // Slow the DMA clock after exactly 16 transmitted payload bytes.
  task run_dma_starvation(
    uvm_event tx_data_progress_event,
    uvm_event failed_packet_complete_event
  );
    tx_data_progress_event.wait_on();
    `uvm_info(
      "USB_TX_UNDERRUN",
      $sformatf(
        "Observed 16 transmitted payload bytes; slowing the DMA clock for %0t",
        starvation_duration
      ),
      UVM_LOW
    )
    p_sequencer.ctrl_vif.slow_bus_clock <= 1'b1;
    #(starvation_duration);
    failed_packet_complete_event.wait_on();
    p_sequencer.ctrl_vif.slow_bus_clock <= 1'b0;
    `uvm_info(
      "USB_TX_UNDERRUN",
      "Restored the normal DMA clock rate",
      UVM_LOW
    )
  endtask

  // Read the selected endpoint's data-toggle state.
  task read_endpoint_toggle(
    usb_endpoint_cfg endpoint,
    output bit toggle
  );
    logic [31:0] toggle_value;

    ral_read32(
      "EPTOGGLE",
      p_sequencer.reg_model.combo.dev0_csr.EPTOGGLE,
      toggle_value
    );
    toggle = |(toggle_value & endpoint.csr_bit_mask());
  endtask

  // Verify failed-attempt ownership and absence of a completion interrupt.
  task verify_failed_attempt_preserved(
    usb_endpoint_cfg endpoint,
    usb_ep_entry_t armed_entry,
    bit initial_toggle
  );
    usb_ep_entry_t observed_entry;
    logic [31:0] interrupt_status;
    bit observed_toggle;

    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry !== armed_entry) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Descriptor changed before retry: observed=%s expected=%s",
          describe_entry(observed_entry),
          describe_entry(armed_entry)
        )
      )
    end
    read_endpoint_toggle(endpoint, observed_toggle);
    if (observed_toggle !== initial_toggle) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        "Bulk toggle changed before a valid host ACK"
      )
    end
    ral_read32(
      "INTSTAT",
      p_sequencer.reg_model.combo.dev0_csr.INTSTAT,
      interrupt_status
    );
    if ((interrupt_status & endpoint_intstat_mask(endpoint)) !== 0) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Failed packet generated an endpoint interrupt: INTSTAT=0x%08h",
          interrupt_status
        )
      )
    end
  endtask

  // Enumerate, force one underrun, then verify one complete valid retry.
  virtual task body();
    usb_init_seq init_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t armed_entry;
    usb_ep_entry_t retired_entry;
    usb_utmi_packet failed_packet;
    usb_utmi_packet retry_packet;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;
    uvm_event tx_data_progress_event;
    uvm_event failed_packet_complete_event;
    bit initial_toggle;
    bit retired_toggle;

    completed = 1'b0;
    `uvm_info(
      "USB_TX_UNDERRUN",
      "Starting bulk IN underrun scenario; running enumeration first",
      UVM_LOW
    )
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TX_UNDERRUN", "Enumeration did not complete")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_IN);
    check_buffer_clear_of_endpoint_list(
      "Bulk IN underrun",
      buffer_offset,
      payload_bytes
    );
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      logic [31:0] data_word;

      for (int unsigned lane = 0; lane < 4; lane++) begin
        data_word[8*lane +: 8] = payload_base + offset + lane;
      end
      write32(USB_DEV0_SRAM, buffer_offset + offset, data_word);
    end
    arm_endpoint(
      endpoint,
      payload_bytes,
      buffer_offset,
      armed_entry
    );
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
    read_endpoint_toggle(endpoint, initial_toggle);

    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b1;

    tx_data_progress_event =
        uvm_event_pool::get_global(USB_UTMI_TX_DATA_PROGRESS_EVENT);
    tx_data_progress_event.reset();
    failed_packet_complete_event =
        new("failed_packet_complete_event");
    fork
      begin
        request_in_packet(
          endpoint,
          "Underrun attempt",
          failed_packet
        );
        check_corrupted_packet(failed_packet);
        failed_packet_complete_event.trigger();
      end
      begin
        run_dma_starvation(
            tx_data_progress_event,
            failed_packet_complete_event);
      end
    join
    wait_for_error_code(ERROR_TIMEOUT);
    verify_failed_attempt_preserved(
      endpoint,
      armed_entry,
      initial_toggle
    );

    `uvm_info(
      "USB_TX_UNDERRUN",
      "No ACK was sent for the failed packet; requesting the original packet again",
      UVM_LOW
    )
    request_in_packet(endpoint, "Valid retry", retry_packet);
    check_retry_packet(retry_packet);
    inject_ack();
    wait_for_endpoint_interrupt(endpoint, scenario_timeout);
    read_endpoint_entry(endpoint, retired_entry);
    if (retired_entry.active !== 1'b0 ||
        retired_entry.nbytes !== 0) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        $sformatf(
          "Descriptor did not retire after valid ACK: %s",
          describe_entry(retired_entry)
        )
      )
    end
    read_endpoint_toggle(endpoint, retired_toggle);
    if (retired_toggle === initial_toggle) begin
      `uvm_fatal(
        "USB_TX_UNDERRUN",
        "Bulk toggle did not advance after the valid retry ACK"
      )
    end

    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b0;
    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);

    completed = 1'b1;
    `uvm_info(
      "USB_TX_UNDERRUN",
      "Exact bad CRC, preserved failed attempt, and valid byte-zero retry verified",
      UVM_LOW
    )
  endtask
endclass
