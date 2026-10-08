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

// Supplies a checked post-resume bulk transfer for low-power scenarios.
class usb_resume_recovery_seq extends usb_base_seq;
  logic [31:0] recovery_buffer_offset = 32'h0000_0200;
  int unsigned recovery_bytes = 16;
  logic [7:0] recovery_payload_base = 8'hd0;
  time recovery_timeout = 750us;
  time recovery_poll_interval = 500ns;

  function new(string name = "usb_resume_recovery_seq");
    super.new(name);
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

  // Calculate USB CRC16 over one payload queue.
  function logic [15:0] usb_crc16(byte unsigned bytes[$]);
    logic [15:0] crc;
    logic feedback;
    byte unsigned data_byte;

    crc = 16'hffff;
    foreach (bytes[index]) begin
      data_byte = bytes[index];
      repeat (8) begin
        feedback = crc[0] ^ data_byte[0];
        crc >>= 1;
        if (feedback) crc ^= 16'ha001;
        data_byte >>= 1;
      end
    end
    return ~crc;
  endfunction

  // Drive one complete host packet through the raw UTMI receive path.
  task inject_raw_packet(byte unsigned packet_bytes[$]);
    if (packet_bytes.size() == 0) begin
      `uvm_fatal("USB_RESUME_RECOVERY", "Cannot inject an empty UTMI packet")
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

  // Verify endpoint retirement and every byte of the recovery payload.
  task verify_recovery_transfer(usb_endpoint_cfg endpoint, string scenario_label);
    usb_ep_entry_t observed_entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, observed_entry);
    if (observed_entry.nbytes !== 0 || observed_entry.active !== 1'b0) begin
      `uvm_fatal("USB_RESUME_RECOVERY", $sformatf("%s endpoint did not retire cleanly: %s", scenario_label, describe_entry(observed_entry)))
    end
    for (int unsigned offset = 0; offset < recovery_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = recovery_payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, recovery_buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_RESUME_RECOVERY",
          $sformatf(
            "%s payload mismatch at offset 0x%03h: data=0x%08h expected=0x%08h",
            scenario_label,
            offset,
            observed_word,
            expected_word
          )
        )
      end
    end
    `uvm_info("USB_RESUME_RECOVERY", $sformatf("%s verified for all %0d bytes", scenario_label, recovery_bytes), UVM_LOW)
  endtask

  // Arm EP1 OUT, send known data, and verify the post-resume datapath.
  task run_recovery_transfer(string scenario_label);
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list(scenario_label, recovery_buffer_offset, recovery_bytes);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    fill_endpoint_buffer(recovery_buffer_offset, recovery_bytes, 32'heeee_eeee);
    arm_endpoint(endpoint, recovery_bytes, recovery_buffer_offset, entry);

    host_sequence = usb_bulk_out_host_seq::type_id::create("recovery_host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = recovery_bytes;
    host_sequence.payload_base = recovery_payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = recovery_timeout;
    host_sequence.transfer_label = scenario_label;
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_RESUME_RECOVERY", $sformatf("%s host sequence returned incomplete", scenario_label))
        end
      end
      begin
        wait_for_endpoint_interrupt(endpoint, recovery_timeout, recovery_poll_interval);
      end
    join
    verify_recovery_transfer(endpoint, scenario_label);
  endtask

  // Inject and passively check one post-resume bulk OUT transaction.
  task run_raw_recovery_transfer(string scenario_label);
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    usb_utmi_packet response_packet;
    uvm_event tx_packet_event;
    uvm_object observed_object;
    byte unsigned token_packet[$];
    byte unsigned payload[$];
    byte unsigned data_packet[$];
    logic [10:0] token_bits;
    logic [15:0] token_word;
    logic [15:0] data_crc;
    bit packet_seen;
    bit wait_expired;

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list(
      scenario_label,
      recovery_buffer_offset,
      recovery_bytes
    );
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    fill_endpoint_buffer(
      recovery_buffer_offset,
      recovery_bytes,
      32'heeee_eeee
    );
    arm_endpoint(
      endpoint,
      recovery_bytes,
      recovery_buffer_offset,
      entry
    );

    token_bits = {
      4'(endpoint.ep_number),
      7'(p_sequencer.cfg.device_address)
    };
    token_word = {usb_crc5(token_bits), token_bits};
    token_packet.push_back(8'he1);
    token_packet.push_back(token_word[7:0]);
    token_packet.push_back(token_word[15:8]);
    for (int unsigned byte_index = 0;
         byte_index < recovery_bytes;
         byte_index++) begin
      payload.push_back(recovery_payload_base + byte_index);
    end
    data_crc = usb_crc16(payload);
    data_packet.push_back(8'hc3);
    foreach (payload[index]) data_packet.push_back(payload[index]);
    data_packet.push_back(data_crc[7:0]);
    data_packet.push_back(data_crc[15:8]);

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
            #(recovery_timeout);
            wait_expired = 1'b1;
          end
        join_none
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b1;
        inject_raw_packet(token_packet);
        inject_raw_packet(data_packet);
        wait (packet_seen || wait_expired);
        p_sequencer.ctrl_vif.raw_utmi_txready <= 1'b0;
        disable fork;
      end
    join
    if (!packet_seen || !$cast(response_packet, observed_object)) begin
      `uvm_fatal(
        "USB_RESUME_RECOVERY",
        $sformatf(
          "%s did not receive a DUT response within %0t",
          scenario_label,
          recovery_timeout
        )
      )
    end
    if (response_packet.bytes.size() != 1 ||
        !(response_packet.bytes[0] inside {8'hd2, 8'h96})) begin
      `uvm_fatal(
        "USB_RESUME_RECOVERY",
        $sformatf(
          "%s response is not ACK or NYET: bytes=%0d pid=0x%02h",
          scenario_label,
          response_packet.bytes.size(),
          response_packet.bytes.size() == 0 ?
              8'hxx : response_packet.bytes[0]
        )
      )
    end
    wait_for_endpoint_interrupt(
      endpoint,
      recovery_timeout,
      recovery_poll_interval
    );
    verify_recovery_transfer(endpoint, scenario_label);
    `uvm_info(
      "USB_RESUME_RECOVERY",
      $sformatf(
        "%s received successful handshake 0x%02h and retired with correct data",
        scenario_label,
        response_packet.bytes[0]
      ),
      UVM_LOW
    )
  endtask
endclass
