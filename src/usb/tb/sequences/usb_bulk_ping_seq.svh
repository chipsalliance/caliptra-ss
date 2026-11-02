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

// Forces high-speed bulk OUT flow control through NAK and PING before ACK.
//
// Relies on the Synopsys SVT USB VIP's built-in PING protocol engine
// (svt_usb_host_configuration::ping_protocol_supported = 1), built-in protocol
// packet notifications (host_agent.prot.NOTIFY_20_HOST_TX_PACKET and
// NOTIFY_20_HOST_RX_PACKET in others/class_svt_usb_protocol.html), and
// built-in protocol/link checks (enabled by default via register_default_chks = 1,
// enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_link_20_sc.html):
//   - svt_usb_protocol_ep_sc:
//     * valid_device_response_check: Checks device NAK/ACK/NYET responses to
//       OUT and PING transactions per USB 2.0 Section 8.5.1.
//     * valid_host_response_check: Checks host PING protocol transitions after
//       receiving NAK/NYET on a high-speed bulk OUT endpoint.
//     * data_toggle_check: Checks DATA0 toggle retention across the initial
//       NAKed OUT attempt and the subsequent ACK-accepted OUT retry.
//     * packet_error_check: Checks all tokens, data packets, and handshakes for
//       PID, CRC5, CRC16, bitstuff, and framing errors.
//     * flow_control_duration_check: Checks flow-control duration limits.
//   - svt_usb_link_20_sc:
//     * unexpected_response_check: Checks that every handshake belongs to an
//       active token/data exchange.
class usb_bulk_ping_seq extends usb_base_seq;
  `uvm_object_utils(usb_bulk_ping_seq)

  localparam logic [3:0] ERROR_SENT_RECEIVED_NAK = 4'h9;

  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 64;
  logic [7:0] payload_base = 8'h50;
  time ping_timeout = 500us;
  bit completed;

  function new(string name = "usb_bulk_ping_seq");
    super.new(name);
  endfunction

  // Check endpoint retirement and all received bytes.
  task verify_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 ||
        entry.nbytes !== 0 ||
        entry_buffer_byte_offset(entry) !== buffer_offset + payload_bytes) begin
      `uvm_fatal(
        "USB_BULK_PING",
        $sformatf(
          "Bulk OUT did not retire cleanly after PING flow control: observed %s, expected active=0 nbytes=0 buffer=0x%03h",
          describe_entry(entry),
          buffer_offset + payload_bytes
        )
      )
    end
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_BULK_PING",
          $sformatf("Bulk OUT payload mismatch at offset %0d: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
  endtask

  // Wait on the SVT protocol component's built-in NOTIFY_20_HOST_TX_PACKET and
  // NOTIFY_20_HOST_RX_PACKET events until the host issues a PING to the target
  // bulk OUT endpoint and the inactive device responds with NAK.
  task wait_for_vip_ping_nak(svt_usb_agent host_agent, usb_endpoint_cfg endpoint);
    bit observed_ping_nak;

    observed_ping_nak = 1'b0;
    fork
      begin
        while (!observed_ping_nak) begin
          uvm_object tx_obj;
          svt_usb_packet tx_pkt;

          host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(tx_obj);
          if (!$cast(tx_pkt, tx_obj)) begin
            continue;
          end
          if (tx_pkt.get_pid_name_val() == svt_usb_packet::PING &&
              tx_pkt.get_device_address_val() == p_sequencer.cfg.device_address &&
              tx_pkt.get_ept_num_val() == 4'(endpoint.ep_number)) begin
            uvm_object rx_obj;
            svt_usb_packet rx_pkt;

            host_agent.prot.NOTIFY_20_HOST_RX_PACKET.wait_trigger_data(rx_obj);
            if ($cast(rx_pkt, rx_obj) &&
                rx_pkt.get_pid_name_val() == svt_usb_packet::NAK) begin
              observed_ping_nak = 1'b1;
            end
          end
        end
      end
      begin
        #(ping_timeout);
        if (!observed_ping_nak) begin
          `uvm_fatal(
            "USB_BULK_PING",
            $sformatf("Timed out after %0t waiting for VIP PING -> NAK exchange on EP%0d OUT", ping_timeout, endpoint.ep_number)
          )
        end
      end
    join_any
    disable fork;
  endtask

  // Enumerate, force a PING retry, then complete and verify the transfer.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t inactive_entry;
    usb_ep_entry_t active_entry;
    svt_usb_agent host_agent;

    completed = 1'b0;
    `uvm_info("USB_BULK_PING", "Starting bulk OUT PING flow-control scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BULK_PING", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) ||
        host_agent.prot == null) begin
      `uvm_fatal("USB_BULK_PING", "Unable to resolve the SVT host agent protocol component")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list("Bulk PING", buffer_offset, payload_bytes);
    fill_endpoint_buffer(buffer_offset, payload_bytes, 32'heeee_eeee);
    inactive_entry = endpoint_entry(1'b0, 1'b0, payload_bytes, buffer_offset);
    write_endpoint_entry(endpoint, inactive_entry);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);

    host_sequence = usb_bulk_out_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = ping_timeout;
    host_sequence.transfer_label = "Bulk OUT after PING";

    `uvm_info("USB_BULK_PING", "EP1 OUT is inactive; starting bulk OUT and waiting for VIP PING -> NAK", UVM_LOW)
    fork
      begin
        host_sequence.start(p_sequencer.host_sequencer);
        if (!host_sequence.completed) begin
          `uvm_fatal("USB_BULK_PING", "Bulk OUT host sequence returned incomplete")
        end
      end
      begin
        wait_for_vip_ping_nak(host_agent, endpoint);
        wait_for_sie_error_code(ERROR_SENT_RECEIVED_NAK, ping_timeout, "Bulk OUT NAK/PING");
        `uvm_info("USB_BULK_PING", "Observed VIP PING -> NAK and DUT ERROR_SENT_RECEIVED_NAK; arming EP1 OUT", UVM_LOW)
        arm_endpoint(endpoint, payload_bytes, buffer_offset, active_entry);
      end
    join

    wait_for_endpoint_interrupt(endpoint, ping_timeout);
    verify_transfer(endpoint);

    completed = 1'b1;
    `uvm_info(
      "USB_BULK_PING",
      $sformatf("Bulk OUT PING flow control verified: payload_bytes=%0d", payload_bytes),
      UVM_LOW
    )
  endtask
endclass
