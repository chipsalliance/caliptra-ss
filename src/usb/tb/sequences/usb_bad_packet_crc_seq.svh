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

// Shared malformed-CRC stimulus, DUT status checking, retry, and payload check.
//
// Relies on the Synopsys SVT USB VIP's built-in error-injection callbacks
// (svt_usb_protocol_20_host_tx_packet_crc5_error and
// svt_usb_protocol_20_host_tx_packet_crc16_error in
// callback/class_svt_usb_protocol_20_host_tx_packet_crc5_error.html and
// callback/class_svt_usb_protocol_20_host_tx_packet_crc16_error.html), built-in
// protocol packet notification (host_agent.prot.NOTIFY_20_HOST_TX_PACKET in
// others/class_svt_usb_protocol.html), and built-in protocol/link checks
// (enabled by default via register_default_chks = 1, enable_default_chks = 1 in
// protocolChecks.html, coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_link_20_sc.html):
//   - svt_usb_protocol::NOTIFY_20_HOST_TX_PACKET:
//     Confirms the host transmitted both the initial CRC-corrupted OUT attempt
//     and the subsequent clean retry after device response timeout.
//   - svt_usb_protocol_ep_sc:
//     * data_toggle_check: Checks DATA0 toggle preservation across the
//       rejected attempt and the retried transaction.
//     * valid_device_response_check: Checks the device ACK/NYET handshake on
//       the clean retry.
//     * packet_error_check: Checks all uncorrupted packets and handshakes for
//       PID, CRC, bitstuff, and framing validity.
//   - svt_usb_link_20_sc:
//     * unexpected_response_check: Checks that no handshake is returned for a
//       corrupted token or data packet.
virtual class usb_bad_packet_crc_seq extends usb_base_seq;
  logic [31:0] buffer_offset = 32'h0000_0200;
  int unsigned payload_bytes = 64;
  logic [7:0] payload_base = 8'h60;
  time error_timeout = 500us;
  bit completed;

  function new(string name = "usb_bad_packet_crc_seq");
    super.new(name);
  endfunction

  pure virtual function logic [3:0] expected_error_code();
  pure virtual function string scenario_label();
  pure virtual task install_injection(svt_usb_agent host_agent);
  pure virtual task remove_injection(svt_usb_agent host_agent);
  pure virtual function int unsigned injected_packet_count();

  // Verify retry completion and the final received payload.
  task verify_transfer(usb_endpoint_cfg endpoint);
    usb_ep_entry_t entry;
    logic [31:0] observed_word;
    logic [31:0] expected_word;

    read_endpoint_entry(endpoint, entry);
    if (entry.active !== 1'b0 || entry.nbytes !== 0) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", $sformatf("Bulk OUT did not retire after %s retry: %s", scenario_label(), describe_entry(entry)))
    end
    for (int unsigned offset = 0; offset < payload_bytes; offset += 4) begin
      expected_word = 32'h0;
      for (int unsigned lane = 0; lane < 4; lane++) begin
        expected_word[8*lane +: 8] = payload_base + offset + lane;
      end
      read32(USB_DEV0_SRAM, buffer_offset + offset, observed_word);
      if (observed_word !== expected_word) begin
        `uvm_fatal(
          "USB_BAD_PACKET_CRC",
          $sformatf("Retried payload mismatch at offset %0d: data=0x%08h expected=0x%08h", offset, observed_word, expected_word)
        )
      end
    end
  endtask

  // Enumerate, inject one malformed packet, and verify transparent recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_bulk_out_host_seq host_sequence;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    svt_usb_agent host_agent;
    svt_configuration base_usb_cfg;
    svt_usb_configuration usb_cfg;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;
    int unsigned out_attempt_count;

    completed = 1'b0;
    `uvm_info("USB_BAD_PACKET_CRC", $sformatf("Starting %s scenario; running enumeration first", scenario_label()), UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) ||
        host_agent.prot == null) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Unable to resolve the SVT host agent protocol component")
    end
    p_sequencer.host_sequencer.get_cfg(base_usb_cfg);
    if (!$cast(usb_cfg, base_usb_cfg)) begin
      `uvm_fatal("USB_BAD_PACKET_CRC", "Unable to resolve the SVT USB configuration")
    end

    endpoint = get_endpoint(1, USB_DIRECTION_OUT);
    check_buffer_clear_of_endpoint_list(scenario_label(), buffer_offset, payload_bytes);
    fill_endpoint_buffer(buffer_offset, payload_bytes, 32'heeee_eeee);
    arm_endpoint(endpoint, payload_bytes, buffer_offset, entry);
    enable_endpoint_interrupt(endpoint);
    clear_endpoint_interrupt(endpoint);
    ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);

    host_sequence = usb_bulk_out_host_seq::type_id::create("host_sequence");
    host_sequence.target_endpoint = endpoint;
    host_sequence.payload_byte_count = payload_bytes;
    host_sequence.payload_base = payload_base;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.bulk_transfer_timeout = error_timeout;
    host_sequence.transfer_label = {"Bulk OUT with ", scenario_label()};

    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
    host_agent.reconfigure(usb_cfg);
    install_injection(host_agent);
    out_attempt_count = 0;
    `uvm_info("USB_BAD_PACKET_CRC", $sformatf("Registered one-shot host injection for %s", scenario_label()), UVM_LOW)
    fork
      begin
        fork
          begin
            while (out_attempt_count < 2) begin
              uvm_object tx_obj;
              svt_usb_packet tx_pkt;

              host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_ptrigger_data(tx_obj);
              if ($cast(tx_pkt, tx_obj) &&
                  tx_pkt.get_pid_name_val() == svt_usb_packet::OUT &&
                  tx_pkt.get_device_address_val() == p_sequencer.cfg.device_address &&
                  tx_pkt.get_ept_num_val() == 4'(endpoint.ep_number)) begin
                out_attempt_count++;
              end
            end
          end
          begin
            host_sequence.start(p_sequencer.host_sequencer);
            if (!host_sequence.completed) begin
              `uvm_fatal("USB_BAD_PACKET_CRC", "Bulk OUT host sequence returned incomplete")
            end
          end
          begin
            wait_for_sie_error_code(expected_error_code(), error_timeout, scenario_label());
          end
        join
      end
    join
    remove_injection(host_agent);
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b0;
    host_agent.reconfigure(usb_cfg);
    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);

    if (injected_packet_count() == 0 || out_attempt_count < 2) begin
      `uvm_fatal(
        "USB_BAD_PACKET_CRC",
        $sformatf(
          "The %s injection did not trigger a rejected attempt and retry (injected=%0d attempts=%0d)",
          scenario_label(),
          injected_packet_count(),
          out_attempt_count
        )
      )
    end
    wait_for_endpoint_interrupt(endpoint, error_timeout);
    verify_transfer(endpoint);

    completed = 1'b1;
    `uvm_info(
      "USB_BAD_PACKET_CRC",
      $sformatf("%s was detected and the retried bulk OUT completed with correct data", scenario_label()),
      UVM_LOW
    )
  endtask
endclass
