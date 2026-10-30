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

// Enters TEST_PACKET mode via CSR-directed DEVCMDSTAT.PHY_TEST_MODE programming
// and verifies the received test packet using the Synopsys SVT USB VIP's
// built-in test-mode receiver sequence and protocol packet notification.
//
// Scope note: This is a CSR-directed electrical-output test. Because
// usb_init_seq's EP0 responder only services the standard enumeration requests,
// TEST_PACKET is selected directly through DEVCMDSTAT.PHY_TEST_MODE after
// enumeration rather than via a valid EP0 SET_FEATURE(TEST_MODE) control
// transfer (protocol-entry compliance is outside the scope of this sequence;
// invalid SET_FEATURE(TEST_MODE) selector STALL and GET_STATUS recovery are
// covered in usb_unsupported_request_seq).
//
// Relies on the Synopsys SVT USB VIP's built-in
// svt_usb_protocol_service_20_receive_test_mode_data sequence
// (user_doc_html/usb_svt_uvm_user_guide/usage_notes/using_2_0_test_mode_with_utmi.html
// and sequences/class_svt_usb_protocol_service_20_receive_test_mode_data.html),
// built-in protocol packet event (host_agent.prot.NOTIFY_20_HOST_RX_PACKET
// in others/class_svt_usb_protocol.html), and built-in protocol/physical
// checks (enabled by default via register_default_chks = 1,
// enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_physical_20_sc.html):
//   - svt_usb_protocol_service_20_receive_test_mode_data:
//     Configures the SVT host protocol layer with
//     USB_20_TEST_MODE_TEST_PACKET (receive_test_mode_data = 1) to accept the
//     unsolicited USB 2.0 Section 7.1.20 TEST_PACKET.
//   - svt_usb_protocol::NOTIFY_20_HOST_RX_PACKET:
//     Delivers each decoded svt_usb_packet for consecutive DATA0 PID, 53-byte
//     payload, and CRC16 checking.
//   - svt_usb_protocol_ep_sc:
//     * packet_error_check: Checks PID check nibble, CRC16, bitstuff, and
//       framing on the received DATA0 test packet.
//   - svt_usb_physical_20_sc:
//     * utmi_signal_X_Z_check, chk_utmi_byte_time, chk_utmi_packet_begin_hs,
//       chk_utmi_packet_end_hs, chk_utmi_rxerror
class usb_test_packet_seq extends usb_base_seq;
  `uvm_object_utils(usb_test_packet_seq)

  localparam int unsigned TEST_PACKET_PAYLOAD_BYTES = 53;
  localparam int unsigned MIN_TEST_PACKET_COUNT = 2;
  localparam bit [15:0] TEST_PACKET_EXPECTED_CRC16 = 16'hceb6;
  localparam logic [2:0] TEST_PACKET_MODE = 3'b100;

  bit completed;
  time packet_timeout = 100us;

  function new(string name = "usb_test_packet_seq");
    super.new(name);
  endfunction

  // Return one payload byte (0..52) from the USB 2.0 Section 7.1.20 HS test packet pattern.
  function byte unsigned expected_payload_byte(int unsigned index);
    if (index inside {[0:8]}) return 8'h00;
    if (index inside {[9:16]}) return 8'haa;
    if (index inside {[17:24]}) return 8'hee;
    if (index == 25) return 8'hfe;
    if (index inside {[26:36]}) return 8'hff;
    case (index)
      37: return 8'h7f;
      38: return 8'hbf;
      39: return 8'hdf;
      40: return 8'hef;
      41: return 8'hf7;
      42: return 8'hfb;
      43: return 8'hfd;
      44: return 8'hfc;
      45: return 8'h7e;
      46: return 8'hbf;
      47: return 8'hdf;
      48: return 8'hef;
      49: return 8'hf7;
      50: return 8'hfb;
      51: return 8'hfd;
      52: return 8'h7e;
      default: return 8'h00;
    endcase
  endfunction

  // Validate PID, payload size, all 53 payload bytes, and CRC16 reported by the SVT packet.
  function void check_test_packet(svt_usb_packet packet);
    byte unsigned payload_bytes[];

    if (packet == null) begin
      `uvm_fatal("USB_TEST_PACKET", "Observed VIP packet is null")
      return;
    end
    if (packet.get_pid_name_val() !== svt_usb_packet::DATA0 ||
        packet.get_pid_check_val() !== 4'hc) begin
      `uvm_fatal(
        "USB_TEST_PACKET",
        $sformatf(
          "Test packet PID mismatch: pid=%s check=0x%0h expected DATA0/0xc",
          packet.get_pid_name_val().name(),
          packet.get_pid_check_val()
        )
      )
    end
    if (packet.get_payload_byte_count() != TEST_PACKET_PAYLOAD_BYTES) begin
      `uvm_fatal(
        "USB_TEST_PACKET",
        $sformatf(
          "Test packet payload contains %0d bytes, expected %0d",
          packet.get_payload_byte_count(),
          TEST_PACKET_PAYLOAD_BYTES
        )
      )
    end
    if (!packet.get_bytes(0, TEST_PACKET_PAYLOAD_BYTES, payload_bytes) ||
        payload_bytes.size() != TEST_PACKET_PAYLOAD_BYTES) begin
      `uvm_fatal("USB_TEST_PACKET", "Failed to extract 53-byte payload from SVT packet")
    end
    foreach (payload_bytes[index]) begin
      if (payload_bytes[index] !== expected_payload_byte(index)) begin
        `uvm_fatal(
          "USB_TEST_PACKET",
          $sformatf(
            "Test packet payload byte %0d is 0x%02h, expected 0x%02h",
            index,
            payload_bytes[index],
            expected_payload_byte(index)
          )
        )
      end
    end
    if (packet.crc16_error_detected(0) !== 1'b0 ||
        packet.get_crc16_val(1) !== TEST_PACKET_EXPECTED_CRC16) begin
      `uvm_fatal(
        "USB_TEST_PACKET",
        $sformatf(
          "Test packet CRC16 mismatch: crc16=0x%04h expected=0x%04h crc_error=%0b",
          packet.get_crc16_val(1),
          TEST_PACKET_EXPECTED_CRC16,
          packet.crc16_error_detected(0)
        )
      )
    end
    `uvm_info(
      "USB_TEST_PACKET",
      $sformatf(
        "Verified SVT DATA0 test packet: %0d payload bytes and CRC16=0x%04h",
        payload_bytes.size(),
        packet.get_crc16_val(1)
      ),
      UVM_LOW
    )
  endfunction

  // Enumerate, enable SVT test-mode receive, select TEST_PACKET, and verify the SVT packet.
  virtual task body();
    usb_init_seq init_sequence;
    svt_usb_agent host_agent;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_receive_test_mode_data receive_test_mode_seq;
    uvm_object rx_obj;
    svt_usb_packet observed_packet;
    process observer;
    process watchdog;
    int unsigned observed_packet_count;
    logic [31:0] command;
    logic [31:0] test_mode_mask;
    logic [31:0] test_mode_value;

    completed = 1'b0;
    `uvm_info("USB_TEST_PACKET", "Starting TEST_PACKET scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TEST_PACKET", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) ||
        host_agent.prot == null) begin
      `uvm_fatal("USB_TEST_PACKET", "Unable to resolve the SVT host agent protocol component")
    end

    // SVT's built-in svt_dropping_response_report_catcher passes a slash-less
    // ".*" pattern to uvm_re_match(), which UVM 1800.2 routes to uvm_glob_match()
    // where "." is literal. Suppress "Sequencer" warnings here to restore SVT's
    // intended default suppression for asynchronous service responses.
    p_sequencer.host_sequencer.prot_service_sequencer.set_report_severity_id_action(
        UVM_WARNING, "Sequencer", UVM_NO_ACTION);
    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "sof_off_sequence");
    sof_off_sequence.start(p_sequencer.host_sequencer.prot_service_sequencer);
    #1us;

    receive_test_mode_seq =
        svt_usb_protocol_service_20_receive_test_mode_data::type_id::create(
            "receive_test_mode_seq");
    receive_test_mode_seq.protocol_20_command_type_value =
        svt_usb_protocol_service::USB_20_TEST_MODE_TEST_PACKET;
    receive_test_mode_seq.start(p_sequencer.host_sequencer.prot_service_sequencer);

    test_mode_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE);
    test_mode_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE, TEST_PACKET_MODE);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command = (command & ~test_mode_mask) | test_mode_value;

    observed_packet_count = 0;
    `uvm_info(
      "USB_TEST_PACKET",
      $sformatf(
        "Selecting PHY_TEST_MODE=%0d and waiting up to %0t for %0d consecutive SVT DATA0 test packets",
        TEST_PACKET_MODE,
        packet_timeout,
        MIN_TEST_PACKET_COUNT
      ),
      UVM_LOW
    )
    fork
      begin
        observer = process::self();
        while (observed_packet_count < MIN_TEST_PACKET_COUNT) begin
          host_agent.prot.NOTIFY_20_HOST_RX_PACKET.wait_trigger_data(rx_obj);
          if (!$cast(observed_packet, rx_obj) || observed_packet == null) begin
            `uvm_fatal("USB_TEST_PACKET", "Observed NOTIFY_20_HOST_RX_PACKET object is not a valid svt_usb_packet")
          end
          if (observed_packet.get_pid_name_val() !== svt_usb_packet::DATA0) begin
            `uvm_fatal(
              "USB_TEST_PACKET",
              $sformatf(
                "Expected consecutive DATA0 test packets in TEST_PACKET mode, but observed PID %s",
                observed_packet.get_pid_name_val().name()
              )
            )
          end
          check_test_packet(observed_packet);
          observed_packet_count++;
        end
      end
      begin
        watchdog = process::self();
        #(packet_timeout);
        `uvm_fatal(
          "USB_TEST_PACKET",
          $sformatf(
            "Timed out after %0t waiting for %0d SVT DATA0 test packets (observed %0d)",
            packet_timeout,
            MIN_TEST_PACKET_COUNT,
            observed_packet_count
          )
        )
      end
    join_none
    #0;
    init_sequence.write_devcmdstat(command);
    wait (observed_packet_count >= MIN_TEST_PACKET_COUNT);
    if (observer.status() != process::FINISHED) observer.kill();
    watchdog.kill();

    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & test_mode_mask) !== test_mode_value) begin
      `uvm_fatal("USB_TEST_PACKET", $sformatf("PHY_TEST_MODE readback is 0x%08h, expected field value 0x%08h", command, test_mode_value))
    end

    // Directed RTL coverage stimulus for the USB_PIE debug-exit branch
    // (usbreg_phy_test_mode = "000") and CSR readback sanity check.
    command &= ~test_mode_mask;
    init_sequence.write_devcmdstat(command);
    #200ns;
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & test_mode_mask) !== 32'h0) begin
      `uvm_fatal("USB_TEST_PACKET", $sformatf("PHY_TEST_MODE did not clear on CSR readback: DEVCMDSTAT=0x%08h", command))
    end
    completed = 1'b1;
    `uvm_info(
      "USB_TEST_PACKET",
      $sformatf(
        "TEST_PACKET mode verified across %0d consecutive SVT DATA0 packets; PHY_TEST_MODE=0 stimulus and CSR readback checked",
        observed_packet_count
      ),
      UVM_LOW
    )
  endtask
endclass
