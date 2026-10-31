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

// Enters USB 2.0 Section 7.1.20 electrical test modes (TEST_J, TEST_K, and
// TEST_SE0_NAK) via CSR-directed DEVCMDSTAT.PHY_TEST_MODE programming and
// verifies them using the Synopsys SVT USB VIP's built-in test-mode receiver
// sequences, status notifications, and protocol/physical checks.
//
// Scope note: These are CSR-directed electrical-output tests. Because
// usb_init_seq's EP0 responder only services the standard enumeration requests,
// the target test mode is selected directly through DEVCMDSTAT.PHY_TEST_MODE
// after enumeration rather than via a valid EP0 SET_FEATURE(TEST_MODE) control
// transfer (protocol-entry compliance is outside the scope of this sequence;
// invalid SET_FEATURE(TEST_MODE) selector STALL and GET_STATUS recovery are
// covered in usb_unsupported_request_seq).
//
// Relies on the Synopsys SVT USB VIP's built-in
// svt_usb_protocol_service_20_receive_test_mode_data and
// svt_usb_protocol_service_abort_current_transfer_sequence sequences
// (user_doc_html/usb_svt_uvm_user_guide/usage_notes/using_2_0_test_mode_with_utmi.html,
// sequences/class_svt_usb_protocol_service_20_receive_test_mode_data.html, and
// sequences/class_svt_usb_protocol_service_abort_current_transfer_sequence.html),
// status notifications (phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE in
// status/class_svt_usb_status.html and host_agent.prot.NOTIFY_20_HOST_RX_PACKET
// in others/class_svt_usb_protocol.html), and built-in protocol/physical checks
// (enabled by default via register_default_chks = 1, enable_default_chks = 1 in
// protocolChecks.html, coverage/class_svt_usb_protocol_ep_sc.html, and
// coverage/class_svt_usb_physical_20_sc.html):
//   - svt_usb_protocol_service_20_receive_test_mode_data:
//     Arms the SVT host protocol layer for USB_20_TEST_MODE_TEST_J,
//     USB_20_TEST_MODE_TEST_K, or USB_20_TEST_MODE_TEST_SE0_NAK.
//   - svt_usb_status::NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE:
//     Signals transitions on physical_usb_20_linestate so TEST_J and TEST_K
//     entry and continuous hold across line_hold_time (5 us) are verified.
//   - svt_usb_protocol::NOTIFY_20_HOST_RX_PACKET &
//     svt_usb_protocol_service_abort_current_transfer_sequence:
//     Verifies the device returns NAK to an IN token in TEST_SE0_NAK mode even
//     when an IN endpoint buffer is armed and ready.
//   - svt_usb_protocol_ep_sc & svt_usb_physical_20_sc:
//     * packet_error_check, valid_device_response_check, utmi_signal_X_Z_check
class usb_test_modes_seq extends usb_base_seq;
  `uvm_object_utils(usb_test_modes_seq)

  // USB 2.0 section 7.1.20 and Table 9-7 test selectors.
  localparam logic [2:0] TEST_J_MODE = 3'd1;
  localparam logic [2:0] TEST_K_MODE = 3'd2;
  localparam logic [2:0] TEST_SE0_NAK_MODE = 3'd3;
  localparam logic [3:0] ERROR_SENT_RECEIVED_NAK = 4'h9;
  localparam int unsigned READY_IN_BYTES = 16;
  localparam logic [31:0] READY_IN_BUFFER = 32'h0000_0200;
  string mode_name;
  time mode_timeout = 100us;
  time line_hold_time = 5us;
  bit completed;

  function new(string name = "usb_test_modes_seq");
    super.new(name);
  endfunction

  virtual task body();
    usb_init_seq init_sequence;
    svt_usb_agent host_agent;
    svt_usb_status phy_status;
    svt_usb_protocol_service_20_sof_off_sequence sof_off;
    svt_usb_protocol_service_20_receive_test_mode_data receiver;
    usb_test_mode_nak_host_seq in_probe;
    usb_endpoint_cfg endpoint;
    usb_ep_entry_t entry;
    process observer;
    process watchdog;
    svt_usb_types::linestate_value_enum expected_line;
    logic [2:0] selector;
    logic [31:0] command;
    logic [31:0] mode_mask;
    logic [31:0] mode_value;
    bit mode_observed;

    completed = 1'b0;
    mode_observed = 1'b0;
    receiver = svt_usb_protocol_service_20_receive_test_mode_data::type_id::create("receiver");
    case (mode_name)
      "TEST_J": begin
        selector = TEST_J_MODE;
        expected_line = svt_usb_types::LINESTATE_J;
        receiver.protocol_20_command_type_value = svt_usb_protocol_service::USB_20_TEST_MODE_TEST_J;
      end
      "TEST_K": begin
        selector = TEST_K_MODE;
        expected_line = svt_usb_types::LINESTATE_K;
        receiver.protocol_20_command_type_value = svt_usb_protocol_service::USB_20_TEST_MODE_TEST_K;
      end
      "TEST_SE0_NAK": begin
        selector = TEST_SE0_NAK_MODE;
        receiver.protocol_20_command_type_value = svt_usb_protocol_service::USB_20_TEST_MODE_TEST_SE0_NAK;
      end
      default: `uvm_fatal("USB_TEST_MODES", $sformatf("Unsupported electrical test mode '%s'", mode_name))
    endcase
    `uvm_info("USB_TEST_MODES", $sformatf("Enumerating a fresh device for %s", mode_name), UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TEST_MODES", "Enumeration did not complete")
    end
    if (!$cast(host_agent, p_sequencer.host_sequencer.get_parent()) || host_agent.prot == null) begin
      `uvm_fatal("USB_TEST_MODES", "Native host protocol component is unavailable")
    end
    phy_status = p_sequencer.host_sequencer.get_remote_shared_status(this);
    if (phy_status == null || phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE == null) begin
      `uvm_fatal("USB_TEST_MODES", "Native remote-PHY line-state observation is unavailable")
    end
    // SVT's built-in svt_dropping_response_report_catcher passes a slash-less
    // ".*" pattern to uvm_re_match(), which UVM 1800.2 routes to uvm_glob_match()
    // where "." is literal. Suppress "Sequencer" warnings here to restore SVT's
    // intended default suppression for asynchronous service responses.
    p_sequencer.host_sequencer.prot_service_sequencer.set_report_severity_id_action(
        UVM_WARNING, "Sequencer", UVM_NO_ACTION);
    sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
    sof_off.start(p_sequencer.host_sequencer.prot_service_sequencer);
    // Let any already-started SOF finish before defining the mode-entry baseline.
    #1us;
    if (selector != TEST_SE0_NAK_MODE && phy_status.physical_usb_20_linestate === expected_line) begin
      `uvm_fatal("USB_TEST_MODES", "The requested line state predates the DUT test-mode command")
    end
    mode_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE);
    mode_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE, selector);
    if (selector == TEST_SE0_NAK_MODE) begin
      endpoint = get_endpoint(1, USB_DIRECTION_IN);
      check_buffer_clear_of_endpoint_list("SE0_NAK ready IN", READY_IN_BUFFER, READY_IN_BYTES);
      fill_endpoint_buffer(READY_IN_BUFFER, READY_IN_BYTES, 32'h5a96_3cc3);
      arm_endpoint(endpoint, READY_IN_BYTES, READY_IN_BUFFER, entry);
    end
    receiver.start(p_sequencer.host_sequencer.prot_service_sequencer);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command = (command & ~mode_mask) | mode_value;

    // The vendor example waits for J/K or checks IN/NAK in receiver mode:
    // sequences/class_svt_usb_20_hs_30_na_test_mode_phy_system_virtual_sequence.html.
    fork
      begin
        observer = process::self();
        if (selector != TEST_SE0_NAK_MODE) begin
          while (!mode_observed) begin
            phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE.wait_trigger();
            mode_observed = phy_status.physical_usb_20_linestate === expected_line;
          end
        end
      end
      begin
        time watchdog_timeout;

        watchdog = process::self();
        // Give the outer watchdog margin beyond in_probe's transfer_timeout so
        // the inner host sequence timeout fires first if the probe stalls.
        watchdog_timeout = (selector == TEST_SE0_NAK_MODE) ? (mode_timeout + 20us) : mode_timeout;
        #(watchdog_timeout);
        `uvm_fatal("USB_TEST_MODES", $sformatf("No native DUT %s observation within %0t", mode_name, watchdog_timeout))
      end
    join_none
    #0;
    `uvm_info("USB_TEST_MODES", $sformatf("Native receiver armed; selecting DUT %s", mode_name), UVM_LOW)
    init_sequence.write_devcmdstat(command);
    if (selector == TEST_SE0_NAK_MODE) begin
      ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
      in_probe = usb_test_mode_nak_host_seq::type_id::create("in_probe");
      in_probe.device_address = p_sequencer.cfg.device_address;
      in_probe.target_endpoint = endpoint;
      in_probe.payload_byte_count = READY_IN_BYTES;
      in_probe.transfer_timeout = mode_timeout;
      in_probe.start(p_sequencer.host_sequencer, this);
      if (!in_probe.completed) `uvm_fatal("USB_TEST_MODES", "Native IN/NAK probe did not complete")
      wait_for_sie_error_code(
        ERROR_SENT_RECEIVED_NAK,
        p_sequencer.cfg.transfer_timeout,
        "TEST_SE0_NAK IN token"
      );
      mode_observed = 1'b1;
    end
    wait (mode_observed);
    if (observer.status() != process::FINISHED) observer.kill();
    watchdog.kill();
    if (selector != TEST_SE0_NAK_MODE) begin
      bit line_changed;

      line_changed = (phy_status.physical_usb_20_linestate !== expected_line);
      fork
        begin
          fork
            begin
              phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE.wait_trigger();
              line_changed = 1'b1;
            end
            begin
              #(line_hold_time);
            end
          join_any
          disable fork;
        end
      join
      if (line_changed || phy_status.physical_usb_20_linestate !== expected_line) begin
        `uvm_fatal(
          "USB_TEST_MODES",
          $sformatf(
            "%s did not remain continuously driven at %s for %0t (observed=%s)",
            mode_name,
            expected_line.name(),
            line_hold_time,
            phy_status.physical_usb_20_linestate.name()
          )
        )
      end
    end
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & mode_mask) !== mode_value) begin
      `uvm_fatal("USB_TEST_MODES", "DUT test-mode selector did not remain programmed")
    end
    if (selector == TEST_SE0_NAK_MODE) begin
      logic [2:0] reserved_modes[3] = '{3'd5, 3'd6, 3'd7};

      read_endpoint_entry(endpoint, entry);
      if (entry.active !== 1'b1 || entry.nbytes !== READY_IN_BYTES) begin
        `uvm_fatal("USB_TEST_MODES", "TEST_SE0_NAK consumed the ready IN allocation")
      end
      // Directed RTL coverage stimulus for reserved PHY_TEST_MODE encodings (5..7)
      // and the USB_PIE debug-exit branch (0) while in BUS_EVENT_TEST_MODE,
      // followed by a CSR readback sanity check.
      foreach (reserved_modes[idx]) begin
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        command = (command & ~mode_mask) |
                  ral_field_value(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE, reserved_modes[idx]);
        init_sequence.write_devcmdstat(command);
        #200ns;
      end
      ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
      command &= ~mode_mask;
      init_sequence.write_devcmdstat(command);
      #200ns;
      ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
      if ((command & mode_mask) !== 32'h0) begin
        `uvm_fatal("USB_TEST_MODES", "DUT test-mode selector did not clear on CSR readback")
      end
    end
    completed = 1'b1;
    // An upstream-facing port exits test mode by power cycle, not mode switching.
    `uvm_info("USB_TEST_MODES", $sformatf("%s observed through native VIP facilities; ending this fresh-device run", mode_name), UVM_LOW)
  endtask
endclass
