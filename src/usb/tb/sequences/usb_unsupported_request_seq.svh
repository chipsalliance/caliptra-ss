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

// Extends enumeration with firmware-directed EP0 Request Error STALL checks
// (USB 2.0 Section 9.4) for an undefined bRequest (0x7f) and a USB 2.0
// Section 9.4.9 / Table 9-7 reserved SET_FEATURE(TEST_MODE) selector (0x06 in
// wIndex[15:8]), followed by firmware-assisted EP0 GET_STATUS(DEVICE)
// recovery (USB 2.0 Section 8.5.3.4).
// Protocol STALL termination is verified by the SVT VIP via
// svt_usb_transfer::status == ABORTED and results_status[4] == 1'b1 in
// usb_unsupported_request_host_seq, and on the DUT side via INFO.ERR_CODE ==
// 4'ha (ERROR_SENT_STALL).
class usb_unsupported_request_seq extends usb_init_seq;
  `uvm_object_utils(usb_unsupported_request_seq)

  localparam logic [3:0] ERROR_SENT_STALL = 4'ha;
  localparam byte unsigned SET_FEATURE_REQUEST = 8'h03;
  localparam logic [15:0] TEST_MODE_FEATURE_SELECTOR = 16'h0002;
  // USB 2.0 Section 9.4.9 Table 9-7 reserves test-mode selectors 0x06..0x3F.
  localparam logic [15:0] RESERVED_TEST_MODE_INDEX = 16'h0600;

  function new(string name = "usb_unsupported_request_seq");
    super.new(name);
  endfunction

  virtual function int unsigned expected_setup_request_count();
    return super.expected_setup_request_count() + 3;
  endfunction

  // Direct the firmware model to arm EP0 STALL for the two unsupported
  // post-enumeration requests, then service GET_STATUS recovery via
  // super.service_setup_request().
  virtual task service_setup_request();
    byte unsigned request_type;
    byte unsigned request;
    logic [15:0] value;
    logic [15:0] index;
    logic [15:0] length;
    int unsigned post_enum_step;

    if (serviced_request_count < super.expected_setup_request_count()) begin
      super.service_setup_request();
      return;
    end

    post_enum_step = serviced_request_count - super.expected_setup_request_count();
    read_setup_packet(request_type, request, value, index, length);
    if (post_enum_step == 0) begin
      if (request_type != 8'h00 ||
          request != usb_unsupported_request_host_seq::DEFAULT_UNSUPPORTED_REQUEST ||
          value != usb_unsupported_request_host_seq::DEFAULT_REQUEST_VALUE ||
          index != usb_unsupported_request_host_seq::DEFAULT_REQUEST_INDEX ||
          length != usb_unsupported_request_host_seq::DEFAULT_PAYLOAD_BYTE_COUNT) begin
        `uvm_fatal(
          "USB_UNSUPPORTED_SEQ",
          $sformatf("Unexpected unsupported OUT SETUP: type=0x%02h request=0x%02h value=0x%04h index=0x%04h length=%0d", request_type, request, value, index, length)
        )
      end
      ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
      write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_in_buffer_offset));
      write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_out_buffer_offset));
      clear_setup_bit();
      serviced_request_count++;
      `uvm_info("USB_UNSUPPORTED_SEQ", "Armed EP0 IN and OUT STALL responses for unsupported request 0x7f", UVM_LOW)
    end else if (post_enum_step == 1) begin
      if (request_type != 8'h00 ||
          request != SET_FEATURE_REQUEST ||
          value != TEST_MODE_FEATURE_SELECTOR ||
          index != RESERVED_TEST_MODE_INDEX ||
          length != 0) begin
        `uvm_fatal(
          "USB_UNSUPPORTED_SEQ",
          $sformatf("Unexpected reserved SET_FEATURE(TEST_MODE) SETUP: type=0x%02h request=0x%02h value=0x%04h index=0x%04h length=%0d", request_type, request, value, index, length)
        )
      end
      ral_write32("INFO", p_sequencer.reg_model.combo.dev0_csr.INFO, 32'h0);
      write_endpoint_entry(ep0_in_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_in_buffer_offset));
      write_endpoint_entry(ep0_out_endpoint, endpoint_entry(1'b0, 1'b1, 0, ep0_out_buffer_offset));
      clear_setup_bit();
      serviced_request_count++;
      `uvm_info("USB_UNSUPPORTED_SEQ", "Armed EP0 IN and OUT STALL responses for reserved SET_FEATURE(TEST_MODE) selector 0x06", UVM_LOW)
    end else begin
      if (request_type != 8'h80 || request != 8'h00 || value != 16'h0000 || index != 16'h0000 || length != 2) begin
        `uvm_fatal(
          "USB_UNSUPPORTED_SEQ",
          $sformatf("Unexpected post-STALL recovery SETUP: type=0x%02h request=0x%02h value=0x%04h index=0x%04h length=%0d", request_type, request, value, index, length)
        )
      end
      super.service_setup_request();
      `uvm_info("USB_UNSUPPORTED_SEQ", "Serviced post-STALL GET_STATUS recovery request on EP0", UVM_LOW)
    end
  endtask

  // Run normal enumeration followed by the unsupported requests and GET_STATUS recovery.
  virtual task run_host_scenario();
    usb_init_host_seq init_host_sequence;
    usb_unsupported_request_host_seq unsupported_host_sequence;
    usb_unsupported_request_host_seq reserved_test_mode_host_sequence;
    byte unsigned status_payload[$];

    host_scenario_completed = 1'b0;
    status_payload = '{8'h00, 8'h00};
    init_host_sequence = usb_init_host_seq::type_id::create("init_host_sequence");
    init_host_sequence.control_endpoint = ep0_out_endpoint;
    init_host_sequence.device_address = p_sequencer.cfg.device_address;
    init_host_sequence.link_timeout = p_sequencer.cfg.link_timeout;
    init_host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    init_host_sequence.start(p_sequencer.host_sequencer);
    if (!init_host_sequence.completed) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "Enumeration host sequence returned incomplete")
    end

    unsupported_host_sequence = usb_unsupported_request_host_seq::type_id::create("unsupported_host_sequence");
    unsupported_host_sequence.control_endpoint = ep0_out_endpoint;
    unsupported_host_sequence.device_address = p_sequencer.cfg.device_address;
    unsupported_host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    unsupported_host_sequence.start(p_sequencer.host_sequencer);
    if (!unsupported_host_sequence.completed) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "Unsupported-request host sequence returned incomplete")
    end
    wait_for_sie_error_code(
      ERROR_SENT_STALL,
      p_sequencer.cfg.control_transfer_timeout,
      "EP0 unsupported request STALL"
    );

    reserved_test_mode_host_sequence =
        usb_unsupported_request_host_seq::type_id::create("reserved_test_mode_host_sequence");
    reserved_test_mode_host_sequence.control_endpoint = ep0_out_endpoint;
    reserved_test_mode_host_sequence.device_address = p_sequencer.cfg.device_address;
    reserved_test_mode_host_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    reserved_test_mode_host_sequence.unsupported_request = SET_FEATURE_REQUEST;
    reserved_test_mode_host_sequence.request_value = TEST_MODE_FEATURE_SELECTOR;
    reserved_test_mode_host_sequence.request_index = RESERVED_TEST_MODE_INDEX;
    reserved_test_mode_host_sequence.payload_byte_count = 0;
    reserved_test_mode_host_sequence.start(p_sequencer.host_sequencer);
    if (!reserved_test_mode_host_sequence.completed) begin
      `uvm_fatal("USB_UNSUPPORTED_SEQ", "Reserved SET_FEATURE(TEST_MODE) host sequence returned incomplete")
    end
    wait_for_sie_error_code(
      ERROR_SENT_STALL,
      p_sequencer.cfg.control_transfer_timeout,
      "EP0 reserved SET_FEATURE(TEST_MODE) selector STALL"
    );

    init_host_sequence.run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_STATUS,
      16'h0000,
      16'h0000,
      16'h0002,
      p_sequencer.cfg.device_address,
      expected_setup_request_count(),
      "GET_STATUS_post_stall_recovery",
      status_payload
    );

    host_scenario_completed = 1'b1;
    `uvm_info(
      "USB_UNSUPPORTED_SEQ",
      "Unsupported requests aborted with VIP STALL status and DUT ERROR_SENT_STALL, and EP0 recovered on GET_STATUS",
      UVM_LOW
    )
  endtask
endclass
