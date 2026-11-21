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
//
// Implements the host side of the standalone USB INIT enumeration scenario
// through the real Synopsys SVT USB 2.0 stack. After the link is enabled and
// SOF generation is running, the sequence performs these EP0 requests:
//
//   1. GET_DESCRIPTOR at the default address 0.
//   2. GET_STATUS at address 0.
//   3. SET_ADDRESS to assign device_address.
//   4. GET_DESCRIPTOR again at the assigned device_address.
//   5. GET_CONFIGURATION and confirm the device is unconfigured (value 0).
//   6. GET_DESCRIPTOR for the configuration header and its wTotalLength.
//   7. GET_DESCRIPTOR for that complete configuration tree.
//   8. SET_CONFIGURATION using the discovered bConfigurationValue.
//   9. GET_CONFIGURATION and confirm the discovered configuration is active.
//
// Every request must finish on the bus before its bounded timeout. Completion
// is accepted only when the SVT result, EP0 SETUP fields, device address, and
// payload length match intent; bytes are compared when independently expected.
// Discovery returns bytes for native validation and later stability checks.
// Run this sequence on the SVT
// host agent's virtual sequencer; usb_init_seq supplies the concurrent DUT-side
// EP0 service needed to answer these requests.
//
// Native protocol/link/PHY checks remain active. Descriptor validation is
// explicitly invoked for the device descriptor through the documented SVT
// framework method. Full configuration-tree validation remains a known gap;
// raw control transfers do not automatically execute framework checks.
class usb_init_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_init_host_seq)

  // USB 2.0 9.2.6.3 allows 2ms after SET_ADDRESS status. The bench already
  // uses USB_VIP_SCALEDOWN_TIMER_VALUES; its documented USB2 timer set has no
  // address-recovery entry. Keep the existing 5us allowance as explicit,
  // additional test-only scaling, not unscaled USB timing compliance.
  localparam time SET_ADDRESS_RECOVERY = 2ms;
  localparam int unsigned SET_ADDRESS_RECOVERY_SCALE = 400;
  localparam time SCALED_SET_ADDRESS_RECOVERY = SET_ADDRESS_RECOVERY / SET_ADDRESS_RECOVERY_SCALE;

  int unsigned validated_transfer_count;
  localparam int unsigned ENUMERATION_REQUEST_COUNT = 9;
  localparam int unsigned ALTERNATE_SELECTION_REQUEST_COUNT = 2;
  localparam byte unsigned DEVICE_DESCRIPTOR_TYPE = 1;
  localparam byte unsigned CONFIGURATION_DESCRIPTOR_TYPE = 2;
  localparam int unsigned DEVICE_DESCRIPTOR_LENGTH = 18;
  localparam int unsigned CONFIGURATION_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned CONFIGURATION_TOTAL_LENGTH_OFFSET = 2;
  localparam int unsigned CONFIGURATION_VALUE_OFFSET = 5;
  // USB 2.0 9.6.5 Table 9-12 interface descriptor fields.
  localparam byte unsigned INTERFACE_DESCRIPTOR_TYPE = 4;
  localparam int unsigned INTERFACE_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned INTERFACE_DESCRIPTOR_TYPE_OFFSET = 1;
  localparam int unsigned INTERFACE_NUMBER_OFFSET = 2;
  localparam int unsigned ALTERNATE_SETTING_OFFSET = 3;
  localparam int unsigned INTERFACE_ENDPOINT_COUNT_OFFSET = 4;
  byte unsigned discovered_payload[$];
  byte unsigned selected_configuration;
  byte unsigned selected_alternate_setting;
  byte unsigned selected_interface;

  // Scenario inputs. This sequence runs on the SVT sequencer, which has no
  // usb_env_cfg handle, so the parent scenario copies these from
  // usb_env_cfg before start. Link bring-up is bounded separately from each
  // individual control transfer.
  usb_endpoint_cfg control_endpoint;
  // The device service publishes completion of the initial reset/EP0 rearm.
  uvm_event dut_ep0_ready;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  time link_timeout = USB_DEFAULT_LINK_TIMEOUT;
  time control_transfer_timeout = USB_DEFAULT_CONTROL_TRANSFER_TIMEOUT;

  // Constructs the host sequence; body() performs the enumeration.
  function new(string name = "usb_init_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_INIT_HOST";
  endfunction

  // Derives the SVT success mask expected for the two zero-length host writes.
  // Other requests complete successfully with the default all-zero mask.
  function automatic bit [`SVT_USB_RESULTS_STATUS_SIZE - 1:0] derive_expected_results_status(svt_usb_types::setup_data_bmrequesttype_dir_enum expected_direction, svt_usb_types::setup_data_brequest_enum expected_request, bit [15:0] expected_length, byte unsigned expected_payload[$]);
    derive_expected_results_status = '0;
    if ((expected_direction === svt_usb_types::HOST_TO_DEVICE) &&
        ((expected_request === svt_usb_types::SET_ADDRESS) ||
         (expected_request === svt_usb_types::SET_CONFIGURATION) ||
         (expected_request === svt_usb_types::SET_INTERFACE) ||
         (expected_request === svt_usb_types::SET_FEATURE) ||
         (expected_request === svt_usb_types::CLEAR_FEATURE)) &&
        (expected_length === 16'd0) &&
        (expected_payload.size() === 0)) begin
      derive_expected_results_status[5] = 1'b1;
    end
  endfunction

  // Validates one ended-event object against immutable request intent.
  // Discovery disables only byte comparison and uses expected_length for size.
  // Returns one only for a successful, matching completion and provides a
  // complete rejection reason so a fatal report identifies the mismatch.
  function automatic bit validate_completed_transfer(
    uvm_object completed_object,
    svt_usb_types::setup_data_bmrequesttype_dir_enum expected_direction,
    svt_usb_types::setup_data_bmrequesttype_type_enum expected_request_type,
    svt_usb_types::setup_data_bmrequesttype_recipient_enum expected_recipient,
    svt_usb_types::setup_data_brequest_enum expected_request,
    bit [15:0] expected_value,
    bit [15:0] expected_index,
    bit [15:0] expected_length,
    bit [6:0] expected_device_address,
    byte unsigned expected_payload[$],
    output string failure_reason,
    input bit compare_payload_bytes = 1'b1
  );
    svt_usb_transfer transfer;
    bit [`SVT_USB_RESULTS_STATUS_SIZE - 1:0] expected_results_status;
    int observed_payload_count;
    int expected_payload_count;
    string transfer_context;

    // Reject invalid event data before reading any transfer fields.
    if (!cast_completed_transfer(completed_object, transfer, failure_reason)) begin
      return 1'b0;
    end

    // Build one expected result and one observed-versus-expected diagnostic
    // snapshot that every subsequent rejection can reuse.
    observed_payload_count = (transfer.payload === null) ? -1 : transfer.payload.byte_count;
    expected_payload_count = compare_payload_bytes ? expected_payload.size() : int'(expected_length);
    expected_results_status = derive_expected_results_status(expected_direction, expected_request, expected_length, expected_payload);
    transfer_context = $sformatf(
      {"expected status=ACCEPT results=0x%0h type=CONTROL_TRANSFER addr=%0d ep=0 ",
       "setup={dir=%s type=%s recipient=%s request=0x%02h value=0x%04h index=0x%04h length=%0d} payload_len=%0d; ",
       "observed status=%s results=0x%0h type=%s addr=%0d ep=%0d ",
       "setup={dir=%s type=%s recipient=%s request=0x%02h value=0x%04h index=0x%04h length=%0d} payload_len=%0d"},
      expected_results_status,
      expected_device_address,
      expected_direction.name(),
      expected_request_type.name(),
      expected_recipient.name(),
      expected_request,
      expected_value,
      expected_index,
      expected_length,
      expected_payload_count,
      transfer.status.name(),
      transfer.results_status,
      transfer.xfer_type.name(),
      transfer.device_address,
      transfer.endpoint_number,
      transfer.setup_data_bmrequesttype_dir.name(),
      transfer.setup_data_bmrequesttype_type.name(),
      transfer.setup_data_bmrequesttype_recipient.name(),
      transfer.setup_data_brequest,
      transfer.setup_data_w_value,
      transfer.setup_data_w_index,
      transfer.setup_data_w_length,
      observed_payload_count
    );

    // First establish that SVT accepted a control transfer on device EP0.
    if (transfer.status !== svt_sequence_item::ACCEPT) begin
      failure_reason = {"terminal status is not ACCEPT; ", transfer_context};
      return 1'b0;
    end
    if (transfer.results_status !== expected_results_status) begin
      failure_reason = {"results_status does not match the expected success mask; ", transfer_context};
      return 1'b0;
    end
    if (transfer.xfer_type !== svt_usb_transfer::CONTROL_TRANSFER) begin
      failure_reason = {"transfer kind is not CONTROL_TRANSFER; ", transfer_context};
      return 1'b0;
    end
    if (transfer.device_address !== expected_device_address) begin
      failure_reason = {"device address does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.endpoint_number !== 4'd0) begin
      failure_reason = {"endpoint is not EP0; ", transfer_context};
      return 1'b0;
    end
    if (transfer.rcvd_first_attempt_of_setup_with_payload_absent !== 1'b0) begin
      failure_reason = {"semantic SETUP fields are invalid; ", transfer_context};
      return 1'b0;
    end

    // Then prove that the completed SETUP packet is the request that was sent.
    if (transfer.setup_data_bmrequesttype_dir !== expected_direction) begin
      failure_reason = {"SETUP direction does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_bmrequesttype_type !== expected_request_type) begin
      failure_reason = {"SETUP request type does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_bmrequesttype_recipient !== expected_recipient) begin
      failure_reason = {"SETUP recipient does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_brequest !== expected_request) begin
      failure_reason = {"SETUP bRequest does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_w_value !== expected_value) begin
      failure_reason = {"SETUP wValue does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_w_index !== expected_index) begin
      failure_reason = {"SETUP wIndex does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.setup_data_w_length !== expected_length) begin
      failure_reason = {"SETUP wLength does not match; ", transfer_context};
      return 1'b0;
    end

    // Require a complete data stage, including an explicit empty payload object.
    // Compare bytes only when the caller supplied an independent expectation.
    if (transfer.payload === null) begin
      failure_reason = {"payload handle is null; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload.byte_count !== expected_payload_count) begin
      failure_reason = {"payload length does not match; ", transfer_context};
      return 1'b0;
    end
    if (compare_payload_bytes) foreach (expected_payload[byte_index]) begin
      bit [7:0] observed_payload_byte;

      observed_payload_byte = transfer.payload.get_byte_val(byte_index);
      if (observed_payload_byte !== expected_payload[byte_index]) begin
        failure_reason = {
          $sformatf(
            "payload byte %0d is 0x%02h instead of 0x%02h; ",
            byte_index,
            observed_payload_byte,
            expected_payload[byte_index]
          ),
          transfer_context
        };
        return 1'b0;
      end
    end

    return 1'b1;
  endfunction

  // Applies the production validator and counts only fully
  // accepted completions.
  task check_completed_transfer(
    int unsigned step_number,
    string label,
    uvm_object completed_object,
    svt_usb_types::setup_data_bmrequesttype_dir_enum expected_direction,
    svt_usb_types::setup_data_bmrequesttype_type_enum expected_request_type,
    svt_usb_types::setup_data_bmrequesttype_recipient_enum expected_recipient,
    svt_usb_types::setup_data_brequest_enum expected_request,
    bit [15:0] expected_value,
    bit [15:0] expected_index,
    bit [15:0] expected_length,
    bit [6:0] expected_device_address,
    byte unsigned expected_payload[$],
    input bit compare_payload_bytes = 1'b1
  );
    string failure_reason;

    if (!validate_completed_transfer(
          completed_object,
          expected_direction,
          expected_request_type,
          expected_recipient,
          expected_request,
          expected_value,
          expected_index,
          expected_length,
          expected_device_address,
          expected_payload,
          failure_reason,
          compare_payload_bytes
        )) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("Step %0d %s completion rejected: %s", step_number, label, failure_reason))
    end
    validated_transfer_count++;
    `uvm_info("USB_INIT_HOST", $sformatf("Step %0d %s completion validated: payload_bytes=%0d byte_check=%s validated_count=%0d",
      step_number, label, compare_payload_bytes ? expected_payload.size() : int'(expected_length),
      compare_payload_bytes ? "independent expectation" : "discovery; no independent byte oracle", validated_transfer_count), UVM_LOW)
  endtask

  // Submits one control request and validates the resulting completion against
  // its intent. The shared observer is armed before submission so a fast
  // completion cannot be missed, and its timeout bounds the request.
  task run_control_transfer(
    svt_usb_types::setup_data_bmrequesttype_dir_enum direction,
    svt_usb_types::setup_data_brequest_enum request,
    bit [15:0] value,
    bit [15:0] index,
    bit [15:0] length,
    bit [6:0] device_address,
    int unsigned step_number,
    string label,
    byte unsigned expected_payload[$],
    bit discover_descriptor = 1'b0,
    svt_usb_types::setup_data_bmrequesttype_recipient_enum recipient = svt_usb_types::BMREQ_DEVICE
  );
    svt_usb_transfer request_transfer;
    uvm_sequence_item response;
    uvm_object completed_object;
    svt_usb_transfer completed_transfer;
    string transfer_label;
    string failure_reason;

    transfer_label = $sformatf("Step %0d %s", step_number, label);
    request_transfer = svt_usb_transfer::type_id::create({label, "_request"});
    `uvm_info(
      "USB_INIT_HOST",
      $sformatf(
        "Submitting %s: addr=%0d request=0x%02h value=0x%04h length=%0d",
        transfer_label,
        device_address,
        request,
        value,
        length
      ),
      UVM_LOW
    )

    begin_transfer_watch(transfer_label, control_transfer_timeout);
    start_item(request_transfer, -1, p_sequencer.xfer_sequencer);
    request_transfer.cfg = usb_cfg;
    // Pin the device, control endpoint, and ustream configuration indices.
    // SVT disables their randomization so the request keeps these selections.
    request_transfer.fix_anchors(0, control_endpoint.anchor_index, 0);
    if (!request_transfer.randomize() with {
          xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
          device_address == local::device_address;
          setup_data_bmrequesttype_dir == direction;
          setup_data_bmrequesttype_type == svt_usb_types::STANDARD;
          setup_data_bmrequesttype_recipient == local::recipient;
          setup_data_brequest == request;
          setup_data_w_value == value;
          setup_data_w_index == index;
          setup_data_w_length == length;
        }) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("Unable to randomize %s", transfer_label))
    end
    finish_item(request_transfer);
    // SVT also routes a UVM response for each request. Consume it by transaction
    // ID before retiring the watch so response delivery shares the same deadline
    // and cannot accumulate past UVM's bounded response queue.
    get_response(response, request_transfer.get_transaction_id());
    if (response == null || response.get_sequence_id() != request_transfer.get_sequence_id()) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("%s received an invalid routed response", transfer_label))
    end
    end_transfer_watch(completed_object);
    check_transfer_correlation(transfer_label, request_transfer, completed_object);

    // Discovery has no fixture-byte oracle. Check the request/completion
    // envelope below; body() separately invokes the native device validator.
    if (discover_descriptor) begin
      if (!cast_completed_transfer(completed_object, completed_transfer, failure_reason)) begin
        `uvm_fatal("USB_INIT_HOST", failure_reason)
      end
      if (completed_transfer.payload == null) begin
        `uvm_fatal("USB_INIT_HOST", "Descriptor response has no payload")
      end
      if (completed_transfer.payload.byte_count != length) begin
        `uvm_fatal("USB_INIT_HOST", "Descriptor response length differs from requested discovery length")
      end
      discovered_payload.delete();
      for (int unsigned byte_index = 0; byte_index < length; byte_index++) begin
        discovered_payload.push_back(completed_transfer.payload.get_byte_val(byte_index));
      end
    end

    check_completed_transfer(
      step_number,
      label,
      completed_object,
      direction,
      svt_usb_types::STANDARD,
      recipient,
      request,
      value,
      index,
      length,
      device_address,
      expected_payload,
      !discover_descriptor
    );
  endtask

  // Wait for device-side reset writes, independently of native link readiness.
  task wait_for_dut_ep0_ready();
    if (dut_ep0_ready === null) begin
      `uvm_fatal("USB_INIT_HOST", "No device-side EP0 reset-readiness event was supplied")
    end
    `uvm_info("USB_INIT_HOST", "Waiting for device reset handling and EP0 rearm", UVM_LOW)
    dut_ep0_ready.wait_on();
    `uvm_info("USB_INIT_HOST", "Device reset handling and EP0 rearm complete; starting checked enumeration traffic", UVM_LOW)
  endtask

  // Reuse SVT's device-descriptor validator on the complete bus response.
  // See get_descriptor_system_virtual_sequence::validate_descriptor_data and
  // virtual_sequencer::get_err_check in the installed USB SVT class reference.
  function void validate_device_descriptor(byte unsigned payload[$]);
    svt_usb_device_framework_get_descriptor_system_virtual_sequence validator;
    svt_usb_configuration remote_cfg;
    svt_usb_agent_configuration device_cfg;
    svt_err_check checks;
    svt_usb_device_framework_sc framework_checks;
    bit [7:0] descriptor_data[];

    if (!uvm_config_db#(svt_usb_configuration)::get(host_agent, "", "remote_cfg", remote_cfg) ||
        !$cast(device_cfg, remote_cfg) || device_cfg == null) begin
      `uvm_fatal("USB_INIT_HOST", "Descriptor validation requires the configured remote device PHY context")
    end
    checks = p_sequencer.get_err_check(this);
    if (!$cast(framework_checks, p_sequencer.get_err_check(this, "device_framework_checks")) ||
        checks == null || framework_checks == null) begin
      `uvm_fatal("USB_INIT_HOST", "Native descriptor validation check infrastructure is unavailable")
    end
    descriptor_data = new[payload.size()];
    foreach (payload[index]) descriptor_data[index] = payload[index];
    validator = svt_usb_device_framework_get_descriptor_system_virtual_sequence::type_id::create("descriptor_validator");
    `uvm_info("USB_INIT_HOST", $sformatf("Invoking native device descriptor validation: bytes=%0d", payload.size()), UVM_LOW)
    if (!(validator.validate_descriptor_data(svt_usb_types::DESC_TYPE_DEVICE, descriptor_data,
          {DEVICE_DESCRIPTOR_TYPE, 8'h00}, device_cfg, checks, framework_checks, 0) === 1'b1)) begin
      `uvm_fatal("USB_INIT_HOST", "Native validation rejected the device descriptor")
    end
    `uvm_info("USB_INIT_HOST", $sformatf("Native device descriptor validation completed: bytes=%0d", payload.size()), UVM_LOW)
  endfunction

  // Discover the populated alternate of this single-interface fixture. The
  // walk chooses stimulus; it is not full configuration-descriptor validation.
  function void discover_interface(byte unsigned payload[$]);
    int unsigned offset;
    selected_alternate_setting = 0;
    selected_interface = 0;
    offset = CONFIGURATION_DESCRIPTOR_LENGTH;
    while (offset < payload.size()) begin
      int unsigned descriptor_length;
      descriptor_length = payload[offset];
      if (descriptor_length < 2 || offset + descriptor_length > payload.size()) begin
        `uvm_fatal("USB_INIT_HOST", "Cannot select an interface from a truncated descriptor tree")
      end
      if (payload[offset + INTERFACE_DESCRIPTOR_TYPE_OFFSET] == INTERFACE_DESCRIPTOR_TYPE &&
          descriptor_length >= INTERFACE_DESCRIPTOR_LENGTH && payload[offset + INTERFACE_ENDPOINT_COUNT_OFFSET] != 0) begin
        selected_interface = payload[offset + INTERFACE_NUMBER_OFFSET];
        selected_alternate_setting = payload[offset + ALTERNATE_SETTING_OFFSET];
        return;
      end
      offset += descriptor_length;
    end
  endfunction

  // Select configuration descriptor index zero, using only its bus response
  // to determine wTotalLength and bConfigurationValue.
  virtual task body();
    byte unsigned no_payload[$];
    byte unsigned descriptor_payload[$];
    byte unsigned status_payload[$];
    byte unsigned unconfigured_payload[$];
    byte unsigned configured_payload[$];
    byte unsigned configuration_header[$];
    int unsigned configuration_length;

    completed = 1'b0;
    validated_transfer_count = 0;
    if (control_endpoint == null || !control_endpoint.anchor_index_valid) begin
      `uvm_fatal("USB_INIT_HOST", "control_endpoint must be set to an applied EP0 configuration before start")
    end

    selected_configuration = 0;
    discovered_payload.delete();
    // USB 2.0 sections 9.4.4 and 9.4.5: bus-powered fixture status and
    // configuration state before SET_CONFIGURATION.
    status_payload = '{8'h00, 8'h00};
    unconfigured_payload = '{8'h00};

    // Resolve the host agent, configuration, and shared status supplied by
    // usb_env; the shared status is required for the link wait below.
    resolve_host_context(1'b1);

    if (device_address == 0) begin
      `uvm_fatal("USB_INIT_HOST", "device_address must be 1-127")
    end
    `uvm_info("USB_INIT_HOST", $sformatf("Starting USB INIT host enumeration from address 0 to address %0d", device_address), UVM_LOW)

    // Bring up periodic USB framing before issuing the first EP0 request.
    wait_for_link_enabled(link_timeout);
    begin
      svt_usb_protocol_service_20_sof_on_sequence sof_sequence;
      sof_sequence = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_sequence");
      sof_sequence.start(p_sequencer.prot_service_sequencer);
      `uvm_info("USB_INIT_HOST", "SOF generation started", UVM_LOW)
    end
    // Native link/SOF readiness does not establish completion of DUT CSR writes.
    wait_for_dut_ep0_ready();

    // Steps 1-3 discover the default-address device, inspect its status, and
    // request the transition from address 0 to device_address.
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      {DEVICE_DESCRIPTOR_TYPE, 8'h00},
      16'h0000,
      16'(DEVICE_DESCRIPTOR_LENGTH),
      0,
      1,
      "GET_DESCRIPTOR_address_0",
      no_payload,
      1'b1
    );
    descriptor_payload = discovered_payload;
    if (descriptor_payload.size() < DEVICE_DESCRIPTOR_LENGTH) begin
      `uvm_fatal("USB_INIT_HOST", "Device descriptor discovery returned a truncated descriptor")
    end
    validate_device_descriptor(descriptor_payload);
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_STATUS,
      16'h0000,
      16'h0000,
      16'h0002,
      0,
      2,
      "GET_STATUS_address_0",
      status_payload
    );
    run_control_transfer(
      svt_usb_types::HOST_TO_DEVICE,
      svt_usb_types::SET_ADDRESS,
      16'(device_address),
      16'h0000,
      16'h0000,
      0,
      3,
      $sformatf("SET_ADDRESS_%0d", device_address),
      no_payload
    );

    `uvm_info("USB_INIT_HOST",
              $sformatf("Waiting for SET_ADDRESS recovery: USB2=%0t additional_test_scale=%0d effective=%0t; not unscaled timing coverage",
                        SET_ADDRESS_RECOVERY, SET_ADDRESS_RECOVERY_SCALE, SCALED_SET_ADDRESS_RECOVERY), UVM_LOW)
    #(SCALED_SET_ADDRESS_RECOVERY);
    `uvm_info("USB_INIT_HOST", "Scaled SET_ADDRESS recovery elapsed; reconfiguring host before checked addressed traffic", UVM_LOW)
    // Status completion plus the scaled recovery gates host reconfiguration.
    // The next addressed transfer and final CSR readback prove activation.
    begin
      svt_usb_configuration addressed_cfg;

      // Reconfigure from a copy so the configuration the agent was built
      // with is never edited in place.
      if (!$cast(addressed_cfg, usb_cfg.clone())) begin
        `uvm_fatal("USB_INIT_HOST", "Unable to clone the SVT host configuration")
      end
      addressed_cfg.remote_device_cfg[0].device_address = device_address;
      host_agent.reconfigure(addressed_cfg);
      usb_cfg = addressed_cfg;
    end
    `uvm_info("USB_INIT_HOST", $sformatf("Reconfigured the SVT host for device address %0d", device_address), UVM_LOW)

    // Prove descriptor stability at the assigned address, then discover the
    // complete configuration before selecting it.
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      {DEVICE_DESCRIPTOR_TYPE, 8'h00},
      16'h0000,
      16'(DEVICE_DESCRIPTOR_LENGTH),
      device_address,
      4,
      $sformatf("GET_DESCRIPTOR_address_%0d", device_address),
      descriptor_payload
    );
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_CONFIGURATION,
      16'h0000,
      16'h0000,
      16'h0001,
      device_address,
      5,
      "GET_CONFIGURATION_before_set",
      unconfigured_payload
    );
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      {CONFIGURATION_DESCRIPTOR_TYPE, 8'h00},
      16'h0000,
      16'(CONFIGURATION_DESCRIPTOR_LENGTH),
      device_address,
      6,
      "GET_CONFIGURATION_DESCRIPTOR_header",
      no_payload,
      1'b1
    );
    configuration_header = discovered_payload;
    if (configuration_header.size() < CONFIGURATION_DESCRIPTOR_LENGTH) begin
      `uvm_fatal("USB_INIT_HOST", "Configuration discovery returned a truncated header")
    end
    configuration_length = int'(configuration_header[CONFIGURATION_TOTAL_LENGTH_OFFSET]) |
                           (int'(configuration_header[CONFIGURATION_TOTAL_LENGTH_OFFSET + 1]) << 8);
    // USB 2.0 section 9.6.3: wTotalLength includes the configuration header.
    if (configuration_length < CONFIGURATION_DESCRIPTOR_LENGTH) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("Configuration wTotalLength=%0d is shorter than its header", configuration_length))
    end
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      {CONFIGURATION_DESCRIPTOR_TYPE, 8'h00},
      16'h0000,
      16'(configuration_length),
      device_address,
      7,
      "GET_CONFIGURATION_DESCRIPTOR_full",
      no_payload,
      1'b1
    );
    if (discovered_payload.size() < configuration_length || discovered_payload.size() < configuration_header.size()) begin
      `uvm_fatal("USB_INIT_HOST", "Configuration tree discovery returned fewer bytes than its declared length or saved header")
    end
    foreach (configuration_header[byte_index]) begin
      if (configuration_header[byte_index] != discovered_payload[byte_index]) begin
        `uvm_fatal("USB_INIT_HOST", "Configuration header changed between discovery requests")
      end
    end
    selected_configuration = discovered_payload[CONFIGURATION_VALUE_OFFSET];
    discover_interface(discovered_payload);
    configured_payload = '{selected_configuration};
    run_control_transfer(
      svt_usb_types::HOST_TO_DEVICE,
      svt_usb_types::SET_CONFIGURATION,
      16'(selected_configuration),
      16'h0000,
      16'h0000,
      device_address,
      8,
      $sformatf("SET_CONFIGURATION_%0d", selected_configuration),
      no_payload
    );
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_CONFIGURATION,
      16'h0000,
      16'h0000,
      16'h0001,
      device_address,
      9,
      "GET_CONFIGURATION_after_set",
      configured_payload
    );
    if (selected_alternate_setting != 0) begin
      byte unsigned interface_payload[$];
      interface_payload = '{selected_alternate_setting};
      `uvm_info("USB_INIT_HOST", $sformatf("Selecting discovered interface=%0d alternate=%0d before endpoint traffic",
        selected_interface, selected_alternate_setting), UVM_LOW)
      run_control_transfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::SET_INTERFACE,
        16'(selected_alternate_setting), 16'(selected_interface), 0, device_address, 10, "SET_INTERFACE", no_payload, 1'b0,
        svt_usb_types::BMREQ_INTERFACE);
      run_control_transfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_INTERFACE,
        0, 16'(selected_interface), 1, device_address, 11, "GET_INTERFACE", interface_payload, 1'b0,
        svt_usb_types::BMREQ_INTERFACE);
      `uvm_info("USB_INIT_HOST", "Alternate selection and GET_INTERFACE readback completed; periodic traffic admitted", UVM_LOW)
    end

    // Each transfer watch already observed terminal completion.
    if (validated_transfer_count !== (ENUMERATION_REQUEST_COUNT +
        (selected_alternate_setting != 0 ? ALTERNATE_SELECTION_REQUEST_COUNT : 0))) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("USB INIT validated an unexpected number of control transfers: %0d alternate=%0d",
        validated_transfer_count, selected_alternate_setting))
    end
    completed = 1'b1;
    `uvm_info("USB_INIT_HOST", $sformatf("USB INIT host enumeration complete: validated_count=%0d address=%0d configuration=%0d", validated_transfer_count, device_address, selected_configuration), UVM_LOW)
  endtask
endclass
