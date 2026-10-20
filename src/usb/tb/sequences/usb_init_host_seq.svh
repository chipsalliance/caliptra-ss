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
// returned payload all match the request intent. Run this sequence on the SVT
// host agent's virtual sequencer; usb_init_seq supplies the concurrent DUT-side
// EP0 service needed to answer these requests.
class usb_init_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_init_host_seq)

  int unsigned validated_transfer_count;
  localparam int unsigned ENUMERATION_REQUEST_COUNT = 9;
  // USB 2.0 chapter 9 descriptor types, lengths, and field offsets.
  localparam byte unsigned DEVICE_DESCRIPTOR_TYPE = 1;
  localparam byte unsigned CONFIGURATION_DESCRIPTOR_TYPE = 2;
  localparam byte unsigned INTERFACE_DESCRIPTOR_TYPE = 4;
  localparam byte unsigned ENDPOINT_DESCRIPTOR_TYPE = 5;
  localparam int unsigned DEVICE_DESCRIPTOR_LENGTH = 18;
  localparam int unsigned CONFIGURATION_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned INTERFACE_DESCRIPTOR_LENGTH = 9;
  localparam int unsigned ENDPOINT_DESCRIPTOR_LENGTH = 7;
  localparam int unsigned DESCRIPTOR_LENGTH_OFFSET = 0;
  localparam int unsigned DESCRIPTOR_TYPE_OFFSET = 1;
  localparam int unsigned DEVICE_USB_VERSION_OFFSET = 2;
  localparam int unsigned DEVICE_EP0_PACKET_SIZE_OFFSET = 7;
  localparam int unsigned DEVICE_CONFIGURATION_COUNT_OFFSET = 17;
  localparam int unsigned CONFIGURATION_TOTAL_LENGTH_OFFSET = 2;
  localparam int unsigned CONFIGURATION_INTERFACE_COUNT_OFFSET = 4;
  localparam int unsigned CONFIGURATION_VALUE_OFFSET = 5;
  localparam int unsigned CONFIGURATION_ATTRIBUTES_OFFSET = 7;
  localparam int unsigned CONFIGURATION_POWER_OFFSET = 8;
  localparam int unsigned INTERFACE_NUMBER_OFFSET = 2;
  localparam int unsigned INTERFACE_ALTERNATE_OFFSET = 3;
  localparam int unsigned INTERFACE_ENDPOINT_COUNT_OFFSET = 4;
  localparam int unsigned ENDPOINT_ADDRESS_OFFSET = 2;
  localparam int unsigned ENDPOINT_ATTRIBUTES_OFFSET = 3;
  localparam int unsigned ENDPOINT_PACKET_SIZE_OFFSET = 4;
  localparam int unsigned ENDPOINT_INTERVAL_OFFSET = 6;
  localparam byte unsigned ISOCHRONOUS_ENDPOINT_TYPE = 1;
  localparam byte unsigned BULK_ENDPOINT_TYPE = 2;
  byte unsigned discovered_payload[$];
  byte unsigned selected_configuration;

  // Scenario inputs. This sequence runs on the SVT sequencer, which has no
  // usb_env_cfg handle, so the parent scenario copies these from
  // usb_env_cfg before start. Link bring-up is bounded separately from each
  // individual control transfer.
  usb_endpoint_cfg control_endpoint;
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

  // USB 2.0 section 9.6.1: HS devices report USB 2.0, a 64-byte EP0,
  // and at least one configuration. Identity fields are not an oracle.
  function void check_device_descriptor(byte unsigned descriptor[$]);
    if (descriptor.size() != DEVICE_DESCRIPTOR_LENGTH) begin
      `uvm_fatal("USB_INIT_HOST", "Device descriptor must contain exactly 18 bytes")
    end
    if (descriptor[DESCRIPTOR_LENGTH_OFFSET] != DEVICE_DESCRIPTOR_LENGTH ||
        descriptor[DESCRIPTOR_TYPE_OFFSET] != DEVICE_DESCRIPTOR_TYPE ||
        descriptor[DEVICE_USB_VERSION_OFFSET] != 0 || descriptor[DEVICE_USB_VERSION_OFFSET + 1] != 2 ||
        descriptor[DEVICE_EP0_PACKET_SIZE_OFFSET] != 64 || descriptor[DEVICE_CONFIGURATION_COUNT_OFFSET] == 0) begin
      `uvm_fatal("USB_INIT_HOST", "Invalid USB 2.0 HS device descriptor or no advertised configurations")
    end
  endfunction

  // USB 2.0 section 9.6.3, Table 9-10. Validate the header independently
  // before trusting its transfer length or selecting its configuration value.
  function void check_configuration_header(byte unsigned descriptor[$]);
    if (descriptor.size() < CONFIGURATION_DESCRIPTOR_LENGTH) begin
      `uvm_fatal("USB_INIT_HOST", "Truncated configuration descriptor header")
    end
    if (descriptor[DESCRIPTOR_LENGTH_OFFSET] != CONFIGURATION_DESCRIPTOR_LENGTH ||
        descriptor[DESCRIPTOR_TYPE_OFFSET] != CONFIGURATION_DESCRIPTOR_TYPE ||
        (int'(descriptor[CONFIGURATION_TOTAL_LENGTH_OFFSET]) |
         (int'(descriptor[CONFIGURATION_TOTAL_LENGTH_OFFSET + 1]) << 8)) <
        CONFIGURATION_DESCRIPTOR_LENGTH + INTERFACE_DESCRIPTOR_LENGTH ||
        descriptor[CONFIGURATION_INTERFACE_COUNT_OFFSET] == 0 || descriptor[CONFIGURATION_VALUE_OFFSET] == 0 ||
        (descriptor[CONFIGURATION_ATTRIBUTES_OFFSET] & 8'h9f) != 8'h80 ||
        descriptor[CONFIGURATION_POWER_OFFSET] > 250) begin
      `uvm_fatal("USB_INIT_HOST", "Invalid configuration descriptor header")
    end
  endfunction

  // USB 2.0 sections 9.6.5/9.6.6: walk descriptor boundaries and validate
  // interface/endpoint counts, addresses, HS packet sizes, and intervals.
  // This scenario selects default alternate settings, not alternate interfaces.
  function void check_configuration_descriptor(byte unsigned descriptor[$]);
    int unsigned offset;
    int unsigned interface_count;
    int unsigned expected_endpoints;
    int unsigned observed_endpoints;
    bit interface_seen[byte unsigned];
    bit endpoint_seen[byte unsigned];

    check_configuration_header(descriptor);
    if (descriptor.size() != (int'(descriptor[CONFIGURATION_TOTAL_LENGTH_OFFSET]) |
                              (int'(descriptor[CONFIGURATION_TOTAL_LENGTH_OFFSET + 1]) << 8))) begin
      `uvm_fatal("USB_INIT_HOST", "Configuration tree length differs from wTotalLength")
    end
    offset = descriptor[DESCRIPTOR_LENGTH_OFFSET];
    interface_count = 0;
    expected_endpoints = 0;
    observed_endpoints = 0;
    while (offset < descriptor.size()) begin
      int unsigned descriptor_length;

      if (offset + 2 > descriptor.size()) begin
        `uvm_fatal("USB_INIT_HOST", "Truncated subordinate descriptor header")
      end
      descriptor_length = descriptor[offset + DESCRIPTOR_LENGTH_OFFSET];
      if (descriptor_length < 2 || offset + descriptor_length > descriptor.size()) begin
        `uvm_fatal("USB_INIT_HOST", "Invalid subordinate descriptor boundary")
      end
      case (descriptor[offset + DESCRIPTOR_TYPE_OFFSET])
        INTERFACE_DESCRIPTOR_TYPE: begin
          if (descriptor_length != INTERFACE_DESCRIPTOR_LENGTH || observed_endpoints != expected_endpoints) begin
            `uvm_fatal("USB_INIT_HOST", "Invalid interface length or preceding endpoint count")
          end
          if (descriptor[offset + INTERFACE_ALTERNATE_OFFSET] != 0 ||
              interface_seen.exists(descriptor[offset + INTERFACE_NUMBER_OFFSET]) ||
              descriptor[offset + INTERFACE_NUMBER_OFFSET] >= descriptor[CONFIGURATION_INTERFACE_COUNT_OFFSET]) begin
            `uvm_fatal("USB_INIT_HOST", "Expected unique, zero-based default interface settings")
          end
          interface_seen[descriptor[offset + INTERFACE_NUMBER_OFFSET]] = 1;
          interface_count++;
          expected_endpoints = descriptor[offset + INTERFACE_ENDPOINT_COUNT_OFFSET];
          observed_endpoints = 0;
        end
        ENDPOINT_DESCRIPTOR_TYPE: begin
          byte unsigned address;
          byte unsigned attributes;
          int unsigned packet_size;
          int unsigned additional_transactions;

          if (descriptor_length != ENDPOINT_DESCRIPTOR_LENGTH || interface_count == 0) begin
            `uvm_fatal("USB_INIT_HOST", "Invalid endpoint descriptor length or missing interface")
          end
          address = descriptor[offset + ENDPOINT_ADDRESS_OFFSET];
          attributes = descriptor[offset + ENDPOINT_ATTRIBUTES_OFFSET];
          packet_size = int'(descriptor[offset + ENDPOINT_PACKET_SIZE_OFFSET]) |
                        (int'(descriptor[offset + ENDPOINT_PACKET_SIZE_OFFSET + 1]) << 8);
          additional_transactions = (packet_size >> 11) & 3;
          if ((address & 8'h70) != 0 || (address & 8'h0f) == 0 || endpoint_seen.exists(address) ||
              (attributes & 8'hc0) != 0 || (attributes & 3) == 0 ||
              ((attributes & 3) != ISOCHRONOUS_ENDPOINT_TYPE && (attributes & 8'hfc) != 0) ||
              ((attributes & 3) == ISOCHRONOUS_ENDPOINT_TYPE && (attributes & 8'h30) == 8'h30) ||
              (packet_size & 16'he000) != 0 || additional_transactions == 3 ||
              (packet_size & 16'h07ff) == 0 || (packet_size & 16'h07ff) > 1024 ||
              ((attributes & 3) == BULK_ENDPOINT_TYPE && packet_size != 512) ||
              ((attributes & 3) != BULK_ENDPOINT_TYPE &&
               (descriptor[offset + ENDPOINT_INTERVAL_OFFSET] == 0 ||
                descriptor[offset + ENDPOINT_INTERVAL_OFFSET] > 16))) begin
            `uvm_fatal("USB_INIT_HOST", "Invalid HS endpoint address, attributes, packet size, or interval")
          end
          endpoint_seen[address] = 1;
          observed_endpoints++;
        end
        default: `uvm_fatal("USB_INIT_HOST", "Unexpected descriptor in the enumeration fixture")
      endcase
      offset += descriptor_length;
    end
    if (interface_count != descriptor[CONFIGURATION_INTERFACE_COUNT_OFFSET] ||
        observed_endpoints != expected_endpoints) begin
      `uvm_fatal("USB_INIT_HOST", "Configuration interface/endpoint counts do not match their descriptors")
    end
  endfunction

  // Derives the SVT success mask expected for the two zero-length host writes.
  // Other requests complete successfully with the default all-zero mask.
  function automatic bit [`SVT_USB_RESULTS_STATUS_SIZE - 1:0] derive_expected_results_status(svt_usb_types::setup_data_bmrequesttype_dir_enum expected_direction, svt_usb_types::setup_data_brequest_enum expected_request, bit [15:0] expected_length, byte unsigned expected_payload[$]);
    derive_expected_results_status = '0;
    if ((expected_direction === svt_usb_types::HOST_TO_DEVICE) &&
        ((expected_request === svt_usb_types::SET_ADDRESS) ||
         (expected_request === svt_usb_types::SET_CONFIGURATION) ||
         (expected_request === svt_usb_types::SET_FEATURE) ||
         (expected_request === svt_usb_types::CLEAR_FEATURE)) &&
        (expected_length === 16'd0) &&
        (expected_payload.size() === 0)) begin
      derive_expected_results_status[5] = 1'b1;
    end
  endfunction

  // Validates one ended-event object against immutable request intent.
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
    output string failure_reason
  );
    svt_usb_transfer transfer;
    bit [`SVT_USB_RESULTS_STATUS_SIZE - 1:0] expected_results_status;
    int observed_payload_count;
    string transfer_context;

    // Reject invalid event data before reading any transfer fields.
    if (!cast_completed_transfer(completed_object, transfer, failure_reason)) begin
      return 1'b0;
    end

    // Build one expected result and one observed-versus-expected diagnostic
    // snapshot that every subsequent rejection can reuse.
    observed_payload_count = (transfer.payload === null) ? -1 : transfer.payload.byte_count;
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
      expected_payload.size(),
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

    // Finally compare the complete data stage, including an explicit empty
    // payload object for requests whose expected payload length is zero.
    if (transfer.payload === null) begin
      failure_reason = {"payload handle is null; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload.byte_count !== expected_payload.size()) begin
      failure_reason = {"payload length does not match; ", transfer_context};
      return 1'b0;
    end
    foreach (expected_payload[byte_index]) begin
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
    byte unsigned expected_payload[$]
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
          failure_reason
        )) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("Step %0d %s completion rejected: %s", step_number, label, failure_reason))
    end
    validated_transfer_count++;
    `uvm_info("USB_INIT_HOST", $sformatf("Step %0d %s validated: payload_bytes=%0d validated_count=%0d", step_number, label, expected_payload.size(), validated_transfer_count), UVM_LOW)
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
    bit discover_descriptor = 1'b0
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
          setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
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
    // envelope below, then validate descriptor semantics in body().
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
      expected_payload = discovered_payload;
    end

    check_completed_transfer(
      step_number,
      label,
      completed_object,
      direction,
      svt_usb_types::STANDARD,
      svt_usb_types::BMREQ_DEVICE,
      request,
      value,
      index,
      length,
      device_address,
      expected_payload
    );
  endtask

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
    // Fixed framing-settling allowance before the first request, not a checked
    // readiness condition or a protocol minimum established by this sequence.
    #20us;

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
    check_device_descriptor(discovered_payload);
    descriptor_payload = discovered_payload;
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

    // Allow a fixed interval after SET_ADDRESS validation before
    // updating the host model for the new address; this delay does not poll
    // DUT address activation.
    #5us;
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

    // Prove descriptor stability at the assigned address, then discover and
    // validate the complete configuration before selecting it.
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
    check_configuration_header(configuration_header);
    configuration_length = int'(configuration_header[CONFIGURATION_TOTAL_LENGTH_OFFSET]) |
                           (int'(configuration_header[CONFIGURATION_TOTAL_LENGTH_OFFSET + 1]) << 8);
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
    check_configuration_descriptor(discovered_payload);
    foreach (configuration_header[byte_index]) begin
      if (configuration_header[byte_index] != discovered_payload[byte_index]) begin
        `uvm_fatal("USB_INIT_HOST", "Configuration header changed between discovery requests")
      end
    end
    selected_configuration = discovered_payload[CONFIGURATION_VALUE_OFFSET];
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

    // Preserve a fixed post-enumeration observation window; this sequence
    // adds no active checks during the delay. Then gate completion on all
    // expected validated transfers, rather than treating elapsed time as proof
    // of success.
    #50us;
    if (validated_transfer_count != ENUMERATION_REQUEST_COUNT) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("USB INIT validated %0d control transfers instead of %0d", validated_transfer_count, ENUMERATION_REQUEST_COUNT))
    end
    completed = 1'b1;
    `uvm_info("USB_INIT_HOST", $sformatf("USB INIT host enumeration complete: validated_count=%0d address=%0d configuration=%0d", validated_transfer_count, device_address, selected_configuration), UVM_LOW)
  endtask
endclass
