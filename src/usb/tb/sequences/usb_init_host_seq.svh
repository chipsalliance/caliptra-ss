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
// SOF generation is running, the sequence performs these seven EP0 requests:
//
//   1. GET_DESCRIPTOR at the default address 0.
//   2. GET_STATUS at address 0.
//   3. SET_ADDRESS to assign address 1.
//   4. GET_DESCRIPTOR again at the assigned address 1.
//   5. GET_CONFIGURATION and confirm the device is unconfigured (value 0).
//   6. SET_CONFIGURATION to select configuration 1.
//   7. GET_CONFIGURATION and confirm configuration 1 is active.
//
// Every request must finish on the bus before its bounded timeout. Completion
// is accepted only when the SVT result, EP0 SETUP fields, device address, and
// returned payload all match the request intent. Run this sequence on the SVT
// host agent's virtual sequencer; usb_init_seq supplies the concurrent DUT-side
// EP0 service needed to answer these requests.
class usb_init_host_seq extends uvm_sequence;
  `uvm_object_utils(usb_init_host_seq)
  `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

  // Bound link bring-up separately from each individual control transfer.
  localparam time USB_LINK_TIMEOUT = 750us;
  localparam time USB_CONTROL_TRANSFER_TIMEOUT = 100us;

  // usb_init_seq consumes completed; the count guards against partial flows.
  bit completed;
  int unsigned validated_transfer_count;

  // Constructs the host sequence; body() performs the enumeration.
  function new(string name = "usb_init_host_seq");
    super.new(name);
  endfunction

  // Derives the SVT success mask expected for the two zero-length host writes.
  // Other requests complete successfully with the default all-zero mask.
  function automatic bit [`SVT_USB_RESULTS_STATUS_SIZE - 1:0] derive_expected_results_status(svt_usb_types::setup_data_bmrequesttype_dir_enum expected_direction, svt_usb_types::setup_data_brequest_enum expected_request, bit [15:0] expected_length, byte unsigned expected_payload[$]);
    derive_expected_results_status = '0;
    if ((expected_direction === svt_usb_types::HOST_TO_DEVICE) &&
        ((expected_request === svt_usb_types::SET_ADDRESS) ||
         (expected_request === svt_usb_types::SET_CONFIGURATION)) &&
        (expected_length === 16'd0) &&
        (expected_payload.size() === 0)) begin
      derive_expected_results_status[5] = 1'b1;
    end
  endfunction

  // Waits for USB 2.0 link enablement before SOF or EP0 traffic can begin.
  task wait_for_link_enabled(svt_usb_status shared_status);
    bit link_enabled;

    link_enabled = 1'b0;
    `uvm_info("USB_INIT_HOST", "Waiting for the SVT USB 2.0 host link to reach ENABLED", UVM_LOW)
    fork
      begin
        wait (shared_status.link_usb_20_state === svt_usb_types::ENABLED);
        link_enabled = 1'b1;
      end
      begin
        #(USB_LINK_TIMEOUT);
      end
    join_any
    disable fork;

    if (!link_enabled) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("USB link did not reach ENABLED within %0t; state=%p", USB_LINK_TIMEOUT, shared_status.link_usb_20_state))
    end
    `uvm_info("USB_INIT_HOST", "SVT USB host link is ENABLED", UVM_LOW)
  endtask

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

    failure_reason = "";
    // Reject invalid event data before reading any transfer fields.
    if (completed_object === null) begin
      failure_reason = "completion object is null";
      return 1'b0;
    end
    if (!$cast(transfer, completed_object)) begin
      failure_reason = $sformatf("completion object type %s is not svt_usb_transfer", completed_object.get_type_name());
      return 1'b0;
    end
    if (transfer === null) begin
      failure_reason = "checked completion cast returned a null transfer";
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

  // Applies the production validator and counts only fully accepted completions.
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
      `uvm_fatal("USB_INIT_HOST", $sformatf("Step %0d/7 %s completion rejected: %s", step_number, label, failure_reason))
    end
    validated_transfer_count++;
    `uvm_info("USB_INIT_HOST", $sformatf("Step %0d/7 %s validated: payload_bytes=%0d validated_count=%0d/7", step_number, label, expected_payload.size(), validated_transfer_count), UVM_LOW)
  endtask

  // Submits one control request and validates the first ended event against
  // its intent. The event wait runs concurrently with request submission so
  // both a fast completion and a bounded timeout are handled.
  task run_control_transfer(
    svt_usb_agent host_agent,
    svt_usb_configuration usb_cfg,
    svt_usb_types::setup_data_bmrequesttype_dir_enum direction,
    svt_usb_types::setup_data_brequest_enum request,
    bit [15:0] value,
    bit [15:0] index,
    bit [15:0] length,
    bit [6:0] device_address,
    int unsigned step_number,
    string label,
    byte unsigned expected_payload[$]
  );
    svt_usb_transfer request_transfer;
    uvm_object completed_object;
    bit transfer_ended;

    transfer_ended = 1'b0;
    request_transfer = svt_usb_transfer::type_id::create({label, "_request"});
    `uvm_info(
      "USB_INIT_HOST",
      $sformatf(
        "Submitting step %0d/7 %s: addr=%0d request=0x%02h value=0x%04h length=%0d",
        step_number,
        label,
        device_address,
        request,
        value,
        length
      ),
      UVM_LOW
    )

    // One branch captures the first ended event or times out while the other
    // drives the request through the transfer sequencer.
    fork
      begin
        fork
          begin
            host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger_data(completed_object);
            transfer_ended = 1'b1;
          end
          begin
            #(USB_CONTROL_TRANSFER_TIMEOUT);
          end
        join_any
        disable fork;
      end
      begin
        start_item(request_transfer, -1, p_sequencer.xfer_sequencer);
        request_transfer.cfg = usb_cfg;
        // Pin the device, endpoint, and ustream configuration indices to zero.
        // SVT disables their randomization so the request keeps these selections.
        request_transfer.fix_anchors(0, 0, 0);
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
          `uvm_fatal("USB_INIT_HOST", $sformatf("Unable to randomize step %0d/7 %s", step_number, label))
        end
        finish_item(request_transfer);
      end
    join

    if (!transfer_ended) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("Step %0d/7 %s did not complete within %0t", step_number, label, USB_CONTROL_TRANSFER_TIMEOUT))
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

  // Runs the fixed seven-request USB INIT flow and gates completion on all
  // seven transfer validations.
  virtual task body();
    svt_usb_agent host_agent;
    svt_usb_status shared_status;
    svt_configuration base_cfg;
    svt_usb_configuration usb_cfg;
    byte unsigned no_payload[$];
    byte unsigned descriptor_payload[$];
    byte unsigned status_payload[$];
    byte unsigned unconfigured_payload[$];
    byte unsigned configured_payload[$];

    completed = 1'b0;
    validated_transfer_count = 0;

    // These are the exact data-stage bytes expected from the DUT-side EP0
    // service for discovery, status, and configuration-state requests.
    descriptor_payload = '{
      8'h12, 8'h01, 8'h02, 8'h00, 8'h00, 8'h00, 8'h00, 8'h40,
      8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h01, 8'h00, 8'h00,
      8'h00, 8'h00
    };
    status_payload = '{8'h00, 8'h00};
    unconfigured_payload = '{8'h00};
    configured_payload = '{8'h01};

    // Resolve the host agent and shared VIP objects supplied by usb_env.
    if (p_sequencer === null || !$cast(host_agent, p_sequencer.get_parent())) begin
      `uvm_fatal("USB_INIT_HOST", "Sequence must run on the SVT host_agent virtual sequencer")
    end
    shared_status = p_sequencer.get_shared_status(this);
    if (shared_status === null) begin
      `uvm_fatal("USB_INIT_HOST", "SVT shared status is unavailable")
    end
    p_sequencer.get_cfg(base_cfg);
    if (!$cast(usb_cfg, base_cfg)) begin
      `uvm_fatal("USB_INIT_HOST", "SVT USB configuration is unavailable")
    end

    `uvm_info("USB_INIT_HOST", "Starting seven-step USB INIT host enumeration from address 0 to configuration 1", UVM_LOW)

    // Bring up periodic USB framing before issuing the first EP0 request.
    wait_for_link_enabled(shared_status);
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
    // request the transition from address 0 to address 1.
    run_control_transfer(
      host_agent,
      usb_cfg,
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      16'h0100,
      16'h0000,
      16'h0012,
      0,
      1,
      "GET_DESCRIPTOR_address_0",
      descriptor_payload
    );
    run_control_transfer(
      host_agent,
      usb_cfg,
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
      host_agent,
      usb_cfg,
      svt_usb_types::HOST_TO_DEVICE,
      svt_usb_types::SET_ADDRESS,
      16'h0001,
      16'h0000,
      16'h0000,
      0,
      3,
      "SET_ADDRESS_1",
      no_payload
    );

    // Allow a fixed interval after SET_ADDRESS validation before updating the
    // host model for address 1; this delay does not poll DUT address activation.
    #5us;
    usb_cfg.remote_device_cfg[0].device_address = 7'd1;
    host_agent.reconfigure(usb_cfg);
    `uvm_info("USB_INIT_HOST", "Reconfigured the SVT host for device address 1", UVM_LOW)

    // Steps 4-7 prove communication at the assigned address, observe the
    // initial configuration value, select configuration 1, and read it back.
    run_control_transfer(
      host_agent,
      usb_cfg,
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_DESCRIPTOR,
      16'h0100,
      16'h0000,
      16'h0012,
      1,
      4,
      "GET_DESCRIPTOR_address_1",
      descriptor_payload
    );
    run_control_transfer(
      host_agent,
      usb_cfg,
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_CONFIGURATION,
      16'h0000,
      16'h0000,
      16'h0001,
      1,
      5,
      "GET_CONFIGURATION_before_set",
      unconfigured_payload
    );
    run_control_transfer(
      host_agent,
      usb_cfg,
      svt_usb_types::HOST_TO_DEVICE,
      svt_usb_types::SET_CONFIGURATION,
      16'h0001,
      16'h0000,
      16'h0000,
      1,
      6,
      "SET_CONFIGURATION_1",
      no_payload
    );
    run_control_transfer(
      host_agent,
      usb_cfg,
      svt_usb_types::DEVICE_TO_HOST,
      svt_usb_types::GET_CONFIGURATION,
      16'h0000,
      16'h0000,
      16'h0001,
      1,
      7,
      "GET_CONFIGURATION_after_set",
      configured_payload
    );

    // Preserve a fixed post-enumeration observation window; this sequence adds
    // no active checks during the delay. Then gate completion on exactly seven
    // validated transfers, rather than treating elapsed time as proof of success.
    #50us;
    if (validated_transfer_count !== 7) begin
      `uvm_fatal("USB_INIT_HOST", $sformatf("USB INIT validated %0d control transfers instead of exactly 7", validated_transfer_count))
    end
    completed = 1'b1;
    `uvm_info("USB_INIT_HOST", $sformatf("USB INIT host enumeration complete: validated_count=%0d/7 address=1 configuration=1", validated_transfer_count), UVM_LOW)
  endtask
endclass
