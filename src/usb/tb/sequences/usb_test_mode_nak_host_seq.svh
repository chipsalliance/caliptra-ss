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

// Issues a single bulk IN probe during TEST_SE0_NAK mode, verifies the native
// NAK handshake via host_agent.prot.NOTIFY_20_HOST_RX_PACKET
// (others/class_svt_usb_protocol.html), and retires the transfer cleanly via
// svt_usb_protocol_service_abort_current_transfer_sequence
// (sequences/class_svt_usb_protocol_service_abort_current_transfer_sequence.html)
// with svt_usb_transfer::results_status[1] == 1'b1 while relying on the SVT
// VIP's built-in protocol/physical checks (svt_usb_protocol_ep_sc and
// svt_usb_physical_20_sc).
class usb_test_mode_nak_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_test_mode_nak_host_seq)

  usb_endpoint_cfg target_endpoint;
  bit [6:0] device_address;
  int unsigned payload_byte_count;
  time transfer_timeout = 100us;

  function new(string name = "usb_test_mode_nak_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_TEST_MODE_NAK_HOST";
  endfunction

  virtual task body();
    svt_usb_transfer request_transfer;
    svt_usb_transfer completed_transfer;
    svt_usb_protocol_service_abort_current_transfer_sequence abort_sequence;
    uvm_sequence_item response;
    uvm_object completed_object;
    process nak_observer;
    bit nak_observed;
    bit [3:0] endpoint_number;
    bit [`SVT_USB_RESULTS_STATUS_SIZE-1:0] expected_results;
    string failure_reason;

    completed = 1'b0;
    if (target_endpoint == null || !target_endpoint.anchor_index_valid ||
        target_endpoint.direction != USB_DIRECTION_IN ||
        target_endpoint.transfer_type != USB_TRANSFER_TYPE_BULK || payload_byte_count == 0) begin
      `uvm_fatal(report_id(), "A valid bulk IN endpoint and nonzero payload size are required")
    end
    resolve_host_context();
    endpoint_number = 4'(target_endpoint.ep_number);
    request_transfer = svt_usb_transfer::type_id::create("test_mode_in");
    begin_transfer_watch("TEST_SE0_NAK IN probe", transfer_timeout);
    // A protocol transfer supplies the routing context needed to accept NAK.
    // After NAK, the native abort service ends the probe without requiring DATA.
    fork
      begin
        uvm_object rx_object;
        svt_usb_packet rx_packet;

        nak_observer = process::self();
        host_agent.prot.NOTIFY_20_HOST_RX_PACKET.wait_trigger_data(rx_object);
        if (!$cast(rx_packet, rx_object) || rx_packet.get_pid_name_val() !== svt_usb_packet::NAK) begin
          `uvm_fatal(report_id(), "TEST_SE0_NAK did not return an accepted native NAK to IN")
        end
        nak_observed = 1'b1;
        abort_sequence = svt_usb_protocol_service_abort_current_transfer_sequence::type_id::create("abort_sequence");
        abort_sequence.dev_add = device_address;
        abort_sequence.ep_number = endpoint_number;
        abort_sequence.dir_seq = svt_usb_types::IN;
        abort_sequence.force_immd_abrt = 1'b0;
        abort_sequence.start(p_sequencer.prot_service_sequencer);
      end
    join_none
    #0;
    start_item(request_transfer, -1, p_sequencer.xfer_sequencer);
    request_transfer.cfg = usb_cfg;
    request_transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
    if (!request_transfer.randomize() with {
          xfer_type == svt_usb_transfer::BULK_IN_TRANSFER;
          device_address == local::device_address;
          endpoint_number == local::endpoint_number;
          payload_intended_byte_count == local::payload_byte_count;
        }) begin
      `uvm_fatal(report_id(), "Unable to randomize the native test-mode IN transfer")
    end
    finish_item(request_transfer);
    get_response(response, request_transfer.get_transaction_id());
    if (response == null || response.get_sequence_id() != request_transfer.get_sequence_id()) begin
      `uvm_fatal(report_id(), "TEST_SE0_NAK IN probe received an invalid routed response")
    end
    end_transfer_watch(completed_object);
    nak_observer.await();
    check_transfer_correlation("TEST_SE0_NAK IN probe", request_transfer, completed_object);
    if (!cast_completed_transfer(completed_object, completed_transfer, failure_reason)) begin
      `uvm_fatal(report_id(), $sformatf("IN probe completion rejected: %s", failure_reason))
    end
    expected_results = '0;
    // svt_usb_transfer::results_status[1]: explicit testbench-command abort.
    expected_results[1] = 1'b1;
    if (!nak_observed || completed_transfer.status !== svt_sequence_item::ABORTED ||
        completed_transfer.results_status !== expected_results ||
        completed_transfer.xfer_type !== svt_usb_transfer::BULK_IN_TRANSFER ||
        completed_transfer.device_address !== device_address ||
        completed_transfer.endpoint_number !== endpoint_number) begin
      `uvm_fatal(report_id(), $sformatf("IN probe failed: NAK=%0b status=%s results=0x%0h",
        nak_observed, completed_transfer.status.name(), completed_transfer.results_status))
    end
    completed = 1'b1;
    `uvm_info(report_id(), "Native IN probe received NAK and was explicitly retired without DATA", UVM_LOW)
  endtask
endclass
