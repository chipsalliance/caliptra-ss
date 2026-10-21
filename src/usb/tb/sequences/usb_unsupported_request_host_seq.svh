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

// Sends one unsupported control OUT request and requires non-success.
class usb_unsupported_request_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_unsupported_request_host_seq)

  usb_endpoint_cfg control_endpoint;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  time control_transfer_timeout = USB_DEFAULT_CONTROL_TRANSFER_TIMEOUT;
  byte unsigned unsupported_request = 8'h7f;
  int unsigned payload_byte_count = 4;

  function new(string name = "usb_unsupported_request_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_UNSUPPORTED_HOST";
  endfunction

  // Drive the unsupported SETUP and payload, then reject a successful result.
  virtual task body();
    svt_usb_transfer request_transfer;
    svt_usb_transfer completed_transfer;
    uvm_object completed_object;
    string failure_reason;

    completed = 1'b0;
    if (control_endpoint == null || !control_endpoint.anchor_index_valid) begin
      `uvm_fatal(report_id(), "An applied EP0 endpoint configuration is required")
    end
    resolve_host_context();
    request_transfer = svt_usb_transfer::type_id::create("unsupported_request");
    `uvm_info(
      report_id(),
      $sformatf("Submitting unsupported control OUT request 0x%02h with %0d data bytes", unsupported_request, payload_byte_count),
      UVM_LOW
    )

    begin_transfer_watch("Unsupported control OUT", control_transfer_timeout);
    start_item(request_transfer, -1, p_sequencer.xfer_sequencer);
    request_transfer.cfg = usb_cfg;
    request_transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
    request_transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
    request_transfer.fix_anchors(0, control_endpoint.anchor_index, 0);
    if (!request_transfer.randomize() with {
          xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
          device_address == local::device_address;
          setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE;
          setup_data_bmrequesttype_type == svt_usb_types::STANDARD;
          setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
          setup_data_brequest == local::unsupported_request;
          setup_data_w_value == 16'h0000;
          setup_data_w_index == 16'h0000;
          setup_data_w_length == local::payload_byte_count;
          payload_intended_byte_count == local::payload_byte_count;
        }) begin
      `uvm_fatal(report_id(), "Unable to randomize unsupported control request")
    end
    for (int unsigned byte_index = 0; byte_index < payload_byte_count; byte_index++) begin
      request_transfer.payload.data[byte_index] = 8'ha0 + byte_index;
    end
    finish_item(request_transfer);

    end_transfer_watch(completed_object);
    check_transfer_correlation("Unsupported control OUT", request_transfer, completed_object);
    if (!cast_completed_transfer(completed_object, completed_transfer, failure_reason)) begin
      `uvm_fatal(report_id(), $sformatf("Unsupported request completion rejected: %s", failure_reason))
    end
    if (completed_transfer.status === svt_sequence_item::ACCEPT &&
        completed_transfer.results_status === '0) begin
      `uvm_fatal(report_id(), "Unsupported control request completed successfully instead of terminating with STALL")
    end

    completed = 1'b1;
    `uvm_info(
      report_id(),
      $sformatf(
        "Unsupported request completed non-successfully: status=%s results=0x%0h",
        completed_transfer.status.name(),
        completed_transfer.results_status
      ),
      UVM_LOW
    )
  endtask
endclass
