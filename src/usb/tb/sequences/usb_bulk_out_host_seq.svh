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

// Drives one checked bulk OUT transfer on a configured endpoint.
class usb_bulk_out_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_bulk_out_host_seq)

  usb_endpoint_cfg target_endpoint;
  int unsigned payload_byte_count;
  logic [7:0] payload_base;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  time bulk_transfer_timeout = 200us;
  string transfer_label = "Bulk OUT";

  function new(string name = "usb_bulk_out_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_BULK_OUT_HOST";
  endfunction

  // Accept only the requested successful bulk OUT completion.
  function automatic bit validate_completed_transfer(uvm_object completed_object, output string failure_reason);
    svt_usb_transfer transfer;
    int observed_payload_count;
    string transfer_context;

    if (!cast_completed_transfer(completed_object, transfer, failure_reason)) begin
      return 1'b0;
    end

    observed_payload_count = (transfer.payload === null) ? -1 : transfer.payload.byte_count;
    transfer_context = $sformatf(
      {"expected status=ACCEPT results=0x0 type=BULK_OUT_TRANSFER addr=%0d ep=%0d payload_len=%0d; ",
       "observed status=%s results=0x%0h type=%s addr=%0d ep=%0d payload_len=%0d"},
      device_address,
      target_endpoint.ep_number,
      payload_byte_count,
      transfer.status.name(),
      transfer.results_status,
      transfer.xfer_type.name(),
      transfer.device_address,
      transfer.endpoint_number,
      observed_payload_count
    );

    if (transfer.status !== svt_sequence_item::ACCEPT) begin
      failure_reason = {"terminal status is not ACCEPT; ", transfer_context};
      return 1'b0;
    end
    if (transfer.results_status !== '0) begin
      failure_reason = {"results_status does not match the expected success mask; ", transfer_context};
      return 1'b0;
    end
    if (transfer.xfer_type !== svt_usb_transfer::BULK_OUT_TRANSFER) begin
      failure_reason = {"transfer kind is not BULK_OUT_TRANSFER; ", transfer_context};
      return 1'b0;
    end
    if (transfer.device_address !== device_address) begin
      failure_reason = {"device address does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.endpoint_number !== 4'(target_endpoint.ep_number)) begin
      failure_reason = {"endpoint number does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload === null) begin
      failure_reason = {"payload handle is null; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload.byte_count !== payload_byte_count) begin
      failure_reason = {"payload length does not match; ", transfer_context};
      return 1'b0;
    end
    return 1'b1;
  endfunction

  // Submit the transfer and validate its terminal event.
  virtual task body();
    svt_usb_transfer bulk_transfer;
    uvm_object completed_object;
    string failure_reason;
    bit aligned_payload;
    bit [3:0] target_ep_number;

    completed = 1'b0;
    if (target_endpoint == null) begin
      `uvm_fatal(report_id(), "No target endpoint configuration was supplied")
    end
    if (target_endpoint.direction != USB_DIRECTION_OUT ||
        target_endpoint.transfer_type != USB_TRANSFER_TYPE_BULK) begin
      `uvm_fatal(report_id(), $sformatf("Target is not a bulk OUT endpoint: %s", target_endpoint.convert2string()))
    end
    if (payload_byte_count == 0) begin
      `uvm_fatal(report_id(), "payload_byte_count must be nonzero")
    end
    if (!target_endpoint.anchor_index_valid) begin
      `uvm_fatal(report_id(), $sformatf("%s has no VIP anchor index", target_endpoint.convert2string()))
    end

    resolve_host_context();
    target_ep_number = 4'(target_endpoint.ep_number);
    `uvm_info(
      report_id(),
      $sformatf(
        "Submitting %s on %s: addr=%0d bytes=%0d payload=0x%02h..0x%02h",
        transfer_label,
        target_endpoint.convert2string(),
        device_address,
        payload_byte_count,
        payload_base,
        payload_base + payload_byte_count - 1
      ),
      UVM_LOW
    )

    aligned_payload = (payload_byte_count % target_endpoint.max_packet_size) == 0;
    bulk_transfer = svt_usb_transfer::type_id::create("bulk_out_transfer");

    begin_transfer_watch(transfer_label, bulk_transfer_timeout);
    start_item(bulk_transfer, -1, p_sequencer.xfer_sequencer);
    bulk_transfer.cfg = usb_cfg;
    bulk_transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
    bulk_transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
    bulk_transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
    if (!bulk_transfer.randomize() with {
          xfer_type == svt_usb_transfer::BULK_OUT_TRANSFER;
          device_address == local::device_address;
          endpoint_number == target_ep_number;
          payload_intended_byte_count == local::payload_byte_count;
          local::aligned_payload -> aligned_transfer_ends_with_zero_length == 0;
        }) begin
      `uvm_fatal(report_id(), $sformatf("Unable to randomize %s", transfer_label))
    end
    for (int unsigned byte_index = 0; byte_index < payload_byte_count; byte_index++) begin
      bulk_transfer.payload.data[byte_index] = payload_base + byte_index;
    end
    finish_item(bulk_transfer);

    end_transfer_watch(completed_object);
    check_transfer_correlation(transfer_label, bulk_transfer, completed_object);
    if (!validate_completed_transfer(completed_object, failure_reason)) begin
      `uvm_fatal(report_id(), $sformatf("%s completion rejected: %s", transfer_label, failure_reason))
    end

    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("%s accepted on the bus: bytes=%0d", transfer_label, payload_byte_count), UVM_LOW)
  endtask
endclass
