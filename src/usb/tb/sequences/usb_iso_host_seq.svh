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

// Drives one checked high-speed isochronous transfer in either direction.
class usb_iso_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_iso_host_seq)

  usb_endpoint_cfg target_endpoint;
  int unsigned payload_byte_count;
  logic [7:0] payload_base;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  time transfer_timeout = 500us;
  string transfer_label = "Isochronous transfer";
  bit first_isoc_transaction = 1'b1;
  bit last_isoc_transaction = 1'b1;

  function new(string name = "usb_iso_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_ISO_HOST";
  endfunction

  // Submit one complete isochronous service interval and check completion.
  virtual task body();
    svt_usb_transfer transfer;
    svt_usb_transfer completed_transfer;
    uvm_object completed_object;
    string failure_reason;
    bit [3:0] target_ep_number;

    completed = 1'b0;
    if (target_endpoint == null ||
        target_endpoint.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS ||
        !target_endpoint.anchor_index_valid ||
        payload_byte_count == 0) begin
      `uvm_fatal(report_id(), "A valid isochronous endpoint and nonzero payload size are required")
    end

    resolve_host_context();
    target_ep_number = 4'(target_endpoint.ep_number);
    transfer = svt_usb_transfer::type_id::create("iso_transfer");
    `uvm_info(
      report_id(),
      $sformatf("%s starting on %s: address=%0d bytes=%0d", transfer_label, target_endpoint.convert2string(), device_address, payload_byte_count),
      UVM_LOW
    )

    begin_transfer_watch(transfer_label, transfer_timeout);
    start_item(transfer, -1, p_sequencer.xfer_sequencer);
    transfer.cfg = usb_cfg;
    transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
    if (target_endpoint.direction == USB_DIRECTION_OUT) begin
      transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
      transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
      if (!transfer.randomize() with {
            xfer_type == svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;
            device_address == local::device_address;
            endpoint_number == target_ep_number;
            payload_intended_byte_count == local::payload_byte_count;
            first_isoc_transaction == local::first_isoc_transaction;
            last_isoc_transaction == local::last_isoc_transaction;
          }) begin
        `uvm_fatal(report_id(), $sformatf("Unable to randomize %s", transfer_label))
      end
      for (int unsigned byte_index = 0; byte_index < payload_byte_count; byte_index++) begin
        transfer.payload.data[byte_index] = payload_base + byte_index;
      end
    end else begin
      transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
      transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
      if (!transfer.randomize() with {
            xfer_type == svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER;
            device_address == local::device_address;
            endpoint_number == target_ep_number;
            payload_intended_byte_count == local::payload_byte_count;
            first_isoc_transaction == local::first_isoc_transaction;
            last_isoc_transaction == local::last_isoc_transaction;
          }) begin
        `uvm_fatal(report_id(), $sformatf("Unable to randomize %s", transfer_label))
      end
      // The host receives and appends one packet per high-bandwidth
      // transaction. Start with an empty user-defined payload.
      transfer.payload.data.delete();
      transfer.payload.byte_count = 0;
    end
    finish_item(transfer);

    end_transfer_watch(completed_object);
    check_transfer_correlation(transfer_label, transfer, completed_object);
    if (!cast_completed_transfer(completed_object, completed_transfer, failure_reason)) begin
      `uvm_fatal(report_id(), $sformatf("%s completion rejected: %s", transfer_label, failure_reason))
    end
    if (completed_transfer.status !== svt_sequence_item::ACCEPT ||
        completed_transfer.results_status !== '0 ||
        completed_transfer.device_address !== device_address ||
        completed_transfer.endpoint_number !== target_ep_number ||
        completed_transfer.payload == null ||
        completed_transfer.payload.byte_count !== payload_byte_count) begin
      `uvm_fatal(
        report_id(),
        $sformatf(
          "%s completion mismatch: status=%s results=0x%0h addr=%0d ep=%0d bytes=%0d",
          transfer_label,
          completed_transfer.status.name(),
          completed_transfer.results_status,
          completed_transfer.device_address,
          completed_transfer.endpoint_number,
          (completed_transfer.payload == null) ? -1 : completed_transfer.payload.byte_count
        )
      )
    end
    if (target_endpoint.direction == USB_DIRECTION_IN) begin
      for (int unsigned byte_index = 0; byte_index < payload_byte_count; byte_index++) begin
        logic [7:0] observed_byte;
        logic [7:0] expected_byte;

        observed_byte = completed_transfer.payload.get_byte_val(byte_index);
        expected_byte = payload_base + byte_index;
        if (observed_byte !== expected_byte) begin
          `uvm_fatal(
            report_id(),
            $sformatf("%s byte %0d is 0x%02h instead of 0x%02h", transfer_label, byte_index, observed_byte, expected_byte)
          )
        end
      end
    end

    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("%s accepted with %0d bytes", transfer_label, payload_byte_count), UVM_LOW)
  endtask
endclass
