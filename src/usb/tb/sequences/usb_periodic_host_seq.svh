//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************

// Shared interrupt/ISO submission and payload checking. The VIP owns periodic
// scheduling, SOFs, PID/CRC/handshake checks and coverage.
class usb_periodic_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_periodic_host_seq)

  usb_endpoint_cfg target_endpoint;
  usb_speed_e speed = USB_SPEED_HIGH;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  int unsigned payload_byte_count;
  logic [7:0] payload_base;
  time transfer_timeout = 3ms;
  string transfer_label = "Periodic transfer";

  // Construct a single shared helper for both transfer types and directions.
  function new(string name = "usb_periodic_host_seq");
    super.new(name);
  endfunction

  // Keep the native completion/watch diagnostics component-specific.
  virtual function string report_id();
    return "USB_PERIODIC_HOST";
  endfunction

  // Queue one prepared packet using the native earliest-service constraints.
  virtual task body();
    svt_usb_transfer transfer;
    svt_usb_transfer observed;
    uvm_object completion;
    svt_usb_transfer::transfer_type_enum expected_type;
    bit [3:0] ep_number;
    string reason;
    bit is_iso;
    bit aligned_payload;

    completed = 1'b0;
    if (target_endpoint == null || !target_endpoint.anchor_index_valid ||
        !(target_endpoint.transfer_type inside {USB_TRANSFER_TYPE_INTERRUPT, USB_TRANSFER_TYPE_ISOCHRONOUS}) ||
        payload_byte_count == 0 || payload_byte_count > target_endpoint.max_packet_size || $isunknown(payload_base)) begin
      `uvm_fatal(report_id(), "An anchored periodic endpoint and one known packet-sized payload are required")
    end
    resolve_host_context();
    if ((speed == USB_SPEED_FULL) != (usb_cfg.speed == svt_usb_types::FS)) begin
      `uvm_fatal(report_id(), "Periodic transfer speed disagrees with the centrally configured host bus")
    end
    is_iso = target_endpoint.transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS;
    aligned_payload = (payload_byte_count % target_endpoint.max_packet_size) == 0;
    if (is_iso) begin
      expected_type = target_endpoint.direction == USB_DIRECTION_IN ?
                      svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER : svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;
    end else begin
      expected_type = target_endpoint.direction == USB_DIRECTION_IN ?
                      svt_usb_transfer::INTERRUPT_IN_TRANSFER : svt_usb_transfer::INTERRUPT_OUT_TRANSFER;
    end
    ep_number = 4'(target_endpoint.ep_number);
    transfer = svt_usb_transfer::type_id::create("periodic_transfer");
    `uvm_info(report_id(), $sformatf("%s queueing %s bytes=%0d address=%0d speed=%s with native earliest-service scheduling",
      transfer_label, target_endpoint.short_name(), payload_byte_count, device_address, speed.name()), UVM_LOW)
    begin_transfer_watch(transfer_label, transfer_timeout);
    start_item(transfer, -1, p_sequencer.xfer_sequencer);
    transfer.cfg = usb_cfg;
    transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
    if (target_endpoint.direction == USB_DIRECTION_OUT) begin
      transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
      transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
    end
    // USB2 DATA0 is the public {first,last}={0,1} mapping, not {1,1}.
    if (!transfer.randomize() with {
          xfer_type == local::expected_type;
          device_address == local::device_address;
          endpoint_number == local::ep_number;
          payload_intended_byte_count == local::payload_byte_count;
          local::aligned_payload -> aligned_transfer_ends_with_zero_length == 0;
          inter_transfer_delay_longint == 0;
          local::is_iso -> first_isoc_transaction == 0;
          local::is_iso -> last_isoc_transaction == 1;
          force_extra_isoc == 0;
        }) begin
      `uvm_fatal(report_id(), $sformatf("Unable to randomize %s", transfer_label))
    end
    if (target_endpoint.direction == USB_DIRECTION_OUT) begin
      for (int unsigned index = 0; index < payload_byte_count; index++) transfer.payload.data[index] = payload_base + index;
    end
    finish_item(transfer);
    drain_transfer_response(transfer);
    end_transfer_watch(completion);
    check_transfer_correlation(transfer_label, transfer, completion);
    if (!cast_completed_transfer(completion, observed, reason)) begin
      `uvm_fatal(report_id(), $sformatf("%s completion rejected: %s", transfer_label, reason))
    end
    if (!(observed.status === svt_sequence_item::ACCEPT) || !(observed.results_status === '0) ||
        !(observed.xfer_type === expected_type) || !(observed.device_address === device_address) ||
        !(observed.endpoint_number === ep_number) || observed.payload == null) begin
      `uvm_fatal(report_id(), $sformatf("%s completion mismatch: status=%s results=%h type=%s address=%0d endpoint=%0d",
        transfer_label, observed.status.name(), observed.results_status, observed.xfer_type.name(), observed.device_address, observed.endpoint_number))
    end
    if (!(observed.payload.byte_count === payload_byte_count)) `uvm_fatal(report_id(), "Periodic completion byte count mismatch")
    if (target_endpoint.direction == USB_DIRECTION_IN) begin
      for (int unsigned index = 0; index < payload_byte_count; index++) begin
        logic [7:0] expected;
        expected = payload_base + index;
        if (!(observed.payload.get_byte_val(index) === expected)) begin
          `uvm_fatal(report_id(), $sformatf("%s IN byte %0d mismatch", transfer_label, index))
        end
      end
    end
    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("%s accepted with all %0d bytes checked under native periodic scheduling",
      transfer_label, payload_byte_count), UVM_LOW)
  endtask
endclass
