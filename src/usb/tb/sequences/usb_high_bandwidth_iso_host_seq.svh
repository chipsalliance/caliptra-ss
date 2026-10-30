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

// Drives up to three 1024-byte high-bandwidth isochronous transactions in one
// microframe using Synopsys SVT USB VIP transfers (ISOCHRONOUS_OUT_TRANSFER /
// ISOCHRONOUS_IN_TRANSFER in transaction/class_svt_usb_transfer.html) and
// resets the host endpoint's per-interval PID state via
// svt_usb_endpoint_status::set_isoc_toggle_state(ISOC_TOGGLE_RESET)
// (status/class_svt_usb_endpoint_status.html) after an intentionally
// incomplete microframe.
class usb_high_bandwidth_iso_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_high_bandwidth_iso_host_seq)

  localparam int unsigned PACKET_BYTES = 1024;
  localparam int unsigned PACKETS_PER_INTERVAL = 3;

  usb_endpoint_cfg target_endpoint;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  int unsigned packet_count = PACKETS_PER_INTERVAL;
  logic [7:0] interval_base = 8'h10;
  logic [7:0] packet_stride = 8'h40;
  time transfer_timeout = 750us;
  string transfer_label = "High-bandwidth ISO";

  function new(string name = "usb_high_bandwidth_iso_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_HB_ISO_HOST";
  endfunction

  // Generate packet- and interval-distinct byte patterns.
  function logic [7:0] expected_byte(int unsigned byte_index);
    int unsigned packet_index;

    packet_index = byte_index / PACKET_BYTES;
    return interval_base + 8'(byte_index) + packet_stride * packet_index;
  endfunction

  // Wait for automatic host SOF generation to advance past target_microframe.
  task wait_for_microframe_end(int unsigned target_microframe);
    bit advanced;

    advanced = 1'b0;
    fork
      begin
        wait (shared_status.local_host_status.micro_frame_count > target_microframe);
        advanced = 1'b1;
      end
      begin
        #(transfer_timeout);
      end
    join_any
    disable fork;
    if (!advanced) begin
      `uvm_fatal(
        report_id(),
        $sformatf(
          "%s did not advance past microframe %0d within %0t (current=%0d)",
          transfer_label,
          target_microframe,
          transfer_timeout,
          shared_status.local_host_status.micro_frame_count
        )
      )
    end
  endtask

  // Schedule packet_count 1024-byte transactions in one microframe and wait for
  // the next automatic 125 us SOF to close the service interval.
  virtual task body();
    int unsigned target_microframe;
    bit [3:0] target_ep_number;
    svt_usb_transfer::transfer_type_enum expected_xfer_type;

    completed = 1'b0;
    if (target_endpoint == null ||
        target_endpoint.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS ||
        !target_endpoint.anchor_index_valid ||
        packet_count == 0 ||
        packet_count > PACKETS_PER_INTERVAL) begin
      `uvm_fatal(report_id(), "Require a valid anchored ISO endpoint and packet_count in 1..3")
    end

    resolve_host_context(1'b1);
    if (shared_status.local_host_status == null) begin
      `uvm_fatal(report_id(), "SVT local_host_status is unavailable")
    end
    target_microframe = shared_status.local_host_status.micro_frame_count + 2;
    target_ep_number = 4'(target_endpoint.ep_number);
    expected_xfer_type = (target_endpoint.direction == USB_DIRECTION_IN) ?
                         svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER :
                         svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;

    `uvm_info(
      report_id(),
      $sformatf(
        "%s scheduling %0d/%0d transactions on %s in microframe %0d",
        transfer_label,
        packet_count,
        PACKETS_PER_INTERVAL,
        target_endpoint.convert2string(),
        target_microframe
      ),
      UVM_LOW
    )

    for (int unsigned index = 0; index < packet_count; index++) begin
      svt_usb_transfer transfer;
      svt_usb_transfer observed_transfer;
      uvm_sequence_item response;
      uvm_object completion;
      bit first_transaction;
      bit last_transaction;
      string reason;

      first_transaction = (index == 0);
      last_transaction = (index == (PACKETS_PER_INTERVAL - 1));
      transfer = svt_usb_transfer::type_id::create($sformatf("iso_xfer_%0d", index));
      begin_transfer_watch($sformatf("%s transaction %0d", transfer_label, index + 1), transfer_timeout);
      start_item(transfer, -1, p_sequencer.xfer_sequencer);
      transfer.cfg = usb_cfg;
      if (target_endpoint.direction == USB_DIRECTION_OUT) begin
        transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
        transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
      end
      transfer.reasonable_start_uframe_bus_interval.constraint_mode(0);
      transfer.reasonable_end_uframe_bus_interval.constraint_mode(0);
      transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
      if (!transfer.randomize() with {
            xfer_type == local::expected_xfer_type;
            device_address == local::device_address;
            endpoint_number == local::target_ep_number;
            payload_intended_byte_count == PACKET_BYTES;
            first_isoc_transaction == local::first_transaction;
            last_isoc_transaction == local::last_transaction;
            start_uframe_bus_interval == int'(local::target_microframe);
            end_uframe_bus_interval == int'(local::target_microframe);
            inter_transfer_delay_longint == 0;
          }) begin
        `uvm_fatal(report_id(), $sformatf("Unable to randomize %s transaction %0d", transfer_label, index))
      end
      if (target_endpoint.direction == USB_DIRECTION_OUT) begin
        for (int unsigned offset = 0; offset < PACKET_BYTES; offset++) begin
          transfer.payload.data[offset] = expected_byte(index * PACKET_BYTES + offset);
        end
      end
      finish_item(transfer);
      get_response(response, transfer.get_transaction_id());
      if (response == null || response.get_sequence_id() != transfer.get_sequence_id()) begin
        `uvm_fatal(report_id(), $sformatf("%s transaction %0d received an invalid routed response", transfer_label, index + 1))
      end
      end_transfer_watch(completion);
      check_transfer_correlation($sformatf("%s transaction %0d", transfer_label, index + 1), transfer, completion);
      if (!cast_completed_transfer(completion, observed_transfer, reason)) begin
        `uvm_fatal(report_id(), $sformatf("%s transaction %0d rejected: %s", transfer_label, index + 1, reason))
      end
      if (observed_transfer.status !== svt_sequence_item::ACCEPT ||
          observed_transfer.results_status !== '0 ||
          observed_transfer.xfer_type !== expected_xfer_type ||
          observed_transfer.device_address !== device_address ||
          observed_transfer.endpoint_number !== target_ep_number ||
          observed_transfer.payload == null ||
          observed_transfer.payload.byte_count !== PACKET_BYTES) begin
        `uvm_fatal(
          report_id(),
          $sformatf(
            "%s transaction %0d completion mismatch: status=%s results=0x%0h type=%s addr=%0d ep=%0d bytes=%0d",
            transfer_label,
            index + 1,
            observed_transfer.status.name(),
            observed_transfer.results_status,
            observed_transfer.xfer_type.name(),
            observed_transfer.device_address,
            observed_transfer.endpoint_number,
            (observed_transfer.payload == null) ? -1 : observed_transfer.payload.byte_count
          )
        )
      end
      if (target_endpoint.direction == USB_DIRECTION_IN) begin
        for (int unsigned offset = 0; offset < PACKET_BYTES; offset++) begin
          logic [7:0] observed_byte;
          logic [7:0] expected;

          observed_byte = observed_transfer.payload.get_byte_val(offset);
          expected = expected_byte(index * PACKET_BYTES + offset);
          if (observed_byte !== expected) begin
            `uvm_fatal(
              report_id(),
              $sformatf(
                "%s packet %0d byte %0d is 0x%02h, expected 0x%02h",
                transfer_label,
                index,
                offset,
                observed_byte,
                expected
              )
            )
          end
        end
      end
    end

    wait_for_microframe_end(target_microframe);
    if (packet_count < PACKETS_PER_INTERVAL) begin
      shared_status.remote_device_status[0]
          .endpoint_status[target_endpoint.anchor_index]
          .set_isoc_toggle_state(svt_usb_endpoint_status::ISOC_TOGGLE_RESET);
    end
    completed = 1'b1;
    `uvm_info(
      report_id(),
      $sformatf(
        "%s completed %0d/%0d transactions in microframe %0d and observed next SOF",
        transfer_label,
        packet_count,
        PACKETS_PER_INTERVAL,
        target_microframe
      ),
      UVM_LOW
    )
  endtask
endclass
