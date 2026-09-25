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
// Supplies the host half of the USB DMA endpoint-skip scenario. This sequence
// is protocol-only: it drives USB traffic and never touches DUT registers or
// packet memory. usb_dev_skip_seq performs every device-side operation.
//
// The sequence assumes usb_init_host_seq has already enumerated the device to
// address 1 and configuration 1, so the link is ENABLED, SOF generation is
// running, and the SVT host is reconfigured for address 1. It then issues a
// single high-speed bulk OUT transfer of USB_DEV_SKIP_RECOVERY_BYTES bytes
// carrying the fixed payload 0xA0..0xAF, and accepts the transfer only when the
// SVT completion matches that intent.
//
// The target endpoint is supplied as a usb_endpoint_profile by usb_dev_skip_seq
// rather than named here, so this sequence contains no assumption about which
// endpoint carries the recovery transfer or where it sits in the VIP anchor
// array. usb_host_base_seq supplies the submit, observe, and timeout mechanics.
//
// The device-side endpoint is armed before this sequence starts, so the
// transfer does not rely on NAK-retry timing to succeed.
class usb_dev_skip_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_dev_skip_host_seq)

  // Bound the single bulk transfer independently of the scenario timeout.
  localparam time USB_BULK_TRANSFER_TIMEOUT = 200us;

  localparam bit [6:0] ENUMERATED_DEVICE_ADDRESS = 7'd1;

  // Supplied by usb_dev_skip_seq before start(); names the endpoint to drive
  // and its VIP anchor index.
  usb_endpoint_profile target_endpoint;

  function new(string name = "usb_dev_skip_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_SKIP_HOST";
  endfunction

  // Rejects any completion that is not the intended accepted bulk OUT transfer
  // on the enumerated device and the requested endpoint. The rejection reason
  // identifies the mismatch so a fatal report does not require waveform
  // inspection.
  function automatic bit validate_completed_transfer(uvm_object completed_object, output string failure_reason);
    svt_usb_transfer transfer;
    int observed_payload_count;
    string transfer_context;

    if (!cast_completed_transfer(completed_object, transfer, failure_reason)) begin
      return 1'b0;
    end

    observed_payload_count = (transfer.payload === null) ? -1 : transfer.payload.byte_count;
    transfer_context = $sformatf(
      {"expected status=ACCEPT type=BULK_OUT_TRANSFER addr=%0d ep=%0d payload_len=%0d; ",
       "observed status=%s type=%s addr=%0d ep=%0d payload_len=%0d"},
      ENUMERATED_DEVICE_ADDRESS,
      target_endpoint.ep_number,
      USB_DEV_SKIP_RECOVERY_BYTES,
      transfer.status.name(),
      transfer.xfer_type.name(),
      transfer.device_address,
      transfer.endpoint_number,
      observed_payload_count
    );

    if (transfer.status !== svt_sequence_item::ACCEPT) begin
      failure_reason = {"terminal status is not ACCEPT; ", transfer_context};
      return 1'b0;
    end
    if (transfer.xfer_type !== svt_usb_transfer::BULK_OUT_TRANSFER) begin
      failure_reason = {"transfer kind is not BULK_OUT_TRANSFER; ", transfer_context};
      return 1'b0;
    end
    if (transfer.device_address !== ENUMERATED_DEVICE_ADDRESS) begin
      failure_reason = {"device address does not match; ", transfer_context};
      return 1'b0;
    end
    if (transfer.endpoint_number !== 4'(target_endpoint.ep_number)) begin
      failure_reason = {"endpoint number does not match the requested endpoint; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload === null) begin
      failure_reason = {"payload handle is null; ", transfer_context};
      return 1'b0;
    end
    if (transfer.payload.byte_count !== USB_DEV_SKIP_RECOVERY_BYTES) begin
      failure_reason = {"payload length does not match; ", transfer_context};
      return 1'b0;
    end

    return 1'b1;
  endfunction

  // Issues the recovery bulk OUT transfer and gates completion on a validated
  // SVT completion rather than on elapsed time.
  virtual task body();
    svt_usb_transfer bulk_transfer;
    uvm_object completed_object;
    string failure_reason;
    bit [3:0] target_ep_number;

    completed = 1'b0;

    if (target_endpoint == null) begin
      `uvm_fatal("USB_SKIP_HOST", "No target endpoint profile was supplied to the recovery host sequence")
    end
    if (!target_endpoint.anchor_index_valid) begin
      `uvm_fatal("USB_SKIP_HOST", $sformatf("%s has no VIP anchor index, so the transfer cannot be anchored", target_endpoint.describe()))
    end
    resolve_host_context();
    target_ep_number = 4'(target_endpoint.ep_number);

    `uvm_info(
      "USB_SKIP_HOST",
      $sformatf(
        "Submitting post-skip recovery bulk OUT on %s: addr=%0d bytes=%0d payload=0x%02h..0x%02h",
        target_endpoint.describe(),
        ENUMERATED_DEVICE_ADDRESS,
        USB_DEV_SKIP_RECOVERY_BYTES,
        USB_DEV_SKIP_PAYLOAD_BASE,
        USB_DEV_SKIP_PAYLOAD_BASE + USB_DEV_SKIP_RECOVERY_BYTES - 1
      ),
      UVM_LOW
    )

    bulk_transfer = svt_usb_transfer::type_id::create("skip_recovery_bulk_out");

    begin_transfer_watch();
    start_item(bulk_transfer, -1, p_sequencer.xfer_sequencer);
    bulk_transfer.cfg = usb_cfg;
    // Select the caller-supplied payload bytes instead of a generated
    // pattern so the device-side data comparison uses known values.
    bulk_transfer.payload.USER_DEFINED_ALGORITHM_wt = 1;
    bulk_transfer.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
    // Pin the device, endpoint, and ustream configuration indices. The
    // endpoint anchor comes from the environment profile; SVT disables anchor
    // randomization so the transfer keeps these selections.
    bulk_transfer.fix_anchors(0, target_endpoint.anchor_index, 0);
    if (!bulk_transfer.randomize() with {
          xfer_type == svt_usb_transfer::BULK_OUT_TRANSFER;
          device_address == ENUMERATED_DEVICE_ADDRESS;
          endpoint_number == target_ep_number;
          payload_intended_byte_count == USB_DEV_SKIP_RECOVERY_BYTES;
        }) begin
      `uvm_fatal("USB_SKIP_HOST", "Unable to randomize the recovery bulk OUT transfer")
    end
    for (int unsigned byte_index = 0; byte_index < USB_DEV_SKIP_RECOVERY_BYTES; byte_index++) begin
      bulk_transfer.payload.data[byte_index] = USB_DEV_SKIP_PAYLOAD_BASE + byte_index;
    end
    finish_item(bulk_transfer);

    end_transfer_watch("Recovery bulk OUT", USB_BULK_TRANSFER_TIMEOUT, completed_object);
    check_transfer_correlation("Recovery bulk OUT", bulk_transfer, completed_object);
    if (!validate_completed_transfer(completed_object, failure_reason)) begin
      `uvm_fatal("USB_SKIP_HOST", $sformatf("Recovery bulk OUT completion rejected: %s", failure_reason))
    end

    completed = 1'b1;
    `uvm_info("USB_SKIP_HOST", $sformatf("Recovery bulk OUT accepted on the bus: bytes=%0d", USB_DEV_SKIP_RECOVERY_BYTES), UVM_LOW)
  endtask
endclass
