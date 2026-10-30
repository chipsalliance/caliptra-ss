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

class usb_lpm_capability_host_seq extends usb_init_host_seq;
  `uvm_object_utils(usb_lpm_capability_host_seq)

  // USB 2.0 LPM ECN section 3, Table 3-1.
  localparam int unsigned DISCOVERY_REQUEST_COUNT = 3;
  localparam byte unsigned BOS_DESCRIPTOR_TYPE = 15;
  localparam byte unsigned DEVICE_CAPABILITY_DESCRIPTOR_TYPE = 16;
  localparam byte unsigned USB20_EXTENSION_CAPABILITY_TYPE = 2;
  localparam int unsigned BOS_HEADER_LENGTH = 5;
  localparam int unsigned USB20_EXTENSION_LENGTH = 7;
  localparam int unsigned DESCRIPTOR_TYPE_OFFSET = 1;
  localparam int unsigned DEVICE_BCD_USB_OFFSET = 2;
  localparam int unsigned BOS_TOTAL_LENGTH_OFFSET = 2;
  localparam int unsigned BOS_CAPABILITY_COUNT_OFFSET = 4;
  localparam int unsigned CAPABILITY_TYPE_OFFSET = 2;
  localparam int unsigned CAPABILITY_ATTRIBUTES_OFFSET = 3;
  localparam logic [31:0] LPM_CAPABILITY_MASK = 32'h0000_0002;

  function new(string name = "usb_lpm_capability_host_seq");
    super.new(name);
  endfunction

  virtual task body();
    byte unsigned no_payload[$];
    byte unsigned bos_header[$];
    int unsigned total_length;
    int unsigned capability_count;
    int unsigned offset;
    bit usb20_extension_found;
    bit lpm_found;

    completed = 1'b0;
    validated_transfer_count = 0;
    if (control_endpoint == null || !control_endpoint.anchor_index_valid) begin
      `uvm_fatal("USB_LPM_DISCOVERY", "An applied control endpoint is required")
    end
    resolve_host_context();
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_DESCRIPTOR,
      {DEVICE_DESCRIPTOR_TYPE, 8'h00}, 16'h0000, 16'(DEVICE_DESCRIPTOR_LENGTH),
      device_address, 1, "Discover_LPM_device", no_payload, 1'b1
    );
    if (discovered_payload[0] != DEVICE_DESCRIPTOR_LENGTH ||
        discovered_payload[DESCRIPTOR_TYPE_OFFSET] != DEVICE_DESCRIPTOR_TYPE ||
        {discovered_payload[DEVICE_BCD_USB_OFFSET + 1], discovered_payload[DEVICE_BCD_USB_OFFSET]} < 16'h0201) begin
      `uvm_fatal("USB_LPM_DISCOVERY", "The device does not advertise BOS descriptor support")
    end
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_DESCRIPTOR,
      {BOS_DESCRIPTOR_TYPE, 8'h00}, 16'h0000, 16'(BOS_HEADER_LENGTH),
      device_address, 2, "Discover_BOS_header", no_payload, 1'b1
    );
    bos_header = discovered_payload;
    total_length = {bos_header[BOS_TOTAL_LENGTH_OFFSET + 1], bos_header[BOS_TOTAL_LENGTH_OFFSET]};
    if (bos_header[0] != BOS_HEADER_LENGTH ||
        bos_header[DESCRIPTOR_TYPE_OFFSET] != BOS_DESCRIPTOR_TYPE ||
        total_length < BOS_HEADER_LENGTH || bos_header[BOS_CAPABILITY_COUNT_OFFSET] == 0) begin
      `uvm_fatal("USB_LPM_DISCOVERY", "The BOS header is malformed or has no device capabilities")
    end
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_DESCRIPTOR,
      {BOS_DESCRIPTOR_TYPE, 8'h00}, 16'h0000, 16'(total_length),
      device_address, 3, "Discover_BOS_capabilities", no_payload, 1'b1
    );
    foreach (bos_header[index]) begin
      if (discovered_payload[index] != bos_header[index]) begin
        `uvm_fatal("USB_LPM_DISCOVERY", "The BOS header changed between discovery requests")
      end
    end
    offset = BOS_HEADER_LENGTH;
    capability_count = 0;
    lpm_found = 1'b0;
    usb20_extension_found = 1'b0;
    while (offset < total_length) begin
      int unsigned capability_length;

      if (total_length - offset <= CAPABILITY_TYPE_OFFSET) begin
        `uvm_fatal("USB_LPM_DISCOVERY", "Truncated device capability header")
      end
      capability_length = discovered_payload[offset];
      if (capability_length <= CAPABILITY_TYPE_OFFSET || capability_length > total_length - offset ||
          discovered_payload[offset + DESCRIPTOR_TYPE_OFFSET] != DEVICE_CAPABILITY_DESCRIPTOR_TYPE) begin
        `uvm_fatal("USB_LPM_DISCOVERY", "Invalid device capability length or descriptor type")
      end
      if (discovered_payload[offset + CAPABILITY_TYPE_OFFSET] == USB20_EXTENSION_CAPABILITY_TYPE) begin
        logic [31:0] attributes;

        if (capability_length != USB20_EXTENSION_LENGTH || usb20_extension_found) begin
          `uvm_fatal("USB_LPM_DISCOVERY", "Invalid or duplicate USB 2.0 extension capability")
        end
        usb20_extension_found = 1'b1;
        attributes = '0;
        for (int unsigned lane = 0; lane < 4; lane++) begin
          attributes[8 * lane +: 8] = discovered_payload[offset + CAPABILITY_ATTRIBUTES_OFFSET + lane];
        end
        lpm_found = (attributes & LPM_CAPABILITY_MASK) != 0;
      end
      offset += capability_length;
      capability_count++;
    end
    if (!lpm_found || capability_count != bos_header[BOS_CAPABILITY_COUNT_OFFSET]) begin
      `uvm_fatal("USB_LPM_DISCOVERY", "BOS discovery did not establish a consistent LPM-capable device")
    end
    completed = validated_transfer_count == DISCOVERY_REQUEST_COUNT;
    `uvm_info("USB_LPM_DISCOVERY", "Discovered LPM support through device and BOS control transfers", UVM_LOW)
  endtask
endclass
