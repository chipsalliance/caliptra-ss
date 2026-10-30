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

class usb_remote_wake_enable_host_seq extends usb_init_host_seq;
  `uvm_object_utils(usb_remote_wake_enable_host_seq)

  // USB 2.0 Table 9-10 bmAttributes and Table 9-6 device status.
  localparam int unsigned CONFIGURATION_ATTRIBUTES_OFFSET = 7;
  localparam int unsigned AUTHORIZATION_REQUEST_COUNT = 3;

  function new(string name = "usb_remote_wake_enable_host_seq");
    super.new(name);
  endfunction

  virtual task body();
    byte unsigned no_payload[$];
    byte unsigned enabled_status[$];

    completed = 1'b0;
    validated_transfer_count = 0;
    if (control_endpoint == null || !control_endpoint.anchor_index_valid) begin
      `uvm_fatal("USB_REMOTE_WAKE_ENABLE", "An applied control endpoint is required")
    end
    resolve_host_context();
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_DESCRIPTOR,
      {CONFIGURATION_DESCRIPTOR_TYPE, 8'h00}, 16'h0000, 16'(CONFIGURATION_DESCRIPTOR_LENGTH),
      device_address, 1, "Discover_remote_wakeup_capability", no_payload, 1'b1
    );
    if (discovered_payload[0] != CONFIGURATION_DESCRIPTOR_LENGTH ||
        discovered_payload[1] != CONFIGURATION_DESCRIPTOR_TYPE ||
        !(discovered_payload[CONFIGURATION_ATTRIBUTES_OFFSET] & usb_init_seq::REMOTE_WAKEUP_ATTRIBUTE)) begin
      `uvm_fatal("USB_REMOTE_WAKE_ENABLE", "The device did not advertise remote-wakeup capability")
    end
    run_control_transfer(
      svt_usb_types::HOST_TO_DEVICE, svt_usb_types::SET_FEATURE,
      usb_init_seq::DEVICE_REMOTE_WAKEUP_FEATURE, 16'h0000, 16'h0000,
      device_address, 2, "SET_FEATURE_DEVICE_REMOTE_WAKEUP", no_payload
    );
    enabled_status = '{usb_init_seq::REMOTE_WAKEUP_STATUS, 8'h00};
    run_control_transfer(
      svt_usb_types::DEVICE_TO_HOST, svt_usb_types::GET_STATUS,
      16'h0000, 16'h0000, 16'h0002,
      device_address, 3, "GET_STATUS_remote_wakeup_enabled", enabled_status
    );
    completed = validated_transfer_count == AUTHORIZATION_REQUEST_COUNT;
    `uvm_info("USB_REMOTE_WAKE_ENABLE", "Discovered, enabled, and read back DEVICE_REMOTE_WAKEUP through EP0", UVM_LOW)
  endtask
endclass
