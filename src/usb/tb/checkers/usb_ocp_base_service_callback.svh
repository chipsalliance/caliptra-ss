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

class usb_ocp_base_service_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_ocp_base_service_callback)
  longint unsigned completed_commands;
  int command;
  logic [6:0] address;
  logic [3:0] endpoint;
  bit pause_at_transfer_boundary;
  int return_status;
  bit accepted;
  string status_name;

  function new(string name = "usb_ocp_base_service_callback");
    super.new(name);
  endfunction

  virtual function void protocol_service_ended(
      svt_usb_protocol component, svt_usb_protocol_service protocol_service);
    if (protocol_service == null)
      `uvm_fatal("OCP_EPN_COMMAND", "Missing completed native service descriptor")
    if (protocol_service.service_type != svt_usb_protocol_service::CMD ||
        !(protocol_service.protocol_command_type inside {
          svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING})) return;
    // Copy the completed descriptor; never retain a mutable vendor handle.
    command = protocol_service.protocol_command_type;
    address = protocol_service.device_address;
    endpoint = protocol_service.endpoint_number;
    pause_at_transfer_boundary = protocol_service.pause_at_transfer_boundary;
    return_status = protocol_service.return_status;
    accepted = (protocol_service.status === svt_sequence_item::ACCEPT);
    status_name = protocol_service.status.name();
    completed_commands++;
    `uvm_info("OCP_EPN_COMMAND",$sformatf(
      "Native completion serial=%0d cmd=%0d addr=%0d ep=%0d mode=%0b status=%s return_status=%0d",
      completed_commands,command,address,endpoint,pause_at_transfer_boundary,
      status_name,return_status),UVM_LOW)
  endfunction
endclass
