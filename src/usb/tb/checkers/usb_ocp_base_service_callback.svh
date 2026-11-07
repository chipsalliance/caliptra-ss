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
  bit force_immediate_abort;
  int return_status;
  bit accepted;
  string status_name;
  realtime command_ended_at;
  bit capture_mixed_abort;
  logic [6:0] expected_abort_address;
  logic [7:0] expected_abort_setup[8];
  usb_ocp_event mixed_native_abort;

  function new(string name = "usb_ocp_base_service_callback");
    super.new(name);
  endfunction

  function void ocp_configure_abort_capture(logic [6:0] target_address,
      logic [7:0] target_setup[8]);
    if (capture_mixed_abort || mixed_native_abort != null)
      `uvm_fatal("OCP_MIXED_COMMAND", "Previous native abort evidence is still outstanding")
    expected_abort_address = target_address;
    expected_abort_setup = target_setup;
    capture_mixed_abort = 1;
  endfunction

  task ocp_wait_native_abort(output usb_ocp_event actual);
    wait (mixed_native_abort != null);
    actual = mixed_native_abort;
    mixed_native_abort = null;
    capture_mixed_abort = 0;
  endtask

  virtual function void transfer_ended(svt_usb_protocol component, svt_usb_transfer transfer);
    logic [7:0] actual_setup[8];
    if (!capture_mixed_abort) return;
    if (transfer == null)
      `uvm_fatal("OCP_MIXED_COMMAND", "Missing ended native transfer")
    if (transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) return;
    // Enum storage is wider than USB 2.0 Table 9-2's 1/2/5-bit fields;
    // observer build_phase already guards the enums' numeric encodings.
    actual_setup = '{{1'(transfer.setup_data_bmrequesttype_dir),
                     2'(transfer.setup_data_bmrequesttype_type),
                     5'(transfer.setup_data_bmrequesttype_recipient)},
      transfer.setup_data_brequest,transfer.setup_data_w_value[7:0],
      transfer.setup_data_w_value[15:8],transfer.setup_data_w_index[7:0],
      transfer.setup_data_w_index[15:8],transfer.setup_data_w_length[7:0],
      transfer.setup_data_w_length[15:8]};
    if (transfer.device_address !== expected_abort_address ||
        transfer.endpoint_number !== 0 || actual_setup !== expected_abort_setup) return;
    if (mixed_native_abort != null)
      `uvm_fatal("OCP_MIXED_COMMAND", "Duplicate native end for the captured original control")
    mixed_native_abort = usb_ocp_event::type_id::create("mixed_native_abort");
    mixed_native_abort.kind = usb_ocp_event::USB_TRANSFER;
    mixed_native_abort.observed_at = $realtime;
    mixed_native_abort.address = transfer.device_address;
    mixed_native_abort.endpoint = transfer.endpoint_number;
    mixed_native_abort.setup = actual_setup;
    mixed_native_abort.transfer_type = transfer.xfer_type;
    mixed_native_abort.native_aborted = (transfer.status === svt_sequence_item::ABORTED);
    mixed_native_abort.results = transfer.results_status;
    mixed_native_abort.completed_bytes = transfer.completed_payload_bytes();
  endfunction

  virtual function void protocol_service_ended(
      svt_usb_protocol component, svt_usb_protocol_service protocol_service);
    if (protocol_service == null)
      `uvm_fatal("OCP_EPN_COMMAND", "Missing completed native service descriptor")
    if (protocol_service.service_type != svt_usb_protocol_service::CMD ||
        !(protocol_service.protocol_command_type inside {
          svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER})) return;
    if (protocol_service.protocol_command_type ==
        svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER && !capture_mixed_abort) return;
    // Copy the completed descriptor; never retain a mutable vendor handle.
    command = protocol_service.protocol_command_type;
    address = protocol_service.device_address;
    endpoint = protocol_service.endpoint_number;
    pause_at_transfer_boundary = protocol_service.pause_at_transfer_boundary;
    force_immediate_abort = protocol_service.force_immediate_abort;
    return_status = protocol_service.return_status;
    accepted = (protocol_service.status === svt_sequence_item::ACCEPT);
    status_name = protocol_service.status.name();
    command_ended_at = $realtime;
    completed_commands++;
    `uvm_info("OCP_EPN_COMMAND",$sformatf(
      "Native completion serial=%0d cmd=%0d addr=%0d ep=%0d mode=%0b status=%s return_status=%0d",
      completed_commands,command,address,endpoint,pause_at_transfer_boundary,
      status_name,return_status),UVM_LOW)
  endfunction
endclass
