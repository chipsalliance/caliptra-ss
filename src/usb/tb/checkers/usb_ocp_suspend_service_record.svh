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

class usb_ocp_suspend_service_record extends uvm_object;
  `uvm_object_utils(usb_ocp_suspend_service_record)
  typedef enum int {SOF_OFF, SOF_ON, LINK_CLEAR} operation_e;
  operation_e operation;
  bit ended;
  int sequence_id;
  int transaction_id;
  int instance_id;
  string status_name;
  realtime ended_at;
  int unsigned responses;
  int unsigned ingress_count;
  uvm_sequence_base issuer;
  uvm_sequence_item issued;
  bit submitted;
  bit release_requested;
  bit finished;
  string dispatch_stage = "not_started";

  function new(string name = "usb_ocp_suspend_service_record");
    super.new(name);
  endfunction

  function void ocp_check_response(uvm_sequence_item response);
    svt_usb_protocol_service protocol_response;
    svt_usb_link_service link_response;
    svt_sequence_item::status_enum actual_status;
    if (response == null || issued == null ||
        response.get_sequence_id() != issued.get_sequence_id() ||
        response.get_transaction_id() != issued.get_transaction_id())
      `uvm_fatal("OCP_L2_RESPONSE_API", "Missing/mismatched native service response identity")
    if (operation == LINK_CLEAR) begin
      if (!$cast(link_response,response) ||
          link_response.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
          link_response.link_20_command_type !== svt_usb_link_service::USB_20_CLEAR_PORT_SUSPEND)
        `uvm_fatal("OCP_L2_RESPONSE_API", "Wrong typed CLEAR response operation")
      actual_status = link_response.status;
    end else begin
      if (!$cast(protocol_response,response) ||
          protocol_response.service_type !== svt_usb_protocol_service::SOF ||
          (operation == SOF_OFF &&
           protocol_response.protocol_20_command_type !== svt_usb_protocol_service::USB_20_SOF_OFF) ||
          (operation == SOF_ON &&
           protocol_response.protocol_20_command_type !== svt_usb_protocol_service::USB_20_SOF_ON))
        `uvm_fatal("OCP_L2_RESPONSE_API", "Wrong typed SOF response operation")
      actual_status = protocol_response.status;
    end
    responses++;
    `uvm_info("OCP_L2_RESPONSE", $sformatf(
      "op=%s response=%0d instance=%0d sequence=%0d transaction=%0d status=%s time=%0t",
      operation.name(),responses,response.get_inst_id(),response.get_sequence_id(),
      response.get_transaction_id(),actual_status.name(),$realtime), UVM_LOW)
    // Response/callback ordering and status mutation are not guaranteed.
    // Neither INITIAL nor ACCEPT proves execution or physical state here.
    if (actual_status === svt_sequence_item::INITIAL)
      `uvm_info("OCP_L2_RESPONSE", "INITIAL response snapshot; no execution or physical credit", UVM_LOW)
    else if (actual_status !== svt_sequence_item::ACCEPT)
      `uvm_fatal("OCP_L2_RESPONSE_API", "Unsupported SOF/link response status")
  endfunction

  task ocp_wait_check_retirement();
    wait (ended);
    if (issued == null || issuer == null ||
        sequence_id != issued.get_sequence_id() ||
        transaction_id != issued.get_transaction_id() ||
        sequence_id != issuer.get_sequence_id())
      `uvm_fatal("OCP_L2_SERVICE_API", "Executed service did not preserve actual issuing IDs")
    wait (release_requested);
    `uvm_info("OCP_L2_SERVICE", $sformatf(
      "Retiring op=%s actual_responses=%0d executed_at=%0t retire_at=%0t",
      operation.name(),responses,ended_at,$realtime), UVM_LOW)
    finished = 1;
  endtask

  function void ocp_capture_end(svt_sequence_item item,
      svt_sequence_item::status_enum actual_status);
    if (item == null || ended)
      `uvm_fatal("OCP_L2_SERVICE", "Null or duplicate executed service completion")
    ended = 1;
    sequence_id = item.get_sequence_id();
    transaction_id = item.get_transaction_id();
    instance_id = item.get_inst_id();
    status_name = actual_status.name();
    ended_at = $realtime;
    `uvm_info("OCP_L2_SERVICE", $sformatf(
      "Executed op=%s instance=%0d sequence=%0d transaction=%0d status=%s time=%0t",
      operation.name(),instance_id,sequence_id,transaction_id,status_name,ended_at), UVM_LOW)
    // SOF end callbacks do not specify a terminal status mutation. Preserve
    // INITIAL as a notification; the host separately requires packet/link effects.
    if (actual_status === svt_sequence_item::INITIAL &&
        operation inside {SOF_OFF,SOF_ON})
      `uvm_info("OCP_L2_SERVICE", "Default SOF status snapshot; independent physical effect remains required", UVM_LOW)
    else if (actual_status !== svt_sequence_item::ACCEPT)
      `uvm_fatal("OCP_L2_SERVICE_API", "Unsupported executed SOF/link terminal status")
  endfunction
endclass
