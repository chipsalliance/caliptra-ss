// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_protocol_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_reset_protocol_seq)
  svt_usb_protocol_service::protocol_command_type_enum operation;
  bit immediate_abort;
  logic [6:0] target_address;
  svt_usb_protocol_service issued;
  longint unsigned floor;
  int unsigned responses;
  bit executed;
  bit release_requested;
  bit finished;

  function new(string name = "usb_ocp_reset_protocol_seq");
    super.new(name);
    use_response_handler(1);
  endfunction

  virtual function void response_handler(uvm_sequence_item response);
    svt_usb_protocol_service service;
    if (issued == null || !$cast(service,response) ||
        service.get_sequence_id() != get_sequence_id() ||
        service.get_transaction_id() != issued.get_transaction_id() ||
        service.service_type !== svt_usb_protocol_service::CMD ||
        service.protocol_command_type !== operation ||
        service.device_address !== target_address || service.endpoint_number !== 0 ||
        service.direction !== svt_usb_types::OUT ||
        service.pause_at_transfer_boundary !== 0 ||
        service.force_immediate_abort !== immediate_abort)
      `uvm_fatal("OCP_RESET_PROTOCOL", "Unmatched typed scoped protocol-service response")
    responses++;
    // return_status is recorded, not guessed to be a particular PAUSE result.
    `uvm_info("OCP_RESET_PROTOCOL", $sformatf(
      "response sequence=%0d transaction=%0d cmd=%s target=%0d count=%0d status=%s return_status=%0d immediate_abort=%0b",
      service.get_sequence_id(),service.get_transaction_id(),operation.name(),
      target_address,responses,service.status.name(),service.return_status,
      immediate_abort), UVM_LOW)
  endfunction

  task body();
    usb_ocp_base_service_callback actual;
    if (observer == null ||
        !(operation inside {svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER}))
      `uvm_fatal("OCP_RESET_PROTOCOL", "Missing observer or unsupported scoped protocol command")
    resolve_host_context(1);
    actual = observer.service_callback;
    if (actual == null)
      `uvm_fatal("OCP_RESET_PROTOCOL", "Missing existing service completion callback")
    floor = actual.completed_commands;
    // svt_usb_protocol_service::force_immediate_abort avoids clean-break
    // deferral. The owner permits abort only after selected hardware reset.
    immediate_abort = (operation == svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER);
    issued = svt_usb_protocol_service::type_id::create("scoped_protocol_command");
    start_item(issued,-1,p_sequencer.prot_service_sequencer);
    issued.cfg = usb_cfg;
    // Descriptor property PAUSE=0 holds between completed USB2 transactions.
    // Stock PAUSE does not expose it. No post-randomization field override.
    if (!issued.randomize() with {
          service_type == svt_usb_protocol_service::CMD;
          protocol_command_type == local::operation;
          device_address == local::target_address;
          endpoint_number == 0;
          direction == svt_usb_types::OUT;
          pause_at_transfer_boundary == 0;
          force_immediate_abort == local::immediate_abort;
        }) `uvm_fatal("OCP_RESET_PROTOCOL", "Scoped native command randomization failed")
    finish_item(issued);
    issued.end_event.wait_on();
    wait (actual.completed_commands > floor);
    if (actual.command_sequence_id != get_sequence_id() ||
        actual.command_transaction_id != issued.get_transaction_id() ||
        actual.command != operation || actual.address !== target_address ||
        actual.endpoint !== 0 || actual.pause_at_transfer_boundary !== 0 ||
        actual.force_immediate_abort !== immediate_abort || !actual.accepted)
      `uvm_fatal("OCP_RESET_PROTOCOL", "Scoped command lacks its correlated accepted end callback")
    executed = 1;
    `uvm_info("OCP_RESET_PROTOCOL", $sformatf(
      "end sequence=%0d transaction=%0d cmd=%s target=%0d status=%s return_status=%0d immediate_abort=%0b",
      get_sequence_id(),issued.get_transaction_id(),operation.name(),target_address,
      actual.status_name,actual.return_status,immediate_abort), UVM_LOW)
    // Keep the issuer alive through the owner's actual old-control/final
    // observation barriers. No exact response count or final-response flag.
    wait (release_requested);
    if (responses == 0)
      `uvm_fatal("OCP_RESET_PROTOCOL", "Ended scoped command has no captured routed response")
    finished = 1;
  endtask
endclass
