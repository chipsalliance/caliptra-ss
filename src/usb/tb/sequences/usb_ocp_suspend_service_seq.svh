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

// One native service per issuing sequence. The owner holds this sequence live
// through physical readiness and the observation/recovery interval; actual
// responses are checked here, never at the outer virtual sequence.
class usb_ocp_suspend_service_seq extends uvm_sequence;
  `uvm_object_utils(usb_ocp_suspend_service_seq)
  svt_usb_configuration cfg;
  svt_usb_status native_status;
  usb_ocp_suspend_service_record record;
  time timeout = 100ms;

  function new(string name = "usb_ocp_suspend_service_seq");
    super.new(name);
    use_response_handler(1);
  endfunction

  function void ocp_report_dispatch(string stage);
    record.dispatch_stage = stage;
    `uvm_info("OCP_L2_DISPATCH", $sformatf(
      "op=%s stage=%s target=%s instance=%0d sequence=%0d transaction=%0d time=%0t",
      record.operation.name(),stage,get_sequencer().get_full_name(),
      (record.issued == null) ? -1 : record.issued.get_inst_id(),
      (record.issued == null) ? -1 : record.issued.get_sequence_id(),
      (record.issued == null) ? -1 : record.issued.get_transaction_id(),$realtime), UVM_LOW)
  endfunction

  virtual function void response_handler(uvm_sequence_item response);
    if (record == null)
      `uvm_fatal("OCP_L2_RESPONSE_API", "Missing native service response record")
    record.ocp_check_response(response);
  endfunction

  task ocp_do_check_service();
    svt_usb_protocol_service protocol_request;
    if (cfg == null || record == null || native_status == null ||
        record.operation == usb_ocp_suspend_service_record::LINK_CLEAR)
      `uvm_fatal("OCP_L2_SERVICE", "Missing service configuration/callback record")
    ocp_report_dispatch("body");
    protocol_request = svt_usb_protocol_service::type_id::create("protocol_request");
    record.issued = protocol_request;
    ocp_report_dispatch("before_start_item");
    start_item(protocol_request);
    ocp_report_dispatch("granted");
    protocol_request.cfg = cfg;
    if (!protocol_request.randomize() with {
        service_type == svt_usb_protocol_service::SOF;
        if (local::record.operation == usb_ocp_suspend_service_record::SOF_OFF)
          protocol_20_command_type == svt_usb_protocol_service::USB_20_SOF_OFF;
        else
          protocol_20_command_type == svt_usb_protocol_service::USB_20_SOF_ON;
      }) `uvm_fatal("OCP_L2_SERVICE", "Native SOF randomization failed")
    finish_item(protocol_request);
    ocp_report_dispatch("finish_item_returned");
    record.submitted = 1;
    ocp_report_dispatch("waiting_callback");
    record.ocp_wait_check_retirement();
  endtask

  task body();
    fork
      begin
        fork
          ocp_do_check_service();
          begin
            #(timeout);
            `uvm_fatal("OCP_L2_SERVICE_API", "Service submission/callback/live-response deadline")
          end
        join_any
        disable fork;
      end
    join
  endtask
endclass
