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

class usb_ocp_suspend_clear_seq extends svt_usb_link_service_clear_suspend_sequence;
  `uvm_object_utils(usb_ocp_suspend_clear_seq)
  usb_ocp_suspend_service_record record;
  svt_usb_status native_status;
  time timeout = 100ms;

  function new(string name = "usb_ocp_suspend_clear_seq");
    super.new(name);
    use_response_handler(1);
  endfunction

  virtual function void mid_do(uvm_sequence_item this_item);
    svt_usb_link_service service;
    super.mid_do(this_item);
    if (record == null || native_status == null || record.issued != null ||
        !$cast(service,this_item) || service.cfg == null ||
        service.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
        service.link_20_command_type !== svt_usb_link_service::USB_20_CLEAR_PORT_SUSPEND)
      `uvm_fatal("OCP_L2_STOCK_API", "Stock CLEAR did not expose one matching native request")
    record.issued = service;
    record.dispatch_stage = "stock_mid_do";
    `uvm_info("OCP_L2_DISPATCH", $sformatf(
      "op=LINK_CLEAR stage=stock_mid_do instance=%0d sequence=%0d transaction=%0d type=%s command=%s cfg=%0d prereq=%s prereq_delay=%g service_delay=%g link=%s power=%s time=%0t",
      service.get_inst_id(),service.get_sequence_id(),service.get_transaction_id(),
      service.service_type.name(),service.link_20_command_type.name(),service.cfg.get_inst_id(),
      service.prereq_link_20_state.name(),service.prereq_link_20_delay,
      service.link_service_delay,native_status.link_usb_20_state.name(),
      native_status.link_usb_20_power_state.name(),$realtime), UVM_LOW)
  endfunction

  virtual function void post_do(uvm_sequence_item this_item);
    super.post_do(this_item);
    if (record == null || record.issued == null || this_item != record.issued ||
        this_item.get_sequence_id() != get_sequence_id())
      `uvm_fatal("OCP_L2_STOCK_API", "Stock CLEAR request is not owned by the live adapter")
    record.submitted = 1;
    record.dispatch_stage = "stock_post_do";
    `uvm_info("OCP_L2_DISPATCH", $sformatf(
      "op=LINK_CLEAR stage=stock_post_do instance=%0d sequence=%0d transaction=%0d time=%0t",
      this_item.get_inst_id(),this_item.get_sequence_id(),this_item.get_transaction_id(),
      $realtime), UVM_LOW)
  endfunction

  virtual function void response_handler(uvm_sequence_item response);
    if (record == null)
      `uvm_fatal("OCP_L2_RESPONSE_API", "Missing stock CLEAR response record")
    record.ocp_check_response(response);
  endfunction

  task ocp_do_check_stock_service();
    if (record == null || native_status == null ||
        record.operation != usb_ocp_suspend_service_record::LINK_CLEAR)
      `uvm_fatal("OCP_L2_STOCK_API", "Missing stock CLEAR lifecycle record")
    record.dispatch_stage = "stock_body";
    super.body();
    record.dispatch_stage = "stock_body_returned";
    if (record.issued == null || !record.submitted)
      `uvm_fatal("OCP_L2_STOCK_API", "Stock CLEAR returned without observed request dispatch")
    record.ocp_wait_check_retirement();
  endtask

  task body();
    fork
      begin
        fork
          ocp_do_check_stock_service();
          begin
            #(timeout);
            `uvm_fatal("OCP_L2_SERVICE_API", "Stock CLEAR live-response deadline")
          end
        join_any
        disable fork;
      end
    join
  endtask
endclass
