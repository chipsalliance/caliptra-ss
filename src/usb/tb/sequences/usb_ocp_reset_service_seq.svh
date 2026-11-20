// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_service_seq extends svt_usb_link_service_usb20_any_state_reset_sequence;
  `uvm_object_utils(usb_ocp_reset_service_seq)
  svt_usb_link_service issued[$];
  bit executed[int];
  int unsigned responses[int];
  int unsigned ingress;
  bit release_requested;
  bit finished;

  function new(string name = "usb_ocp_reset_service_seq");
    super.new(name);
    use_response_handler(1);
  endfunction

  virtual function void mid_do(uvm_sequence_item this_item);
    svt_usb_link_service service;
    super.mid_do(this_item);
    if (!$cast(service,this_item) || service.cfg == null ||
        service.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
        service.link_20_command_type !== svt_usb_link_service::USB_20_PORT_RESET)
      `uvm_fatal("OCP_RESET_NATIVE", "Stock any-state sequence exposed an unrelated native service")
    // UVM may assign transaction_id only after mid_do. Keep the live issuer
    // handle here; callback/response matching reads the eventual native IDs.
    issued.push_back(service);
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "mid_do instance=%0d sequence=%0d transaction=%0d cfg=%0d service=%s command=%s",
      service.get_inst_id(),service.get_sequence_id(),service.get_transaction_id(),
      service.cfg.get_inst_id(),service.service_type.name(),
      service.link_20_command_type.name()), UVM_LOW)
  endfunction

  virtual function void post_do(uvm_sequence_item this_item);
    svt_usb_link_service service;
    super.post_do(this_item);
    if (!$cast(service,this_item))
      `uvm_fatal("OCP_RESET_NATIVE", "Stock reset post_do is not a typed link service")
    ocp_check_identity(service);
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "post_do instance=%0d sequence=%0d transaction=%0d status=%s ingress=%0d executed=%0b",
      service.get_inst_id(),service.get_sequence_id(),service.get_transaction_id(),
      service.status.name(),ingress,ocp_check_executed()), UVM_LOW)
  endfunction

  function void ocp_check_identity(svt_usb_link_service service);
    bit matched;
    matched = 0;
    if (service != null)
      foreach (issued[i])
        if (service.get_sequence_id() == issued[i].get_sequence_id() &&
            service.get_transaction_id() == issued[i].get_transaction_id()) matched = 1;
    if (service == null || !matched ||
        service.get_sequence_id() != get_sequence_id() ||
        service.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
        service.link_20_command_type !== svt_usb_link_service::USB_20_PORT_RESET)
      `uvm_fatal("OCP_RESET_NATIVE", "Unmatched typed native reset request/response")
  endfunction

  virtual function void response_handler(uvm_sequence_item response);
    svt_usb_link_service service;
    if (!$cast(service,response))
      `uvm_fatal("OCP_RESET_NATIVE", "Reset response is not a link-service descriptor")
    ocp_check_identity(service);
    responses[service.get_transaction_id()]++;
    if (!(service.status inside {svt_sequence_item::INITIAL,svt_sequence_item::ACCEPT}))
      `uvm_fatal("OCP_RESET_NATIVE", "Unsupported native reset response status")
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "response sequence=%0d transaction=%0d count=%0d status=%s",
      service.get_sequence_id(),service.get_transaction_id(),
      responses[service.get_transaction_id()],service.status.name()), UVM_LOW)
  endfunction

  function void ocp_capture_execution(svt_usb_link_service service);
    ocp_check_identity(service);
    if (!(service.status inside {svt_sequence_item::INITIAL,svt_sequence_item::ACCEPT}))
      `uvm_fatal("OCP_RESET_NATIVE", "Unsupported native reset execution status")
    executed[service.get_transaction_id()] = 1;
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "service_in_ended instance=%0d sequence=%0d transaction=%0d status=%s ingress=%0d",
      service.get_inst_id(),service.get_sequence_id(),service.get_transaction_id(),
      service.status.name(),ingress), UVM_LOW)
  endfunction

  function bit ocp_check_executed();
    if (issued.size() == 0) return 0;
    foreach (issued[i])
      if (!executed.exists(issued[i].get_transaction_id()) ||
          !executed[issued[i].get_transaction_id()]) return 0;
    return 1;
  endfunction

  task body();
    // Default no-op prerequisites avoid an unrelated link transition.
    enable_rand_delay = 0;
    enable_rand_prereq = 0;
    super.body();
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "stock_body_returned issued=%0d ingress=%0d executed=%0b release_requested=%0b",
      issued.size(),ingress,ocp_check_executed(),release_requested), UVM_LOW)
    wait (release_requested);
    if (!ocp_check_executed())
      `uvm_fatal("OCP_RESET_NATIVE", "Issuer release preceded actual native reset execution")
    foreach (issued[i])
      if (!responses.exists(issued[i].get_transaction_id()) ||
          responses[issued[i].get_transaction_id()] == 0)
        `uvm_fatal("OCP_RESET_NATIVE", "Executed native reset has no captured routed response")
    finished = 1;
  endtask
endclass
