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

class usb_ocp_suspend_link_callback extends svt_usb_link_callback;
  `uvm_object_utils(usb_ocp_suspend_link_callback)
  usb_ocp_suspend_service_record active_record;
  svt_usb_status native_status;

  function new(string name = "usb_ocp_suspend_link_callback");
    super.new(name);
  endfunction

  virtual function void post_link_service_in_port_get(svt_usb_link component,
      int chan_id, svt_usb_link_service service, ref bit drop);
    if (active_record == null) return;
    if (service == null || native_status == null || service.cfg == null ||
        service.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
        service.link_20_command_type !== svt_usb_link_service::USB_20_CLEAR_PORT_SUSPEND ||
        active_record.operation != usb_ocp_suspend_service_record::LINK_CLEAR)
      `uvm_fatal("OCP_L2_SERVICE", "Mismatched received link service in serial CLEAR window")
    active_record.ingress_count++;
    `uvm_info("OCP_L2_INGRESS", $sformatf(
      "component=%s channel=%0d count=%0d instance=%0d sequence=%0d transaction=%0d drop=%0b cfg=%0d prereq=%s prereq_delay=%g service_delay=%g link=%s power=%s time=%0t",
      component.get_full_name(),chan_id,active_record.ingress_count,
      service.get_inst_id(),service.get_sequence_id(),service.get_transaction_id(),
      drop,service.cfg.get_inst_id(),service.prereq_link_20_state.name(),
      service.prereq_link_20_delay,service.link_service_delay,
      native_status.link_usb_20_state.name(),native_status.link_usb_20_power_state.name(),
      $realtime), UVM_LOW)
  endfunction

  virtual function void service_in_ended(svt_usb_link component,
      svt_usb_link_service service);
    if (active_record == null) return;
    if (service == null ||
        service.service_type !== svt_usb_link_service::LINK_20_PORT_COMMAND ||
        service.link_20_command_type !== svt_usb_link_service::USB_20_CLEAR_PORT_SUSPEND ||
        active_record.operation != usb_ocp_suspend_service_record::LINK_CLEAR)
      `uvm_fatal("OCP_L2_SERVICE", "Mismatched executed link service in serial CLEAR window")
    active_record.ocp_capture_end(service,service.status);
  endfunction
endclass
