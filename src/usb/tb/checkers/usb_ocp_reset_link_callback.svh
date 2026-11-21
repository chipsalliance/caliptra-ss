// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_link_callback extends svt_usb_link_callback;
  `uvm_object_utils(usb_ocp_reset_link_callback)
  usb_ocp_reset_service_seq issuer;

  function new(string name = "usb_ocp_reset_link_callback");
    super.new(name);
  endfunction

  virtual function void post_link_service_in_port_get(svt_usb_link component,
      int chan_id, svt_usb_link_service service, ref bit drop);
    if (issuer == null) return;
    issuer.ocp_check_identity(service);
    issuer.ingress++;
    `uvm_info("OCP_RESET_NATIVE", $sformatf(
      "ingress channel=%0d instance=%0d sequence=%0d transaction=%0d count=%0d drop=%0b",
      chan_id,service.get_inst_id(),service.get_sequence_id(),
      service.get_transaction_id(),issuer.ingress,drop), UVM_LOW)
    if (drop)
      `uvm_fatal("OCP_RESET_NATIVE", "Native reset request was dropped")
  endfunction

  virtual function void service_in_ended(svt_usb_link component,
      svt_usb_link_service service);
    if (issuer != null) issuer.ocp_capture_execution(service);
  endfunction
endclass
