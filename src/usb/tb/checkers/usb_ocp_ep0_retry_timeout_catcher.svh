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

class usb_ocp_ep0_retry_timeout_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_ocp_ep0_retry_timeout_catcher)
  usb_ocp_ep0_retry_control control;

  function new(string name = "usb_ocp_ep0_retry_timeout_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    string native_id;
    if (control == null || control.original == null ||
        control.kind != usb_ocp_ep0_retry_control::WRITE_RETRY ||
        !control.expected_timeout_armed || !control.loss_applied ||
        control.expected_timeout_seen || !control.write_committed_before_retry ||
        control.setup_tokens != 1 || control.loss_transaction == null ||
        control.ocp_post_loss_token_seen() ||
        control.data_tokens != control.loss_data_tokens ||
        control.data_packets != control.loss_data_packets ||
        control.data_acks != control.loss_data_acks ||
        control.loss_data_acks != 1 ||
        control.first_pid != svt_usb_packet::DATA1)
      return THROW;
    native_id = $sformatf(
      "register_fail:PROTOCOL TRANSACTOR:IN-LINE:device_response_timeout_check_Dev%0d_EP0",
      control.original.device_address);
    if (get_severity() == UVM_ERROR && get_id() == native_id) begin
      control.expected_timeout_seen = 1;
      set_message($sformatf(
        "Expected timeout after one host-side received-handshake drop; %s: %s",
        native_id,get_message()));
      set_id("OCP_EP0_RETRY_EXPECTED_TIMEOUT");
      set_severity(UVM_INFO);
      set_action(UVM_DISPLAY);
    end
    return THROW;
  endfunction
endclass
