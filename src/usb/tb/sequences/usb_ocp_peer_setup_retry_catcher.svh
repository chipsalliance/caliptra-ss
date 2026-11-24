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

class usb_ocp_peer_setup_retry_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_ocp_peer_setup_retry_catcher)
  usb_ocp_peer_setup_retry_callback control;
  localparam string EXPECTED_MESSAGE =
    "Description: Check if the received packet contains any protocol errors. - Received a packet with protocol errors -RANDOM_ERROR_GROUP:PID_CHECK_ERROR during Control Setup Stage.";

  function new(string name = "usb_ocp_peer_setup_retry_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    string native_id;
    if (control == null || !control.configured || control.checked ||
        !control.expected_error_armed || !control.injection_confirmed ||
        control.expected_errors != 0 || control.rejected_acks != 1 ||
        control.setup_tokens != 1 || control.native_transfer == null ||
        control.injected_packet == null ||
        control.injected_packet.pid_name != svt_usb_packet::ACK ||
        get_client() != control.expected_reporter)
      return THROW;
    native_id = $sformatf(
      "register_fail:PROTOCOL TRANSACTOR:IN-LINE:packet_error_check_Dev%0d_EP0",
      control.address);
    if (get_severity() != UVM_ERROR || get_id() != native_id ||
        get_message() != EXPECTED_MESSAGE)
      return THROW;
    control.expected_errors++;
    control.expected_error_armed = 0;
    set_id("OCP_SETUP_RETRY_EXPECTED_PID");
    set_message("Selected SETUP ACK receive-side PID injection observed exactly once");
    set_severity(UVM_INFO);
    set_action(UVM_DISPLAY);
    return THROW;
  endfunction
endclass
