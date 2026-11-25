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

// Report only the exact diagnostics attributable to the selected fault.
class usb_ocp_crc_timeout_catcher extends uvm_report_catcher;
  `uvm_object_utils(usb_ocp_crc_timeout_catcher)
  usb_ocp_write_crc_callback injection;
  uvm_report_object link_reporter;
  usb_ocp_protocol_error_model error_model;
  bit pid_report_seen;
  localparam string EXPECTED_PID_MESSAGE =
    "Description: Check if the received packet contains any protocol errors. - Received a packet with protocol errors -RANDOM_ERROR_GROUP:PID_CHECK_ERROR during a device response to a host DATA1 packet.";

  function new(string name = "usb_ocp_crc_timeout_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    string native_id;
    if (injection == null || injection.target == null || get_severity() != UVM_ERROR)
      return THROW;
    if (get_client() == injection.reporter && injection.retry_crc && injection.loss_applied &&
        injection.out_context && !injection.injected && !pid_report_seen &&
        get_id() == $sformatf("register_fail:PROTOCOL TRANSACTOR:IN-LINE:packet_error_check_Dev%0d_EP0",
                              injection.target.device_address) &&
        get_message() == EXPECTED_PID_MESSAGE) begin
      pid_report_seen = 1;
      set_id("OCP_CRC_EXPECTED_PID");
      set_severity(UVM_INFO);
      set_action(UVM_DISPLAY);
      return THROW;
    end
    if (!injection.timeout_armed || error_model == null || !error_model.bad_pending)
      return THROW;
    native_id = $sformatf(
      "register_fail:PROTOCOL TRANSACTOR:IN-LINE:device_response_timeout_check_Dev%0d_EP0",
      injection.target.device_address);
    if (get_client() == link_reporter && !injection.link_timeout_seen &&
        get_id() == "register_fail:LINK 20 TIMING CHECKS:COMMON:tend_to_end_delay_check" &&
        uvm_is_match("*Response packet not received within the expiry of End to End Delay*",
                     get_message())) begin
      injection.link_timeout_seen = 1;
    end else if (get_client() == injection.reporter && !injection.timeout_seen &&
                 get_id() == native_id) begin
      injection.timeout_seen = 1;
    end else return THROW;
    set_message($sformatf("Selected corrupt OUT attempt timed out: %s",get_message()));
    set_id("OCP_CRC_EXPECTED_TIMEOUT");
    set_severity(UVM_INFO);
    set_action(UVM_DISPLAY);
    return THROW;
  endfunction
endclass
