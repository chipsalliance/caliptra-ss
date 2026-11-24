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

class usb_ocp_ep0_retry_mcu_seq extends usb_ocp_base_mcu_seq;
  `uvm_object_utils(usb_ocp_ep0_retry_mcu_seq)
  usb_ocp_ep0_retry_host_seq host;

  function new(string name = "usb_ocp_ep0_retry_mcu_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_owned_setup(logic [7:0] request_type,
      logic [7:0] request, logic [15:0] value, logic [15:0] index,
      logic [15:0] length, output bit handled);
    bit observed;
    handled = 0;
    if (host.retry == null || host.retry.original == null ||
        !((host.nak_mode == "in" && request_type === 8'h80 &&
           request == svt_usb_types::GET_CONFIGURATION && value === 0 &&
           index === 0 && length === 1) ||
          (host.status_probe && request_type === 0 &&
           request == svt_usb_types::SET_CONFIGURATION &&
           value === host.configuration_value[1] && index === 0 && length === 0)))
      return;
    observed = 0;
    // Leave the firmware-owned response unarmed until a real IN NAK.
    fork
      begin
        fork
          begin
            wait (host.status_probe ? host.retry.status_naks != 0 : host.retry.data_naks != 0);
            observed = 1;
          end
          begin #(usb_ocp_ep0_retry_host_seq::STATUS_OBSERVATION_TIMEOUT); end
        join_any
        disable fork;
      end
    join
    if (!observed)
      `uvm_fatal("OCP_EP0_RETRY_NAK", "Firmware response hold produced no native IN NAK")
  endtask
endclass
