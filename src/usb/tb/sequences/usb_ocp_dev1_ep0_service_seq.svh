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

class usb_ocp_dev1_ep0_service_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_dev1_ep0_service_seq)
  localparam int unsigned PEER_SCHEDULE_PRIORITY = 99;
  logic [7:0] expected_configuration;
  bytes_t expected_descriptor;
  usb_ocp_peer_setup_retry_callback setup_retry;

  function new(string name = "usb_ocp_dev1_ep0_service_seq");
    super.new(name);
  endfunction

  // Native schedule_priority favors higher values; 99 remains within the
  // VIP's reasonable <100 constraint. Packet checks still require overlap.
  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    tr.schedule_priority = PEER_SCHEDULE_PRIORITY;
    if (setup_retry != null) begin
      if (!setup_retry.configured) begin
        if (device != 2 || tr.setup_data_brequest != svt_usb_types::GET_CONFIGURATION)
          `uvm_fatal("OCP_SETUP_RETRY", "Retry must target the first peer GET_CONFIGURATION")
        setup_retry.ocp_configure_retry(tr.device_address);
      end else if (!setup_retry.checked) begin
        // The next request is prepared only after the first native/payload check.
        setup_retry.ocp_check_retry();
      end
    end
  endfunction

  task body();
    resolve_host_context(1);
    ocp_do_check_standard_controls(2,expected_configuration,expected_descriptor);
    if (setup_retry != null && !setup_retry.checked)
      `uvm_fatal("OCP_SETUP_RETRY", "Peer replay check did not execute")
    completed = 1;
  endtask
endclass
