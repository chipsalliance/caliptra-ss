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

class usb_ocp_dev0_ep0_service_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_dev0_ep0_service_seq)
  localparam int unsigned PEER_SCHEDULE_PRIORITY = 99;
  logic [7:0] expected_configuration;
  bytes_t expected_descriptor;

  function new(string name = "usb_ocp_dev0_ep0_service_seq");
    super.new(name);
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    tr.schedule_priority = PEER_SCHEDULE_PRIORITY;
  endfunction

  task body();
    resolve_host_context(1);
    ocp_do_check_standard_controls(1,expected_configuration,expected_descriptor);
    completed = 1;
  endtask
endclass
