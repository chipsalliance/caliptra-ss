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

  function new(string name = "usb_ocp_dev1_ep0_service_seq");
    super.new(name);
  endfunction

  // Native schedule_priority favors higher values; 99 remains within the
  // VIP's reasonable <100 constraint. Packet checks still require overlap.
  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    tr.schedule_priority = PEER_SCHEDULE_PRIORITY;
  endfunction

  task body();
    bytes_t data;
    bytes_t empty;
    resolve_host_context(1);
    // USB 2.0 9.4.2/9.4.3: compare with this device's earlier USB discovery,
    // not another device's data or an RTL/RDL expected-value oracle.
    ocp_do_check_control(2,8'h80,svt_usb_types::GET_CONFIGURATION,0,0,1,empty,data);
    if (data.size() != 1 || data[0] !== expected_configuration)
      `uvm_fatal("OCP_PEER", "Dev1 GET_CONFIGURATION differs from prior discovery")
    ocp_do_check_control(2,8'h80,svt_usb_types::GET_DESCRIPTOR,16'h0100,0,18,empty,data);
    if (data.size() != expected_descriptor.size())
      `uvm_fatal("OCP_PEER", "Dev1 device descriptor length changed during OCP")
    foreach (data[i])
      if (data[i] !== expected_descriptor[i])
        `uvm_fatal("OCP_PEER", "Dev1 descriptor data changed or crossed device identity")
    completed = 1;
  endtask
endclass
