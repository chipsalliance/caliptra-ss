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

class usb_ocp_dev1_ep0_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_dev1_ep0_host_seq)
  localparam int unsigned OCP_SCHEDULE_PRIORITY = 0;
  usb_ocp_dev1_ep0_service_seq peer;
  svt_usb_transfer peer_request;
  bit read_started;
  bit write_started;

  function new(string name = "usb_ocp_dev1_ep0_host_seq");
    super.new(name);
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    if (device == 1) tr.schedule_priority = OCP_SCHEDULE_PRIORITY;
  endfunction

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    int kind;
    kind = 0;
    if (device == 1 && tr.setup_data_w_value == OCP_CMD_PROT_CAP && !read_started)
      kind = 1;
    if (device == 1 && tr.setup_data_w_value == OCP_CMD_INDIRECT_FIFO_DATA && !write_started)
      kind = 2;
    if (kind == 0) return;
    if (kind == 1) read_started = 1;
    else write_started = 1;
    peer_request = tr;
    peer = usb_ocp_dev1_ep0_service_seq::type_id::create("peer");
    peer.ocp_cfg = ocp_cfg;
    peer.observer = observer;
    peer.expected_configuration = configuration_value[2];
    peer.expected_descriptor = device_descriptor_bytes[2];
    // The native stage notification arms a separate UVM sequence. Wire
    // callbacks, not this fork or notification, must prove actual overlap.
    tr.wait_for_control_transfer_stage(svt_usb_transfer::SETUP_STAGE,1);
    `uvm_info("OCP_INTERLEAVE",$sformatf("Dev1 peer after OCP SETUP cmd=%02h",
              tr.setup_data_w_value),UVM_LOW)
    peer.start(p_sequencer);
  endtask

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    if (tr != peer_request) return;
    // Delay only host-side consumption of a completed observation. This
    // exercises reversed waiter order without modifying wire/DUT progress.
    wait (peer.completed);
  endtask

  task body();
    resolve_host_context(1);
    ocp_cfg.control_transfer_timeout = 5ms;
    for (int device = 1; device < 3; device++)
      usb_cfg.remote_device_cfg[device].endpoint_cfg[0].
        max_retry_due_to_nak_before_moving_to_next_ep = 1;
    host_agent.reconfigure(usb_cfg);
    super.body();
    if (!read_started || !write_started || peer == null || !peer.completed)
      `uvm_fatal("OCP_INTERLEAVE", "Read/write peer stimulus did not complete")
  endtask
endclass
