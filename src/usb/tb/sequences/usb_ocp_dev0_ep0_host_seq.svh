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

class usb_ocp_dev0_ep0_host_seq extends usb_ocp_base_replacement_host_seq;
  `uvm_object_utils(usb_ocp_dev0_ep0_host_seq)

  function new(string name = "usb_ocp_dev0_ep0_host_seq");
    super.new(name);
    require_replacement = 1;
  endfunction

  virtual function usb_ocp_base_ep0_peer_seq ocp_prepare_replacement_peer();
    return usb_ocp_dev0_ep0_service_seq::type_id::create("replacement_peer");
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    if (device == 1) tr.schedule_priority = 0;
  endfunction

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    svt_usb_protocol_service_abort_current_transfer_sequence abort_seq;
    if (!replacing || device != 1) return;
    peer = null;
    replacement_request = tr;
    tr.wait_for_control_transfer_stage(svt_usb_transfer::SETUP_STAGE,1);
    if (!tr.setup_data_bmrequesttype_dir) begin
      // ACK/NYET observation can lag the native scheduler's next STATUS.
      // Request a clean break while the actual OUT transaction is underway;
      // its independently checked accepted prefix must still survive.
      wait (scoreboard.model.token != null &&
            scoreboard.model.token.pid === svt_usb_packet::OUT &&
            scoreboard.model.token.address === tr.device_address &&
            scoreboard.model.token.endpoint === 0);
    end
    // The native CMD requests a clean abort, not a replacement on the wire.
    // The subsequent standard transfer must supply an ACKed new SETUP.
    abort_seq = svt_usb_protocol_service_abort_current_transfer_sequence::type_id::create("abort_seq");
    abort_seq.dev_add = usb_cfg.remote_device_cfg[1].device_address;
    abort_seq.ep_number = 0;
    abort_seq.dir_seq = svt_usb_types::OUT;
    abort_seq.force_immd_abrt = 0;
    abort_seq.start(p_sequencer.prot_service_sequencer);
    `uvm_info("OCP_SUPERSESSION",$sformatf(
      "Native clean-abort requested cmd=%02h accepted_at_request=%0d",
      tr.setup_data_w_value,
      scoreboard.model.accepted_bytes-accepted_before),UVM_LOW)
    ocp_do_check_standard_replacement(tr);
  endtask

  task body();
    resolve_host_context(1);
    if (ocp_cfg == null || observer == null || scoreboard == null)
      `uvm_fatal("OCP_SUPERSESSION", "Missing mandatory replacement checker")
    ocp_cfg.control_transfer_timeout = 5ms;
    recovery_status_timeout = 5ms;
    usb_cfg.remote_device_cfg[1].endpoint_cfg[0].
      max_retry_due_to_nak_before_moving_to_next_ep = 1;
    host_agent.reconfigure(usb_cfg);
    super.body();
    if (!replacement_read_started || !replacement_write_started || peer == null || !peer.completed)
      `uvm_fatal("OCP_SUPERSESSION", "Read/write replacement stimulus did not complete")
  endtask
endclass
