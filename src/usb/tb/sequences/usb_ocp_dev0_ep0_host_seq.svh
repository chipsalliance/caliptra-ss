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

class usb_ocp_dev0_ep0_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_dev0_ep0_host_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_dev0_ep0_service_seq peer;
  svt_usb_transfer replacement_request;
  bit replacing;
  bit read_started;
  bit write_started;
  int unsigned accepted_before;

  function new(string name = "usb_ocp_dev0_ep0_host_seq");
    super.new(name);
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
    peer = usb_ocp_dev0_ep0_service_seq::type_id::create("replacement_peer");
    peer.ocp_cfg = ocp_cfg;
    peer.observer = observer;
    peer.expected_configuration = configuration_value[1];
    peer.expected_descriptor = device_descriptor_bytes[1];
    peer.start(p_sequencer);
  endtask

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    if (tr == replacement_request) begin
      wait (peer != null);
      wait (peer.completed);
    end
  endtask

  virtual task ocp_wait_replaced_prefix(usb_ocp_event observed, output bytes_t prefix);
    wait (scoreboard.model.checked_replacement_valid[1]);
    if (scoreboard.model.checked_replacement_serial[1] != observed.transfer_serial)
      `uvm_fatal("OCP_SUPERSESSION", "Checked prefix belongs to another monitor completion")
    prefix = scoreboard.model.checked_replacement_bytes[1];
    scoreboard.model.checked_replacement_valid[1] = 0;
  endtask

  virtual task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
                                    logic [15:0] value, logic [15:0] index,
                                    logic [15:0] length, bytes_t write_data,
                                    output bytes_t read_data, input bit expect_replacement = 0);
    bytes_t accepted;
    bytes_t remaining;
    bit selected;
    if (expect_replacement)
      `uvm_fatal("OCP_SUPERSESSION", "Nested replacement request is unsupported")
    selected = (device == 1 && request === OCP_BREQUEST_XFER &&
                ((bm === 8'ha1 && value === OCP_CMD_PROT_CAP && !read_started) ||
                 (bm === 8'h21 && value === OCP_CMD_INDIRECT_FIFO_DATA && !write_started)));
    if (!selected) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      return;
    end
    if (bm[7]) read_started = 1;
    else write_started = 1;
    accepted_before = scoreboard.model.accepted_bytes;
    replacing = 1;
    super.ocp_do_check_control(device,bm,request,value,index,length,write_data,accepted,1);
    replacing = 0;
    if (bm[7]) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      if (accepted.size() > read_data.size())
        `uvm_fatal("OCP_SUPERSESSION", "Canceled read prefix exceeds the fresh response")
      foreach (accepted[i])
        if (accepted[i] !== read_data[i])
          `uvm_fatal("OCP_SUPERSESSION", "Canceled capability prefix differs from fresh discovery")
    end else begin
      if (accepted.size() == 0 || accepted.size() > write_data.size() ||
          accepted.size()%4 != 0)
        `uvm_fatal("OCP_SUPERSESSION", "FIFO replacement lacks a legal accepted DWORD prefix")
      for (int i = accepted.size(); i < write_data.size(); i++)
        remaining.push_back(write_data[i]);
      `uvm_info("OCP_SUPERSESSION",$sformatf(
        "Resubmit only unaccepted FIFO suffix: accepted_bytes=%0d remaining_bytes=%0d",
        accepted.size(),remaining.size()),UVM_LOW)
      read_data.delete();
      if (remaining.size() != 0)
        super.ocp_do_check_control(device,bm,request,value,index,
                                  16'(remaining.size()),remaining,read_data);
      // Discharge canceled-control obligations before continuing the image.
      scoreboard.ocp_check_replacements();
      `uvm_info("OCP_SUPERSESSION_PHASE",$sformatf(
        "Checked same-EP0 replacement phase; recovery remains required: read=%0d write=%0d crosschecks=%0d",
        scoreboard.model.dev0_ep0_read_replacements,
        scoreboard.model.dev0_ep0_write_replacements,
        scoreboard.model.replacement_crosschecks),UVM_LOW)
    end
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
    if (!read_started || !write_started || peer == null || !peer.completed)
      `uvm_fatal("OCP_SUPERSESSION", "Read/write replacement stimulus did not complete")
  endtask
endclass
