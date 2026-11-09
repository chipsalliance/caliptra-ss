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

class usb_ocp_base_replacement_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_base_replacement_host_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_base_ep0_peer_seq peer;
  svt_usb_transfer replacement_request;
  bit require_replacement;
  bit zero_prefix_required;
  bit replacing;
  bit replacement_read_started;
  bit replacement_write_started;
  int unsigned accepted_before;

  function new(string name = "usb_ocp_base_replacement_host_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_ep0_peer_seq ocp_prepare_replacement_peer();
    return usb_ocp_base_ep0_peer_seq::type_id::create("replacement_peer");
  endfunction

  task ocp_do_check_standard_replacement(svt_usb_transfer tr);
    replacement_request = tr;
    peer = ocp_prepare_replacement_peer();
    if (peer == null) `uvm_fatal("OCP_SUPERSESSION", "Missing mandatory replacement peer")
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
      logic [15:0] value, logic [15:0] index, logic [15:0] length,
      bytes_t write_data, output bytes_t read_data, input bit expect_replacement = 0,
      input bit expect_protocol_stall = 0);
    bytes_t accepted;
    bytes_t remaining;
    bit selected;
    if (expect_protocol_stall)
      `uvm_fatal("OCP_STALL_GUARD", "Replacement actor does not own protocol STALL")
    if (expect_replacement)
      `uvm_fatal("OCP_SUPERSESSION", "Nested replacement request is unsupported")
    selected = require_replacement && device == 1 && request === OCP_BREQUEST_XFER &&
      ((bm === 8'ha1 && value === OCP_CMD_PROT_CAP && !replacement_read_started) ||
       (bm === 8'h21 && value === OCP_CMD_INDIRECT_FIFO_DATA && !replacement_write_started));
    if (!selected) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      return;
    end
    if (scoreboard == null)
      `uvm_fatal("OCP_SUPERSESSION", "Missing mandatory replacement checker")
    if (bm[7]) replacement_read_started = 1;
    else replacement_write_started = 1;
    accepted_before = scoreboard.model.accepted_bytes;
    replacing = 1;
    super.ocp_do_check_control(device,bm,request,value,index,length,write_data,accepted,1);
    replacing = 0;
    if (zero_prefix_required && accepted.size() != 0)
      `uvm_fatal("OCP_MIXED_STIMULUS", "Paused pre-DATA replacement unexpectedly accepted old DATA")
    if (bm[7]) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      if (accepted.size() > read_data.size())
        `uvm_fatal("OCP_SUPERSESSION", "Canceled read prefix exceeds the fresh response")
      foreach (accepted[i])
        if (accepted[i] !== read_data[i])
          `uvm_fatal("OCP_SUPERSESSION", "Canceled capability prefix differs from fresh discovery")
    end else begin
      if ((!zero_prefix_required && accepted.size() == 0) ||
          accepted.size() > write_data.size() || accepted.size()%4 != 0)
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
      scoreboard.ocp_check_replacements();
      `uvm_info("OCP_SUPERSESSION_PHASE",$sformatf(
        "Checked same-EP0 replacement phase; recovery remains required: read=%0d write=%0d crosschecks=%0d",
        scoreboard.model.dev0_ep0_read_replacements,
        scoreboard.model.dev0_ep0_write_replacements,
        scoreboard.model.replacement_crosschecks),UVM_LOW)
    end
  endtask
endclass
