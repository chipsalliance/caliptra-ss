// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_ep0_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_ep0_host_seq)
  usb_ocp_fifo_backpressure_ep0_checker fifo_checker;
  usb_ocp_base_ep0_peer_seq peer;
  svt_usb_transfer replacement_request;
  string variant = "partial";
  bit replacing;
  bit blocked_request_started;
  bit image_prepared;

  function new(string name = "usb_ocp_fifo_backpressure_ep0_host_seq");
    super.new(name);
  endfunction

  virtual function int ocp_configure_control_priority(int device);
    return (device == 1) ? 0 : -1;
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    int exact_words;
    int requested;
    void'($value$plusargs("usb_ocp_fifo_ep0_variant=%s",variant));
    if (!(variant inside {"capacity_plus_one","exact","partial"}) ||
        fifo_depth < 64 || fifo_depth%64 != 0 || fifo_depth >= 1024)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Variant/geometry cannot support full capacity and the fixed 64-DWORD DMA batch contract")
    exact_words = ((fifo_depth/64)+1)*64;
    if (exact_words < 128) exact_words = 128;
    case (variant)
      "capacity_plus_one": words = int'(fifo_depth)+1;
      "exact": words = exact_words;
      "partial": words = exact_words+5;
    endcase
    requested = words;
    if ($value$plusargs("usb_ocp_image_words=%d",requested)) words = requested;
    if (words <= fifo_depth || words > 1024 ||
        (variant == "capacity_plus_one" && words != fifo_depth+1) ||
        (variant == "exact" && (words < 128 || words%64 != 0)) ||
        (variant == "partial" && (words <= 128 || words%64 == 0)))
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Image override must exceed capacity and preserve selected batch/tail variant")
    `uvm_info("OCP_FIFO_EP0_VARIANT", $sformatf(
      "variant=%s image_words=%0d capacity_words=%0d final_batch_words=%0d final_burst_words=%0d",
      variant,words,fifo_depth,(words%64 == 0) ? 64 : words%64,
      (words%16 == 0) ? 16 : words%16), UVM_NONE)
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    bytes_t image_bytes;
    if (!image_prepared) begin
      if (fifo_checker == null || fifo_checker.model.fifo_depth_words != fifo_depth ||
          fifo_checker.model.fifo_max_words != fifo_max || fifo_checker.model.max_write != max_write ||
          fifo_checker.model.image_words != words)
        `uvm_fatal("OCP_FIFO_EP0_GUARD", "Host discovery/image differs from passive native control context")
      foreach (image[i]) image_bytes.push_back(image[i]);
      fifo_checker.ocp_configure_experiment(image_bytes);
      image_prepared = 1;
    end
    // Keep randomized contents/chunks, but land exactly on full advertised
    // capacity. The following one-DWORD request is the capacity+1 probe.
    if (offset < fifo_depth && chunk_words > fifo_depth-offset)
      chunk_words = fifo_depth-offset;
    if (offset == fifo_depth && !blocked_request_started) chunk_words = 1;
    // Do not straddle the inherited actor's published 64-DWORD batches.
    if (chunk_words > 64-(offset%64)) chunk_words = 64-(offset%64);
    if (chunk_words <= 0 || chunk_words > chunk_limit || offset+chunk_words > words)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Invalid legal randomized write chunk")
  endfunction

  task ocp_do_check_empty_batch();
    bytes_t data;
    bit drained;
    drained = 0;
    fork
      begin
        fork
          begin
            wait (fifo_checker.model.returned_bytes == fifo_checker.model.accepted_bytes &&
                  fifo_checker.model.compared_bytes == fifo_checker.model.accepted_bytes &&
                  ocp_cfg.recovery_vif.payload_available === 1'b0);
            drained = 1;
          end
          begin #(ocp_cfg.control_transfer_timeout); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!drained)
      `uvm_fatal("OCP_FIFO_EP0_WAIT", $sformatf(
        "Real batch drain/deassertion timeout: accepted=%0d returned=%0d compared=%0d actual_DMA=%0d; final image/activation/clear/actor/checker obligations remain",
        fifo_checker.model.accepted_bytes,fifo_checker.model.returned_bytes,
        fifo_checker.model.compared_bytes,fifo_checker.actual_dma_bytes))
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
    if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS || data[0] !== OCP_IFS_EMPTY_MASK)
      `uvm_fatal("OCP_FIFO_EP0_RESUBMIT", "Legal next batch requires real FIFO empty status")
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    bytes_t data;
    bit full;
    if (offset == fifo_depth && !blocked_request_started) begin
      ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
      if (!fifo_checker.full_prefix_seen || data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS ||
          data[0] !== OCP_IFS_FULL_MASK)
        `uvm_fatal("OCP_FIFO_EP0_CAPACITY", "Full advertised capacity was not accepted and reported full")
      full = 0;
      fork
        begin
          fork
            begin wait (fifo_checker.full_status_seen); full = 1; end
            begin #(fifo_checker.witness_timeout); end
          join_any
          disable fork;
        end
      join
      if (!full)
        `uvm_fatal("OCP_FIFO_EP0_WAIT", "Full status response lacks passive native/monitor cross-check")
    end else if (fifo_checker.dma_released && (offset%64 == 0 || offset == words))
      ocp_do_check_empty_batch();
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    svt_usb_protocol_service_abort_current_transfer_sequence abort_seq;
    usb_ocp_fifo_backpressure_ep0_peer_seq checked_peer;
    bit blocked;
    if (!replacing || device != 1) return;
    replacement_request = tr;
    blocked = 0;
    // Submission or a host pause cannot satisfy this barrier. The passive
    // checker must see a real DATA-stage OUT/NAK or legal HS PING/NAK.
    fork
      begin
        fork
          begin wait (fifo_checker.blocked_seen); blocked = 1; end
          begin #(fifo_checker.witness_timeout); end
        join_any
        disable fork;
      end
    join
    if (!blocked)
      `uvm_fatal("OCP_FIFO_EP0_WAIT", $sformatf(
        "No native full/blocked witness: accepted=%0d returned=%0d full=%0b hold=%0b active=%0b; no overlap credit",
        fifo_checker.model.accepted_bytes,fifo_checker.model.returned_bytes,fifo_checker.full_status_seen,
        fifo_checker.dma_hold_entered,fifo_checker.model.control[1].active))
    // Existing verified clean CMD abort is not replacement evidence. The
    // ordinary peer must subsequently put an ACKed new SETUP on this device.
    abort_seq = svt_usb_protocol_service_abort_current_transfer_sequence::type_id::create("abort_seq");
    abort_seq.dev_add = usb_cfg.remote_device_cfg[1].device_address;
    abort_seq.ep_number = 0;
    abort_seq.dir_seq = svt_usb_types::OUT;
    abort_seq.force_immd_abrt = 0;
    abort_seq.start(p_sequencer.prot_service_sequencer);
    checked_peer = usb_ocp_fifo_backpressure_ep0_peer_seq::type_id::create("replacement_peer");
    checked_peer.fifo_checker = fifo_checker;
    peer = checked_peer;
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
    wait (fifo_checker.model.checked_replacement_valid[1]);
    if (fifo_checker.model.checked_replacement_serial[1] != observed.transfer_serial)
      `uvm_fatal("OCP_FIFO_EP0_RETIRE", "Retired native prefix belongs to a different transfer")
    prefix = fifo_checker.model.checked_replacement_bytes[1];
    fifo_checker.model.checked_replacement_valid[1] = 0;
  endtask

  virtual task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
      logic [15:0] value, logic [15:0] index, logic [15:0] length,
      bytes_t write_data, output bytes_t read_data, input bit expect_replacement = 0,
      input bit expect_protocol_stall = 0);
    bytes_t accepted;
    if (expect_replacement || expect_protocol_stall)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Nested replacement/STALL is not owned by the FIFO EP0 row")
    if (device != 1 || bm !== 8'h21 || request !== OCP_BREQUEST_XFER ||
        value !== 16'(OCP_CMD_INDIRECT_FIFO_DATA) || !fifo_checker.full_status_seen ||
        blocked_request_started) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      return;
    end
    if (length != 4)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Blocked request must target capacity+1 DWORD")
    blocked_request_started = 1;
    replacing = 1;
    super.ocp_do_check_control(device,bm,request,value,index,length,write_data,accepted,1);
    replacing = 0;
    if (accepted.size() != 0 || peer == null || !peer.completed)
      `uvm_fatal("OCP_FIFO_EP0_RETIRE", "Blocked capacity+1 request accepted bytes or lacks native/peer retirement")
    fifo_checker.ocp_check_proof_barrier(
      usb_ocp_fifo_backpressure_ep0_checker::RELEASE_PROOF);
    fifo_checker.ocp_check_release_dma();
    ocp_do_check_empty_batch();
    // USB 5.5.5: old operation was replaced. OCP 8.2.5/9.2: submit a new
    // legal command containing only its unaccepted suffix, never replay the
    // previously accepted full FIFO prefix or reset the image/FIFO.
    super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
  endtask

  task body();
    resolve_host_context(1);
    if (fifo_checker == null || ocp_cfg == null || observer == null || ocp_cfg.recovery_vif == null)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Missing FIFO EP0 actor/checker context")
    ocp_cfg.control_transfer_timeout = 5ms;
    recovery_status_timeout = 5ms;
    usb_cfg.remote_device_cfg[1].endpoint_cfg[0].
      max_retry_due_to_nak_before_moving_to_next_ep = 1;
    host_agent.reconfigure(usb_cfg);
    super.body();
    if (!blocked_request_started || !fifo_checker.resubmitted_seen)
      `uvm_fatal("OCP_FIFO_EP0_INCOMPLETE", "Required capacity+1 replacement/resubmission did not execute")
  endtask
endclass
