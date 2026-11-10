// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_epn_host_seq extends usb_ocp_base_epn_overlap_host_seq;
  `uvm_object_utils(usb_ocp_fifo_backpressure_epn_host_seq)
  usb_ocp_fifo_backpressure_epn_checker fifo_checker;
  string variant = "partial";
  bit image_prepared;
  bit blocked_request_started;
  svt_usb_transfer blocked_request;

  function new(string name = "usb_ocp_fifo_backpressure_epn_host_seq");
    super.new(name);
  endfunction

  virtual function int ocp_configure_control_priority(int device);
    return (device == 1) ? 0 : -1;
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    int exact_words;
    int requested;
    void'($value$plusargs("usb_ocp_fifo_epn_variant=%s",variant));
    if (!(variant inside {"capacity_plus_one","exact","partial"}) ||
        fifo_depth < 64 || fifo_depth%64 != 0 || fifo_depth >= 1024)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Selected geometry cannot exercise full capacity with fixed 64-DWORD DMA batches")
    exact_words = ((fifo_depth/64)+1)*64;
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
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Image override must exceed capacity and preserve selected batch/tail geometry")
    `uvm_info("OCP_FIFO_EPN_VARIANT",$sformatf(
      "variant=%s image_words=%0d capacity_words=%0d final_batch_words=%0d final_burst_words=%0d",
      variant,words,fifo_depth,(words%64 == 0) ? 64 : words%64,
      (words%16 == 0) ? 16 : words%16),UVM_NONE)
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    bytes_t image_bytes;
    if (!image_prepared) begin
      if (fifo_checker.model.fifo_depth_words != fifo_depth ||
          fifo_checker.model.fifo_max_words != fifo_max ||
          fifo_checker.model.max_write != max_write || fifo_checker.model.image_words != words)
        `uvm_fatal("OCP_FIFO_EPN_GUARD", "Host discovery/image differs from passive control context")
      foreach (image[i]) image_bytes.push_back(image[i]);
      fifo_checker.ocp_configure_experiment(image_bytes);
      image_prepared = 1;
    end
    // OCP 8.2.5/9.2: runtime limits, contiguous DWORDs, full usable depth.
    // Preserve randomized legal chunks but do not straddle DMA publications.
    if (offset < fifo_depth && chunk_words > fifo_depth-offset)
      chunk_words = fifo_depth-offset;
    if (offset == fifo_depth && !blocked_request_started) chunk_words = 1;
    if (chunk_words > 64-(offset%64)) chunk_words = 64-(offset%64);
    if (chunk_words <= 0 || chunk_words > chunk_limit || offset+chunk_words > words)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Invalid randomized legal write chunk")
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
      `uvm_fatal("OCP_FIFO_EPN_WAIT",$sformatf(
        "Real batch drain/deassertion timeout: accepted=%0d returned=%0d compared=%0d actual_DMA=%0d; image/activation/clear/actor/checker obligations retained",
        fifo_checker.model.accepted_bytes,fifo_checker.model.returned_bytes,
        fifo_checker.model.compared_bytes,fifo_checker.actual_dma_bytes))
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
    if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS || data[0] !== OCP_IFS_EMPTY_MASK)
      `uvm_fatal("OCP_FIFO_EPN_DMA", "Next batch requires real FIFO empty status")
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    bytes_t data;
    bit ready;
    if (offset == fifo_depth && !blocked_request_started) begin
      ready = 0;
      fork
        begin
          fork
            begin
              wait (fifo_checker.full_prefix_seen && fifo_checker.dma_hold_entered);
              ready = 1;
            end
            begin #(fifo_checker.witness_timeout); end
          join_any
          disable fork;
        end
      join
      if (!ready)
        `uvm_fatal("OCP_FIFO_EPN_WAIT", "Full prefix/readiness hold lacks consumed passive proof")
      ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
      if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS || data[0] !== OCP_IFS_FULL_MASK)
        `uvm_fatal("OCP_FIFO_EPN_CAPACITY", "Full advertised capacity was not reported full")
      ready = 0;
      fork
        begin
          fork
            begin wait (fifo_checker.full_status_seen); ready = 1; end
            begin #(fifo_checker.witness_timeout); end
          join_any
          disable fork;
        end
      join
      if (!ready)
        `uvm_fatal("OCP_FIFO_EPN_WAIT", "Full FIFO_STATUS lacks consumed native/packet cross-check")
    end else if (fifo_checker.dma_released && (offset%64 == 0 || offset == words))
      ocp_do_check_empty_batch();
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    bit done;
    if (device == 1 && tr.setup_data_w_value == OCP_CMD_PROT_CAP && !read_started) begin
      // Earlier read-phase service is retained, but earns no held-full credit.
      super.ocp_do_control_interleave(tr,device);
      return;
    end
    if (device != 1 || tr.setup_data_w_value != OCP_CMD_INDIRECT_FIFO_DATA ||
        !fifo_checker.full_status_seen || blocked_request_started) return;
    if (tr.setup_data_w_length != 4 || write_started)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Required capacity+1 command must be the unique EPN write-phase owner")
    blocked_request_started = 1;
    write_started = 1;
    blocked_request = tr;
    done = 0;
    fork
      begin
        fork
          begin
            wait (fifo_checker.blocked_seen);
            fifo_checker.ocp_check_held_window();
            if (tr.device_address !== fifo_checker.blocked_address ||
                tr.setup_data_brequest !== fifo_checker.blocked_setup[1] ||
                tr.setup_data_w_index !==
                  {fifo_checker.blocked_setup[5],fifo_checker.blocked_setup[4]})
              `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "Blocked actual differs from sole submitted OCP command")
            // No scheduler pause/abort/replacement: full FIFO itself blocks
            // the original EP0 while the ordinary native scheduler serves EPN.
            ocp_do_check_epn_pair(tr,1);
            fifo_checker.ocp_check_proof_barrier();
            fifo_checker.ocp_check_release_dma();
            done = 1;
          end
          begin #4ms; end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!done)
      `uvm_fatal("OCP_FIFO_EPN_WAIT",$sformatf(
        "Blocked/EPN/proof timeout: full=%0b hold=%0b blocked=%0b joined=%0b consumed=%0b accepted=%0d DMA=%0d; no forced progress",
        fifo_checker.full_status_seen,fifo_checker.dma_hold_entered,
        fifo_checker.blocked_seen,fifo_checker.overlap_joined,fifo_checker.proof_consumed,
        fifo_checker.model.accepted_bytes,fifo_checker.actual_dma_bytes))
  endtask

  virtual task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
      logic [15:0] value, logic [15:0] index, logic [15:0] length,
      bytes_t write_data, output bytes_t read_data, input bit expect_replacement = 0,
      input bit expect_protocol_stall = 0);
    bit blocked_operation;
    if (expect_replacement || expect_protocol_stall || require_replacement)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "FIFO EPN never owns replacement or terminal STALL")
    blocked_operation = device == 1 && bm === 8'h21 && request === OCP_BREQUEST_XFER &&
      value === 16'(OCP_CMD_INDIRECT_FIFO_DATA) &&
      fifo_checker.full_status_seen && !blocked_request_started;
    super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
    // Before allowing the next SETUP, join original native/STATUS/retry and
    // actual DMA comparisons, even if monitor and AXI callbacks reverse order.
    if (blocked_operation) fifo_checker.ocp_check_proof_barrier(1);
  endtask

  task body();
    if (fifo_checker == null || scoreboard != fifo_checker || ocp_cfg == null ||
        ocp_cfg.recovery_vif == null || both_epn_devices || require_replacement)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Missing or foreign owned FIFO EPN context")
    recovery_status_timeout = 5ms;
    super.body();
    if (!blocked_request_started || !fifo_checker.retry_joined)
      `uvm_fatal("OCP_FIFO_EPN_INCOMPLETE", "Required naturally blocked/retried command did not complete")
  endtask
endclass
