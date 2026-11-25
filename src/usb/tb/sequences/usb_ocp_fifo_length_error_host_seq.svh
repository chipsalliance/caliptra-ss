// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_length_error_host_seq extends usb_ocp_protocol_error_host_seq;
  `uvm_object_utils(usb_ocp_fifo_length_error_host_seq)
  string profile = "overflow";
  bit exercised;

  function new(string name = "usb_ocp_fifo_length_error_host_seq");
    super.new(name);
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    words = (profile == "prefix") ? 2 : 1;
    if (max_write < 8 || fifo_max < 2 || fifo_depth < 3)
      `uvm_fatal("OCP_LENGTH_SCOPE", "Discovered geometry cannot isolate image remainder from physical space")
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    chunk_words = 1;
  endfunction

  task ocp_do_check_overflow(int unsigned image_words, int unsigned accepted_words,
                             int unsigned request_bytes);
    bytes_t response;
    bytes_t rejected = '{8'h91,8'h32,8'h73,8'h14,8'h55,8'hb6,8'hf7,8'h98};
    logic [31:0] ctrl;
    logic [31:0] words;
    logic [31:0] flags;
    logic [31:0] wr;
    logic [31:0] rd;
    bit done;
    process request_process;
    process watchdog_process;
    if (exercised) `uvm_fatal("OCP_LENGTH_SCOPE", "Duplicate image-remainder experiment")
    if (request_bytes == 0 || request_bytes % 4 != 0 || request_bytes > rejected.size() ||
        accepted_words > image_words || accepted_words > fifo_depth)
      `uvm_fatal("OCP_LENGTH_SCOPE", "Invalid FIFO length-probe geometry")
    while (rejected.size() > request_bytes) void'(rejected.pop_back());
    ocp_do_check_snapshot();
    ctrl = error_model.snapshot["INDIRECT_FIFO_CTRL_0"];
    words = error_model.snapshot["INDIRECT_FIFO_CTRL_1"];
    flags = error_model.snapshot["INDIRECT_FIFO_STATUS_0"];
    wr = error_model.snapshot["INDIRECT_FIFO_STATUS_1"];
    rd = error_model.snapshot["INDIRECT_FIFO_STATUS_2"];
    if (words !== 32'(image_words) || wr !== 32'(accepted_words) || rd !== 32'b0 ||
        scoreboard.model.accepted_bytes != accepted_words*4 ||
        scoreboard.model.returned_bytes != 0 ||
        request_bytes/4 > fifo_depth-accepted_words ||
        request_bytes/4 <= image_words-accepted_words)
      `uvm_fatal("OCP_LENGTH_PREREQUISITE", $sformatf(
        "profile=%s expected image/accepted words=%0d/%0d; observed size/wr/rd=%0d/%0d/%0d accepted/returned bytes=%0d/%0d",
        profile,image_words,accepted_words,words,wr,rd,
        scoreboard.model.accepted_bytes,scoreboard.model.returned_bytes))
    error_model.ocp_configure_request(usb_ocp_protocol_error_model::IMAGE_LENGTH,
      usb_cfg.remote_device_cfg[1].device_address,interface_number,
      OCP_CMD_INDIRECT_FIFO_DATA,scoreboard.model.control[1].epoch,
      scoreboard.model.control[1].generation+1,observer.next_order,rejected);
    `uvm_info("OCP_LENGTH_PROBE", $sformatf(
      "profile=%s image_words=%0d accepted_bytes=%0d request_bytes=%0d physical_free_words=%0d",
      profile,words,scoreboard.model.accepted_bytes,rejected.size(),fifo_depth-wr),UVM_NONE)
    done = 0;
    fork
      begin
        fork
          begin
            request_process = process::self();
            ocp_do_check_control(1,8'h21,OCP_BREQUEST_XFER,OCP_CMD_INDIRECT_FIFO_DATA,
              {8'b0,interface_number},16'(rejected.size()),rejected,response,0,1);
            done = 1;
          end
          begin
            watchdog_process = process::self();
            #50us;
            ocp_do_check_snapshot();
            ocp_check_snapshot_unchanged(ctrl,words,flags,wr,rd);
            if (scoreboard.model.accepted_bytes != accepted_words*4 ||
                scoreboard.model.returned_bytes != 0)
              `uvm_fatal("OCP_LENGTH_EVIDENCE", "Rejected write changed the accepted or returned byte count")
            if (error_model.setup_seen && !error_model.stall_seen &&
                error_model.data_naks != 0)
              `uvm_fatal("OCP_LENGTH_REJECT", $sformatf(
                "Image-remainder overflow NAKed instead of DATA STALL/code03: profile=%s NAKs=%0d accepted_bytes=%0d firmware_error=%02h; native/recovery/read-clear remain unreached",
                profile,error_model.data_naks,scoreboard.model.accepted_bytes,
                error_model.snapshot["DEVICE_STATUS_0"][15:8]))
            `uvm_fatal("OCP_LENGTH_EVIDENCE", "Missing bounded SETUP/DATA STALL/native evidence for overflow")
          end
        join_any
        if (!done && request_process != null &&
            request_process.status() != process::FINISHED) request_process.kill();
        if (watchdog_process != null &&
            watchdog_process.status() != process::FINISHED) watchdog_process.kill();
      end
    join
    if (!done) `uvm_fatal("OCP_LENGTH_EVIDENCE", "Overflow request did not retire")
    ocp_do_check_snapshot();
    ocp_check_snapshot_unchanged(ctrl,words,flags,wr,rd);
    ocp_do_check_error_status();
    exercised = 1;
    if (profile != "zero") error_model.release_dma = 1;
  endtask

  virtual task ocp_do_check_pre_image();
    if (profile == "overflow") ocp_do_check_overflow(1,0,8);
    if (profile == "zero") begin
      ocp_do_check_fifo_control(cms,0);
      ocp_do_check_overflow(0,0,4);
      ocp_do_check_fifo_control(cms,1);
      error_model.release_dma = 1;
    end
    if (profile == "exact") error_model.release_dma = 1;
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    if (profile == "prefix" && offset == 1) ocp_do_check_overflow(2,1,8);
    if (profile == "complete" && offset == words) ocp_do_check_overflow(words,words,4);
  endtask

  virtual task ocp_do_check_host_completion();
    super.ocp_do_check_host_completion();
    if (profile != "exact" && !exercised)
      `uvm_fatal("OCP_LENGTH_INCOMPLETE", "Selected overflow was never exercised")
    `uvm_info("OCP_LENGTH_COMPLETE", $sformatf(
      "profile=%s image/recovery/activation/drain completed",profile),UVM_NONE)
  endtask

  task body();
    void'($value$plusargs("usb_ocp_length_profile=%s",profile));
    if (!(profile inside {"overflow","exact","prefix","zero","complete"}))
      `uvm_fatal("OCP_LENGTH_SCOPE", "Select overflow/exact/prefix/zero/complete image-remainder profile")
    super.body();
  endtask
endclass
