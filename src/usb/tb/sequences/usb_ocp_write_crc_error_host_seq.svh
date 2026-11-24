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

// chipsalliance/usb2#72: one INDIRECT_FIFO_DATA write carries a corrupted
// DATA1 CRC16. USB 2.0 8.7.2 requires no handshake and no data acceptance;
// the host then retries the same DATA1. OCP Recovery 1.1 9.2 requires the
// device to report protocol error 04h (general CRC error) in DEVICE_STATUS,
// cleared on read.
class usb_ocp_write_crc_error_host_seq extends usb_ocp_protocol_error_host_seq;
  `uvm_object_utils(usb_ocp_write_crc_error_host_seq)
  localparam int unsigned MIN_IMAGE_WORDS = 2;
  usb_ocp_write_crc_callback injection;
  bit exercised;
  bit saved_disable_tend_check;
  logic [31:0] base_wr;
  logic [31:0] base_rd;

  function new(string name = "usb_ocp_write_crc_error_host_seq");
    super.new(name);
  endfunction

  // A second image DWORD after the corrupted write makes any duplicate or
  // corrupted commit visible to the existing image/drain checks.
  virtual function void ocp_configure_image_words(ref int words);
    if (words < MIN_IMAGE_WORDS) words = MIN_IMAGE_WORDS;
    if (max_write < 4 || fifo_max < 1 || fifo_depth < MIN_IMAGE_WORDS)
      `uvm_fatal("OCP_CRC_SCOPE", "Discovered geometry cannot isolate a one-DWORD corrupted write")
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    if (offset == 0) chunk_words = 1;
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    if (device != 1 || !error_model.armed || error_model.finished ||
        injection.target != null ||
        tr.setup_data_w_value != OCP_CMD_INDIRECT_FIFO_DATA ||
        tr.setup_data_bmrequesttype_dir != svt_usb_types::HOST_TO_DEVICE)
      return;
    injection.target = tr;
  endfunction

  virtual task ocp_do_check_pre_image();
    bytes_t data;
    bytes_t payload;
    if (exercised) `uvm_fatal("OCP_CRC_SCOPE", "Duplicate corrupted-write experiment")
    // The scoreboard rejects any nonzero protocol error before arming.
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
    ocp_do_check_snapshot();
    base_wr = error_model.snapshot["INDIRECT_FIFO_STATUS_1"];
    base_rd = error_model.snapshot["INDIRECT_FIFO_STATUS_2"];
    if (base_wr !== base_rd || scoreboard.model.accepted_bytes != 0)
      `uvm_fatal("OCP_CRC_PREREQUISITE", "Corrupted write requires an empty FIFO with no accepted image bytes")
    for (int i = 0; i < 4; i++) payload.push_back(image[i]);
    error_model.ocp_configure_request(usb_ocp_protocol_error_model::WRITE_CRC,
      usb_cfg.remote_device_cfg[1].device_address,interface_number,
      OCP_CMD_INDIRECT_FIFO_DATA,scoreboard.model.control[1].epoch,
      scoreboard.model.control[1].generation+1,observer.next_order,payload);
    // The missing handshake is an expected host-side timeout, not a
    // turnaround violation.
    saved_disable_tend_check = usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout;
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
    host_agent.reconfigure(usb_cfg);
    `uvm_info("OCP_CRC_PROBE", $sformatf(
      "Armed one-shot CRC16 corruption on first INDIRECT_FIFO_DATA write: wr=%0d rd=%0d",
      base_wr,base_rd),UVM_NONE)
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    if (offset != 1 || exercised) return;
    if (!injection.injected)
      `uvm_fatal("OCP_CRC_INJECTION", "Selected write completed without CRC16 corruption")
    usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = saved_disable_tend_check;
    host_agent.reconfigure(usb_cfg);
    // Normal drain is held, so exactly the retried DWORD must be committed.
    ocp_do_check_snapshot();
    if (error_model.snapshot["INDIRECT_FIFO_STATUS_1"] !== base_wr+1 ||
        error_model.snapshot["INDIRECT_FIFO_STATUS_2"] !== base_rd)
      `uvm_fatal("OCP_CRC_COMMIT", $sformatf(
        "Corrupted write plus clean retry must commit one DWORD: wr=%0d->%0d rd=%0d->%0d",
        base_wr,error_model.snapshot["INDIRECT_FIFO_STATUS_1"],
        base_rd,error_model.snapshot["INDIRECT_FIFO_STATUS_2"]))
    ocp_do_check_error_status();
    exercised = 1;
    error_model.release_dma = 1;
  endtask

  virtual task ocp_do_check_host_completion();
    super.ocp_do_check_host_completion();
    if (!exercised)
      `uvm_fatal("OCP_CRC_INCOMPLETE", "Corrupted-write experiment was never exercised")
    `uvm_info("OCP_CRC_COMPLETE", "Corrupted write retried; image/recovery/activation/drain completed",UVM_NONE)
  endtask

  task body();
    usb_ocp_write_crc_observer crc_observer;
    resolve_host_context(1);
    if (host_agent.prot == null)
      `uvm_fatal("OCP_CRC_SCOPE", "Native host protocol layer unavailable")
    if (!$cast(crc_observer,observer))
      `uvm_fatal("OCP_CRC_SCOPE", "Missing injection-aware observer")
    injection = usb_ocp_write_crc_callback::type_id::create("injection");
    crc_observer.injection = injection;
    uvm_callbacks#(svt_usb_protocol)::add(host_agent.prot,injection);
    super.body();
    uvm_callbacks#(svt_usb_protocol)::delete(host_agent.prot,injection);
  endtask
endclass
