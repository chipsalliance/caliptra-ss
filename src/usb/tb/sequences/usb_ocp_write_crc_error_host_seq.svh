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

// USB 2.0 8.6.4 and 8.7.2: corrupt either the first OUT DATA1 (legacy
// profile), its replay after host handshake loss, or the read STATUS ZLP.
// OCP Recovery 1.1 9.2: write CRC failure reports 04h, cleared on read.
class usb_ocp_write_crc_error_host_seq extends usb_ocp_protocol_error_host_seq;
  `uvm_object_utils(usb_ocp_write_crc_error_host_seq)
  localparam int unsigned MIN_IMAGE_WORDS = 2;
  usb_ocp_write_crc_callback injection;
  usb_ocp_crc_timeout_catcher timeout_catcher;
  usb_ocp_protocol_error_model::error_kind_e crc_kind;
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
    if (crc_kind == usb_ocp_protocol_error_model::READ_STATUS_CRC) return;
    if (words < MIN_IMAGE_WORDS) words = MIN_IMAGE_WORDS;
    if (max_write < 4 || fifo_max < 1 || fifo_depth < MIN_IMAGE_WORDS)
      `uvm_fatal("OCP_CRC_SCOPE", "Discovered geometry cannot isolate a one-DWORD corrupted write")
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    if (crc_kind != usb_ocp_protocol_error_model::READ_STATUS_CRC &&
        offset == 0) chunk_words = 1;
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    logic [7:0] setup[8];
    if (device != 1 || !error_model.armed || error_model.finished ||
        injection.target != null)
      return;
    setup = '{observer.ocp_prepare_request_type(tr.setup_data_bmrequesttype_dir,
        tr.setup_data_bmrequesttype_type,tr.setup_data_bmrequesttype_recipient),
        tr.setup_data_brequest,tr.setup_data_w_value[7:0],tr.setup_data_w_value[15:8],
        tr.setup_data_w_index[7:0],tr.setup_data_w_index[15:8],
        tr.setup_data_w_length[7:0],tr.setup_data_w_length[15:8]};
    if (tr.device_address !== error_model.address || tr.endpoint_number != 0 ||
        tr.xfer_type != svt_usb_transfer::CONTROL_TRANSFER || setup !== error_model.setup)
      `uvm_fatal("OCP_CRC_SCOPE", "Native target does not match the armed CONTROL setup")
    injection.target = tr;
  endfunction

  task ocp_check_injection();
    ocp_poll_observation();
    if (!injection.injected || !injection.clean_sent ||
        !error_model.native_checked ||
        (injection.retry_crc && (!injection.loss_applied || !timeout_catcher.pid_report_seen)))
      `uvm_fatal("OCP_CRC_INJECTION", "Selected transfer lacks injection and native retry evidence")
  endtask

  task ocp_do_check_read_status_crc();
    bytes_t data;
    bytes_t zlp;
    logic [31:0] setup_before;
    logic [31:0] setup_after;
    // CALIPTRA_SETUP_DEBUG: accepted-generation [11:0], OCP owner [12].
    // No intervening native submission is possible between these snapshots.
    error_model.sample_setup_debug = 1;
    ocp_do_check_snapshot();
    setup_before = error_model.snapshot["CALIPTRA_SETUP_DEBUG"];
    error_model.ocp_configure_request(crc_kind,
      usb_cfg.remote_device_cfg[1].device_address,interface_number,
      OCP_CMD_PROT_CAP,scoreboard.model.control[1].epoch,
      scoreboard.model.control[1].generation+1,observer.next_order,zlp,max_read);
    // PROT_CAP is not read-clear, so this target cannot consume a spurious 04h.
    ocp_do_check_read(OCP_CMD_PROT_CAP,data);
    ocp_check_injection();
    ocp_do_check_snapshot();
    setup_after = error_model.snapshot["CALIPTRA_SETUP_DEBUG"];
    if ($isunknown(setup_before[11:0]) ||
        setup_after[12:0] !== {1'b1,12'(setup_before[11:0]+1'b1)})
      `uvm_fatal("OCP_CRC_CLAIM",$sformatf(
        "Target read did not correspond to exactly one claimed SETUP: before=%08h after=%08h",
        setup_before,setup_after))
    if (error_model.snapshot["DEVICE_STATUS_0"][15:8] !== OCP_PROTOCOL_ERROR_NONE)
      `uvm_fatal("OCP_CRC_STATUS", "Corrupted read STATUS raised a protocol error before USB read-clear")
    `uvm_info("OCP_CRC_CLAIM",$sformatf(
      "Claimed PROT_CAP STATUS retry generation=%0d->%0d owner=OCP protocol_error=00",
      setup_before[11:0],setup_after[11:0]),UVM_NONE)
    ocp_do_check_error_status();
    exercised = 1;
    error_model.release_dma = 1;
  endtask

  virtual task ocp_do_check_pre_image();
    bytes_t data;
    bytes_t payload;
    if (exercised) `uvm_fatal("OCP_CRC_SCOPE", "Duplicate corrupted-write experiment")
    // The scoreboard rejects any nonzero protocol error before arming.
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
    if (injection.read_status_crc) begin
      ocp_do_check_read_status_crc();
      return;
    end
    ocp_do_check_snapshot();
    base_wr = error_model.snapshot["INDIRECT_FIFO_STATUS_1"];
    base_rd = error_model.snapshot["INDIRECT_FIFO_STATUS_2"];
    if (base_wr !== base_rd || scoreboard.model.accepted_bytes != 0)
      `uvm_fatal("OCP_CRC_PREREQUISITE", "Corrupted write requires an empty FIFO with no accepted image bytes")
    for (int i = 0; i < 4; i++) payload.push_back(image[i]);
    error_model.ocp_configure_request(crc_kind,
      usb_cfg.remote_device_cfg[1].device_address,interface_number,
      OCP_CMD_INDIRECT_FIFO_DATA,scoreboard.model.control[1].epoch,
      scoreboard.model.control[1].generation+1,observer.next_order,payload);
    // The missing handshake is an expected host-side timeout, not a
    // turnaround violation.
    if (!injection.retry_crc) begin
      saved_disable_tend_check = usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout;
      usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = 1'b1;
      host_agent.reconfigure(usb_cfg);
    end
    `uvm_info("OCP_CRC_PROBE", $sformatf(
      "Armed %s on first INDIRECT_FIFO_DATA write: wr=%0d rd=%0d",
      crc_kind.name(),base_wr,base_rd),UVM_NONE)
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    if (offset != 1 || exercised) return;
    ocp_check_injection();
    if (!injection.retry_crc) begin
      usb_cfg.disable_tend_to_end_delay_check_for_expected_timeout = saved_disable_tend_check;
      host_agent.reconfigure(usb_cfg);
    end
    // Normal drain is held, so exactly the retried DWORD must be committed.
    ocp_do_check_snapshot();
    if (error_model.snapshot["INDIRECT_FIFO_STATUS_1"] !== base_wr+1 ||
        error_model.snapshot["INDIRECT_FIFO_STATUS_2"] !== base_rd)
      `uvm_fatal("OCP_CRC_COMMIT", $sformatf(
        "Corrupted write plus clean retry must commit one DWORD: wr=%0d->%0d rd=%0d->%0d",
        base_wr,error_model.snapshot["INDIRECT_FIFO_STATUS_1"],
        base_rd,error_model.snapshot["INDIRECT_FIFO_STATUS_2"]))
    if (scoreboard.model.accepted_bytes != 4)
      `uvm_fatal("OCP_CRC_COMMIT", "Wire ledger must credit precisely one DWORD")
    `uvm_info("OCP_CRC_COMMIT",$sformatf(
      "Exactly one DWORD credited and committed: wr=%0d->%0d rd=%0d",
      base_wr,error_model.snapshot["INDIRECT_FIFO_STATUS_1"],base_rd),UVM_NONE)
    ocp_do_check_error_status();
    exercised = 1;
    error_model.release_dma = 1;
  endtask

  virtual task ocp_do_check_host_completion();
    super.ocp_do_check_host_completion();
    if (!exercised)
      `uvm_fatal("OCP_CRC_INCOMPLETE", "Corrupted-write experiment was never exercised")
    `uvm_info("OCP_CRC_COMPLETE",$sformatf(
      "%s retried; image/recovery/activation/drain completed",crc_kind.name()),UVM_NONE)
  endtask

  task body();
    usb_ocp_write_crc_observer crc_observer;
    string profile;
    crc_kind = usb_ocp_protocol_error_model::WRITE_CRC;
    if ($value$plusargs("usb_ocp_crc_profile=%s",profile)) begin
      case (profile)
        "write_retry": crc_kind = usb_ocp_protocol_error_model::WRITE_RETRY_CRC;
        "read_status": crc_kind = usb_ocp_protocol_error_model::READ_STATUS_CRC;
        default: `uvm_fatal("OCP_CRC_SCOPE", "Unknown CRC profile")
      endcase
    end
    resolve_host_context(1);
    if (host_agent.prot == null)
      `uvm_fatal("OCP_CRC_SCOPE", "Native host protocol layer unavailable")
    if (!$cast(crc_observer,observer))
      `uvm_fatal("OCP_CRC_SCOPE", "Missing injection-aware observer")
    injection = usb_ocp_write_crc_callback::type_id::create("injection");
    injection.reporter = host_agent.prot;
    injection.retry_crc = crc_kind == usb_ocp_protocol_error_model::WRITE_RETRY_CRC;
    injection.read_status_crc = crc_kind == usb_ocp_protocol_error_model::READ_STATUS_CRC;
    crc_observer.injection = injection;
    if (injection.retry_crc || injection.read_status_crc) begin
      timeout_catcher = usb_ocp_crc_timeout_catcher::type_id::create("timeout_catcher");
      timeout_catcher.injection = injection;
      timeout_catcher.link_reporter = host_agent.link;
      timeout_catcher.error_model = error_model;
      uvm_report_cb::add(host_agent.prot,timeout_catcher);
      uvm_report_cb::add(host_agent.link,timeout_catcher);
    end
    uvm_callbacks#(svt_usb_protocol)::add(host_agent.prot,injection);
    super.body();
    uvm_callbacks#(svt_usb_protocol)::delete(host_agent.prot,injection);
    if (timeout_catcher != null) begin
      uvm_report_cb::delete(host_agent.prot,timeout_catcher);
      uvm_report_cb::delete(host_agent.link,timeout_catcher);
    end
    crc_observer.injection = null;
  endtask
endclass
