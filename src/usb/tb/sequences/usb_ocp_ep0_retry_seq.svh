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

class usb_ocp_ep0_retry_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_ep0_retry_host_seq)
  localparam int unsigned IMAGE_WORDS = 32;
  localparam int unsigned DWORD_BYTES = 4;
  localparam time STATUS_OBSERVATION_TIMEOUT = 100us;
  localparam time RETRY_RECOVERY_TIMEOUT = 250us;
  usb_ocp_ep0_retry_control retry;
  usb_ocp_ep0_retry_callback protocol_callback;
  usb_ocp_ep0_retry_packet_callback packet_callback;
  usb_ocp_ep0_retry_timeout_catcher timeout_catcher;
  string mode = "both";
  bit read_probe;
  bit write_selected;
  bit watchdog_canary;
  int unsigned read_cases;
  int unsigned write_cases;

  constraint retry_image_c {
    foreach (image[i]) image[i] == 8'(i ^ (i >> 8) ^ 8'ha5);
  }

  function new(string name = "usb_ocp_ep0_retry_host_seq");
    super.new(name);
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    words = IMAGE_WORDS;
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    if (offset == 0) chunk_words = words < chunk_limit ? words : chunk_limit;
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    usb_ocp_ep0_retry_control::retry_kind_e kind;
    if (device != 1 || mode == "control") return;
    if (read_probe)
      kind = usb_ocp_ep0_retry_control::READ_RETRY;
    else if ((mode inside {"both","write"}) && !write_selected &&
             tr.setup_data_w_value == OCP_CMD_INDIRECT_FIFO_DATA &&
             tr.setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE) begin
      kind = usb_ocp_ep0_retry_control::WRITE_RETRY;
      write_selected = 1;
    end else return;
    retry.ocp_configure_request(tr,kind);
  endfunction

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    bit observed;
    if (tr != retry.original) return;
    if (watchdog_canary) begin
      `uvm_info("OCP_EP0_RETRY_WATCHDOG_CANARY",
        "Holding selected completion to exercise the independent watchdog", UVM_NONE)
      wait (retry.original != tr);
      return;
    end
    if (tr.status == svt_sequence_item::ACCEPT && !retry.status_acked) begin
      observed = 0;
      fork
        begin
          fork
            begin wait (retry.status_acked); observed = 1; end
            begin #(STATUS_OBSERVATION_TIMEOUT); end
          join_any
          disable fork;
        end
      join
      if (!observed)
        `uvm_error("OCP_EP0_RETRY_STATUS", "Native completion lacks an independently observed Status ACK")
    end
    if (retry.kind == usb_ocp_ep0_retry_control::READ_RETRY) read_cases++;
    else write_cases++;
    retry.ocp_check_completion();
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    bit retired;
    if (tr != retry.original) return;
    retired = 0;
    fork
      begin
        fork
          begin wait (retry.original != tr); retired = 1; end
          begin #(RETRY_RECOVERY_TIMEOUT); end
        join_any
        disable fork;
      end
    join
    if (!retired) begin
      retry.ocp_check_completion();
      `uvm_fatal("OCP_EP0_RETRY_TIMEOUT", $sformatf(
        "Selected CONTROL retry did not recover within its independent %0t watchdog",
        RETRY_RECOVERY_TIMEOUT))
    end
  endtask

  virtual task ocp_do_check_post_capabilities(bytes_t data);
    bytes_t repeated;
    if (mode == "write") return;
    read_probe = 1;
    ocp_do_check_read(OCP_CMD_PROT_CAP,repeated);
    read_probe = 0;
    if (repeated.size() != data.size())
      `uvm_fatal("OCP_EP0_RETRY_READ", "PROT_CAP changed length across the retry experiment")
    foreach (data[i])
      if (repeated[i] !== data[i])
        `uvm_fatal("OCP_EP0_RETRY_READ", "Retried PROT_CAP differs from preceding protocol discovery")
  endtask

  task body();
    usb_ocp_ep0_retry_observer retry_observer;
    resolve_host_context(1);
    void'($value$plusargs("usb_ocp_ep0_retry=%s",mode));
    if (!(mode inside {"both","read","write","control"}) || ocp_cfg.full_speed)
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Select both/read/write/control in the direct HS topology")
    retry = usb_ocp_ep0_retry_control::type_id::create("retry");
    retry.skip_loss = $test$plusargs("usb_ocp_ep0_retry_skip_loss");
    watchdog_canary = $test$plusargs("usb_ocp_ep0_retry_watchdog_canary");
    if (retry.skip_loss && mode == "control")
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Missing-injection canary requires a retry experiment")
    if (watchdog_canary && (!retry.skip_loss || mode != "read"))
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Watchdog canary requires read mode without handshake loss")
    if (!$cast(retry_observer,observer))
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Missing injection-aware observer")
    retry_observer.control = retry;
    protocol_callback = usb_ocp_ep0_retry_callback::type_id::create("protocol_callback");
    packet_callback = usb_ocp_ep0_retry_packet_callback::type_id::create("packet_callback");
    protocol_callback.control = retry;
    packet_callback.control = retry;
    timeout_catcher = usb_ocp_ep0_retry_timeout_catcher::type_id::create("timeout_catcher");
    timeout_catcher.control = retry;
    if (host_agent.prot == null || host_agent.link_mon == null)
      `uvm_fatal("OCP_EP0_RETRY_SCOPE", "Native protocol or wire monitor unavailable")
    uvm_callbacks#(svt_usb_protocol)::add(host_agent.prot,protocol_callback);
    uvm_report_cb::add(host_agent.prot,timeout_catcher);
    uvm_callbacks#(svt_usb_link_monitor,svt_usb_link_monitor_callback)::add(
      host_agent.link_mon,packet_callback);
    super.body();
    uvm_callbacks#(svt_usb_protocol)::delete(host_agent.prot,protocol_callback);
    uvm_report_cb::delete(host_agent.prot,timeout_catcher);
    uvm_callbacks#(svt_usb_link_monitor,svt_usb_link_monitor_callback)::delete(
      host_agent.link_mon,packet_callback);
    if (read_cases != (mode inside {"both","read"}) ||
        write_cases != (mode inside {"both","write"}))
      `uvm_fatal("OCP_EP0_RETRY_COVERAGE", "Selected native retry experiment did not complete")
    `uvm_info("OCP_EP0_RETRY_COMPLETE", $sformatf(
      "mode=%s read_cases=%0d write_cases=%0d; existing image/activation/drain checks retained",
      mode,read_cases,write_cases), UVM_NONE)
  endtask
endclass

class usb_ocp_ep0_retry_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_ep0_retry_seq)
  usb_ocp_ep0_retry_host_seq host;

  function new(string name = "usb_ocp_ep0_retry_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    host = usb_ocp_ep0_retry_host_seq::type_id::create("host");
    return host;
  endfunction

  task ocp_do_check_write_commit();
    logic [31:0] write_index;
    int unsigned expected_index;
    time deadline;
    wait (host != null && host.retry != null);
    if (!(host.mode inside {"both","write"}) || host.retry.skip_loss) return;
    wait (host.retry.original != null &&
          host.retry.kind == usb_ocp_ep0_retry_control::WRITE_RETRY &&
          host.retry.loss_applied);
    expected_index = host.retry.original.setup_data_w_length /
                     usb_ocp_ep0_retry_host_seq::DWORD_BYTES;
    if (expected_index == 0 || expected_index >= host.fifo_depth)
      `uvm_fatal("OCP_EP0_RETRY_BOUNDARY", "Selected chunk cannot qualify an unambiguous WRITE_INDEX advance")
    deadline = $time + usb_ocp_ep0_retry_host_seq::STATUS_OBSERVATION_TIMEOUT;
    // OCP 1.1 9.2 INDIRECT_FIFO_STATUS: Write Index counts accepted DWORDs.
    // An AXI read preserves the CONTROL transfer; a USB read would replace it.
    do begin
      ral_read32("retry_write_index",
        p_sequencer.reg_model.combo.recovery.INDIRECT_FIFO_STATUS_1,write_index);
      if (host.retry.data_tokens >= 2 || $time >= deadline)
        `uvm_fatal("OCP_EP0_RETRY_BOUNDARY", "Public write commit was not observed before repeated OUT")
      if (write_index === expected_index) break;
      #1us;
    end while (1);
    host.retry.write_committed_before_retry = 1;
    `uvm_info("OCP_EP0_RETRY_COMMIT", $sformatf(
      "Public WRITE_INDEX=%0d before repeated OUT; expected from original payload=%0d",
      write_index,expected_index), UVM_NONE)
  endtask

  task body();
    fork
      super.body();
      ocp_do_check_write_commit();
    join
  endtask
endclass
