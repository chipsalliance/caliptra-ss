// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_ep0_checker extends usb_ocp_scoreboard;
  `uvm_component_utils(usb_ocp_fifo_backpressure_ep0_checker)
  // USB 2.0 9.4.2/9.4.3: replacement and follow-up standard requests.
  localparam logic [7:0] CONFIGURATION_SETUP[8] =
    '{8'h80,8'(svt_usb_types::GET_CONFIGURATION),0,0,0,0,1,0};
  localparam logic [7:0] DESCRIPTOR_SETUP[8] =
    '{8'h80,8'(svt_usb_types::GET_DESCRIPTOR),8'h00,8'h01,0,0,18,0};
  localparam int unsigned RELEASE_PROOF = 2;
  string canary_mode = "";
  bit canary_applied;
  usb_ocp_base_env_cfg ocp_cfg;
  bytes_t expected_image;
  logic [63:0] memory_base;
  logic [31:0] list_base;
  logic [31:0] setup_clear_mask;
  bit experiment_armed;
  // Planned actor barriers are lifecycle controls, never packet evidence.
  bit dma_hold_entered;
  bit dma_released;
  bit full_prefix_seen;
  bit full_status_seen;
  bit blocked_seen;
  bit replacement_seen;
  bit native_retired;
  bit native_completion_seen;
  bit drain_seen;
  bit empty_status_seen;
  bit resubmitted_seen;
  time witness_timeout = 2ms;
  longint unsigned full_order;
  longint unsigned blocked_order;
  longint unsigned replacement_order;
  longint unsigned native_order;
  longint unsigned drain_order;
  int unsigned actual_dma_bytes;
  int unsigned blocked_generation;
  int unsigned blocked_epoch;
  int unsigned nak_count;
  int unsigned ping_nak_count;
  int unsigned standard_crosschecks;
  usb_ocp_base_control blocked_control;
  usb_ocp_base_control standard_control[2];
  int unsigned standard_generation[2];
  int unsigned standard_epoch[2];
  // Observer snapshots are immutable actuals, not host completion flags.
  usb_ocp_event standard_completion[2];
  logic [1:0] setup_reads[2];
  int unsigned response_writes[2];
  bit in_armed[2];
  bit out_armed[2];
  bit setup_cleared[2];
  bit standard_status[2];
  bit standard_native[2];
  int unsigned accepted_before_event;
  int unsigned replacements_before_event;
  int unsigned crosschecks_before_event;
  usb_ocp_base_control control_before_event;
  usb_ocp_event token_before_event;
  usb_ocp_event data_before_event;
  usb_ocp_event pending_standard_axi[$];

  function new(string name = "usb_ocp_fifo_backpressure_ep0_checker",
      uvm_component parent = null);
    super.new(name,parent);
    setup_reads = '{default:0};
    response_writes = '{default:0};
    in_armed = '{default:0};
    out_armed = '{default:0};
    setup_cleared = '{default:0};
    standard_status = '{default:0};
    standard_native = '{default:0};
  endfunction

  static function string ocp_check_control_args(bit owner);
    uvm_cmdline_processor cli;
    string args[$];
    string mode = "";
    string value;
    string negative_prefix = "+usb_ocp_negative_fifo_ep0=";
    string variant_prefix = "+usb_ocp_fifo_ep0_variant=";
    int unsigned negative_count = 0;
    int unsigned variant_count = 0;
    cli = uvm_cmdline_processor::get_inst();
    cli.get_args(args);
    foreach (args[i]) begin
      if (!uvm_is_match("+usb_ocp_negative_fifo*",args[i]) &&
          !uvm_is_match("+usb_ocp_fifo*",args[i])) continue;
      if (!owner)
        uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Private FIFO controls require usb_ocp_fifo_backpressure_ep0_test", UVM_NONE, `__FILE__, `__LINE__);
      if (uvm_is_match({negative_prefix,"*"},args[i])) begin
        negative_count++;
        if (negative_count > 1)
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Duplicate usb_ocp_negative_fifo_ep0 selector", UVM_NONE, `__FILE__, `__LINE__);
        mode = args[i].substr(negative_prefix.len(),args[i].len()-1);
        if (!(mode inside {"full","blocked","replacement","sram_setup","sram_response"}))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Unknown FIFO EP0 canary value", UVM_NONE, `__FILE__, `__LINE__);
      end else if (uvm_is_match({variant_prefix,"*"},args[i])) begin
        variant_count++;
        if (variant_count > 1)
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Duplicate usb_ocp_fifo_ep0_variant selector", UVM_NONE, `__FILE__, `__LINE__);
        value = args[i].substr(variant_prefix.len(),args[i].len()-1);
        if (!(value inside {"partial","exact","capacity_plus_one"}))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Unknown FIFO EP0 variant value", UVM_NONE, `__FILE__, `__LINE__);
      end else
        uvm_pkg::uvm_report_fatal("OCP_FIFO_EP0_GUARD", "Unknown private FIFO control", UVM_NONE, `__FILE__, `__LINE__);
    end
    return mode;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    canary_mode = ocp_check_control_args(1);
  endfunction

  // Call only after every canonical comparison for this eligible actual has
  // passed. The caller changes a local expected operand and immediately fails.
  function bit ocp_check_canary(string gate, usb_ocp_event actual,
      int unsigned epoch, int unsigned generation);
    if (canary_mode != gate) return 0;
    if (canary_applied)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Duplicate FIFO EP0 canary application")
    if (!experiment_armed || ocp_cfg == null || actual == null || dma_released ||
        !model.require_dev0_ep0_replacement)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "FIFO EP0 canary lacks its owned held experiment")
    canary_applied = 1;
    `uvm_info("OCP_FIFO_EP0_CANARY", $sformatf(
      "gate=%s order=%0d epoch=%0d generation=%0d",
      gate,actual.order,epoch,generation), UVM_NONE)
    return 1;
  endfunction

  function void ocp_configure_experiment(bytes_t image_bytes);
    if (experiment_armed || ocp_cfg == null || model.accepted_bytes != 0 ||
        !model.fifo_discovered || image_bytes.size() <= model.fifo_depth_words*4)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Experiment requires fresh discovered FIFO and capacity-exceeding image")
    expected_image = image_bytes;
    experiment_armed = 1;
    `uvm_info("OCP_FIFO_EP0_PLAN", $sformatf(
      "Planned pre-DMA hold: capacity_words=%0d image_words=%0d max_write=%0d max_transfer_words=%0d",
      model.fifo_depth_words,image_bytes.size()/4,model.max_write,model.fifo_max_words), UVM_NONE)
  endfunction

  function int ocp_check_standard_slot(usb_ocp_base_control c);
    foreach (standard_control[i])
      if (c != null && c == standard_control[i] &&
          c.generation == standard_generation[i]) return i;
    return -1;
  endfunction

  // SRAM locations are the existing firmware actor's buffer contract, not
  // DUT-derived expectations. Native SETUP/response bytes remain independent.
  function void ocp_check_standard_sram(usb_ocp_event item);
    usb_ocp_base_control c;
    usb_ep_entry_t actual_entry;
    usb_ep_entry_t expected_entry;
    bytes_t expected;
    bytes_t expected_setup;
    logic [63:0] offset;
    logic [31:0] word;
    int slot;
    int byte_offset;
    c = model.control[1];
    slot = ocp_check_standard_slot(c);
    if (slot < 0 || item.order <= c.status_setup_order) return;
    if (item.manager == 0 && item.write_access &&
        item.axi_address === model.device_command_address[0]) begin
      if (item.response_ok !== 1 || item.bytes.size() != 4)
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement SETUP clear lacks successful DWORD response")
      word = model.ocp_get_le32(item.bytes,0);
      if ((word & setup_clear_mask) === setup_clear_mask) setup_cleared[slot] = 1;
    end
    if (item.manager != 1) return;
    offset = item.axi_address-memory_base;
    if (offset inside {[usb_ocp_firmware_base_seq::SETUP_BUFFER:
                        usb_ocp_firmware_base_seq::SETUP_BUFFER+4]} &&
        !item.write_access) begin
      byte_offset = int'(offset-usb_ocp_firmware_base_seq::SETUP_BUFFER);
      if (!(byte_offset inside {0,4}) || item.bytes.size() != 4 ||
          item.axi_beats != 1 || item.response_ok !== 1)
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Malformed replacement SETUP SRAM read")
      foreach (item.bytes[i])
        if (item.bytes[i] !== c.setup[byte_offset+i])
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "SRAM SETUP differs from ACK-qualified same-device SETUP")
      if (byte_offset == 4 && setup_reads[slot][0] !== 1)
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement SETUP DWORD reads are out of order")
      foreach (c.setup[i]) expected_setup.push_back(c.setup[i]);
      if (slot == 0 && byte_offset == 0 && setup_reads[slot] === 2'b00 &&
          ocp_check_canary("sram_setup",item,c.epoch,c.generation))
        expected_setup[0] ^= 8'h01;
      foreach (item.bytes[i])
        if (item.bytes[i] !== expected_setup[byte_offset+i])
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "SRAM SETUP differs from ACK-qualified same-device SETUP")
      setup_reads[slot][byte_offset/4] = 1;
    end
    expected = c.expected;
    if (item.write_access && offset >= usb_ocp_firmware_base_seq::IN_BUFFER &&
        offset < usb_ocp_firmware_base_seq::IN_BUFFER+64) begin
      byte_offset = int'(offset-usb_ocp_firmware_base_seq::IN_BUFFER);
      if (setup_reads[slot] !== 2'b11 || byte_offset != response_writes[slot] ||
          item.response_ok !== 1 || item.axi_beats != 1 || item.bytes.size() != 4 ||
          item.strobes.size() != 4 || byte_offset >= expected.size())
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement response SRAM write lacks exact context/order")
      foreach (item.bytes[i])
        if (item.strobes[i] !== 1 ||
            item.bytes[i] !== ((byte_offset+i < expected.size()) ?
                              expected[byte_offset+i] : 8'h00))
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement response SRAM bytes/padding/strobes differ")
      if (slot == 0 && byte_offset == 0 &&
          ocp_check_canary("sram_response",item,c.epoch,c.generation))
        expected[0] ^= 8'h01;
      foreach (item.bytes[i])
        if (item.bytes[i] !== ((byte_offset+i < expected.size()) ?
                              expected[byte_offset+i] : 8'h00))
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement response SRAM bytes/padding/strobes differ")
      response_writes[slot] += 4;
    end
    if (item.write_access && offset inside {64'(list_base),64'(list_base+8)}) begin
      if (item.bytes.size() != 4 || item.response_ok !== 1 ||
          item.strobes.size() != 4 || setup_reads[slot] !== 2'b11)
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement EP0 arm lacks checked SETUP/AXI context")
      foreach (item.strobes[i])
        if (item.strobes[i] !== 1)
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement EP0 arm requires all byte lanes")
      actual_entry = model.ocp_get_le32(item.bytes,0);
      expected_entry = '0;
      expected_entry.active = 1;
      if (offset == list_base+8) begin
        expected_entry.nbytes = 15'(expected.size());
        expected_entry.buffer_offset = 11'(usb_ocp_firmware_base_seq::IN_BUFFER >> 6);
        if (response_writes[slot] != ((expected.size()+3)/4)*4)
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "IN armed before complete exact replacement response")
        in_armed[slot] = 1;
      end else begin
        expected_entry.buffer_offset = 11'(usb_ocp_firmware_base_seq::OUT_BUFFER >> 6);
        out_armed[slot] = 1;
      end
      if (actual_entry !== expected_entry)
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Replacement EP0 entry differs from exact IN/OUT arm contract")
    end
  endfunction

  function void ocp_check_pending_standard_axi();
    usb_ocp_event actual;
    usb_ocp_base_control c;
    c = model.control[1];
    if (ocp_check_standard_slot(c) < 0) return;
    // The device may finish a frontdoor read before its SETUP ACK finishes
    // on the wire. Retain the completed actual until accepted SETUP provides
    // its generation; never compare it against the preceding request.
    if (model.token != null && model.token_device == 1 &&
        model.token.pid == svt_usb_packet::SETUP &&
        model.token.order > c.status_setup_order) return;
    while (pending_standard_axi.size() != 0) begin
      actual = pending_standard_axi.pop_front();
      // Earlier OCP SETUP polling is not a replacement SRAM obligation.
      // Only this private ancillary queue is retired here, never a byte or
      // native/AXI obligation in the original scoreboard/observer ledgers.
      if (actual.order > c.status_setup_order) ocp_check_standard_sram(actual);
    end
  endfunction

  function void ocp_check_join_standard_proofs(longint unsigned proof_order);
    usb_ocp_base_control c;
    c = model.control[1];
    foreach (standard_completion[slot]) begin
      if (standard_completion[slot] == null || standard_native[slot]) continue;
      if (ocp_check_standard_slot(c) != slot || c.epoch != standard_epoch[slot])
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Peer context changed before native/SRAM proof joined")
      if (!standard_status[slot] || setup_reads[slot] !== 2'b11 ||
          response_writes[slot] != ((c.expected.size()+3)/4)*4 ||
          !in_armed[slot] || !out_armed[slot] || !setup_cleared[slot] ||
          pending_standard_axi.size() != 0) continue;
      standard_native[slot] = 1;
      standard_crosschecks++;
      `uvm_info("OCP_FIFO_EP0_PEER_PROOF", $sformatf(
        "peer=%0d epoch=%0d generation=%0d setup_order=%0d native_order=%0d proof_order=%0d setup_reads=%0d response_bytes=%0d in_armed=%0b out_armed=%0b setup_cleared=%0b status=%0b",
        slot,standard_epoch[slot],standard_generation[slot],c.status_setup_order,
        standard_completion[slot].order,proof_order,setup_reads[slot],
        response_writes[slot],in_armed[slot],out_armed[slot],setup_cleared[slot],
        standard_status[slot]), UVM_NONE)
    end
  endfunction

  // A peer cannot submit its next SETUP until this joined proof is visible.
  // RELEASE_PROOF additionally joins actual old native retirement and the
  // consumed checked prefix; no host-only completion grants DMA permission.
  task ocp_check_proof_barrier(int unsigned peer);
    bit ready;
    if (peer > RELEASE_PROOF || ocp_cfg == null || dma_released)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Invalid FIFO EP0 checker proof barrier")
    ready = 0;
    fork
      begin
        fork
          begin
            if (peer < RELEASE_PROOF) wait (standard_native[peer]);
            else wait (standard_native[0] && standard_native[1] &&
              native_completion_seen && native_retired && model.replacement_crosschecks == 1 &&
              model.replaced_controls[1].size() == 0 &&
              !model.checked_replacement_valid[1] && deferred_transfer_aborts.size() == 0 &&
              pending_standard_axi.size() == 0);
            ready = 1;
          end
          begin #(witness_timeout); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!ready)
      `uvm_fatal("OCP_FIFO_EP0_WAIT", $sformatf(
        "Checker proof timeout/teardown: peer=%0d epochs=%p generations=%p native_seen=%0b/%0b joined=%p setup_reads=%p response_bytes=%p in_armed=%p out_armed=%p setup_cleared=%p status=%p old_native_seen=%0b old_retired=%0b old_crosschecks=%0d replaced=%0d aborts=%0d checked_prefix=%0b pending_SRAM=%0d; DMA remains held",
        peer,standard_epoch,standard_generation,standard_completion[0] != null,
        standard_completion[1] != null,standard_native,setup_reads,response_writes,
        in_armed,out_armed,setup_cleared,standard_status,native_completion_seen,
        native_retired,model.replacement_crosschecks,model.replaced_controls[1].size(),
        deferred_transfer_aborts.size(),model.checked_replacement_valid[1],
        pending_standard_axi.size()))
    `uvm_info("OCP_FIFO_EP0_PROOF_BARRIER", $sformatf(
      "peer=%0d standard_native=%p old_native=%0b pending_SRAM=%0d",
      peer,standard_native,native_retired,pending_standard_axi.size()), UVM_NONE)
  endtask

  virtual function void ocp_check_event_before(usb_ocp_event item);
    usb_ocp_base_control c;
    usb_ocp_event t;
    int unsigned expected_generation;
    if (!experiment_armed) return;
    accepted_before_event = model.accepted_bytes;
    replacements_before_event = model.dev0_ep0_write_replacements;
    crosschecks_before_event = model.replacement_crosschecks;
    control_before_event = model.control[1];
    token_before_event = model.token;
    data_before_event = model.candidate;
    c = model.control[1];
    t = model.token;
    if (item.kind == usb_ocp_event::USB_TRANSFER && blocked_seen &&
        item.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1) begin
      if (native_completion_seen || item.address !== blocked_control.address ||
          item.endpoint !== 0 || item.setup !== blocked_control.setup ||
          item.transfer_start_order >= blocked_order || item.transfer_ok !== 0)
        `uvm_fatal("OCP_FIFO_EP0_RETIRE", "Native abort crossed blocked original identity or completion")
      native_completion_seen = 1;
      native_order = item.order;
    end
    if (item.kind == usb_ocp_event::AXI_COMPLETED) begin
      if (blocked_seen && !dma_released &&
          (item.manager == 1 ||
            (item.manager == 0 && item.write_access &&
            item.axi_address === model.device_command_address[0]))) begin
        if (pending_standard_axi.size() >= 16384)
          `uvm_fatal("OCP_FIFO_EP0_SRAM", "Unreconciled replacement SRAM actuals exceeded bound")
        pending_standard_axi.push_back(item);
      end
      if (item.manager == 0 && !item.write_access &&
          model.recovery_register.exists(item.axi_address) &&
          model.recovery_register[item.axi_address] == "INDIRECT_FIFO_DATA") begin
        if (!dma_released || !dma_hold_entered || !replacement_seen || !native_retired ||
            item.response_ok !== 1 || item.axi_burst !== AAXI_BURST_FIXED ||
            item.axi_beat_bytes != 4 || item.bytes.size() != item.axi_beats*4)
          `uvm_fatal("OCP_FIFO_EP0_DMA", "DMA precedes planned release/retirement or lacks exact FIXED DWORD context")
        actual_dma_bytes += item.bytes.size();
        if (!drain_seen && actual_dma_bytes == model.fifo_depth_words*4) begin
          drain_seen = 1;
          drain_order = item.order;
          `uvm_info("OCP_FIFO_EP0_DRAIN", $sformatf(
            "Real AXI drain of retained full prefix bytes=%0d order=%0d",
            actual_dma_bytes,drain_order), UVM_NONE)
        end
      end
    end
    // USB 2.0 8.5.1/8.5.3: only DATA-stage OUT/NAK or HS PING/NAK
    // demonstrates blocking. STATUS NAK/NYET is not this witness.
    if (item.kind == usb_ocp_event::USB_PACKET && item.pid == svt_usb_packet::NAK &&
        t != null && t.endpoint === 0 && model.token_device == 1 &&
        c.active === 1 && c.setup[0] === 8'h21 &&
        c.ocp_get_value() === 16'(OCP_CMD_INDIRECT_FIFO_DATA) &&
        t.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING} && full_status_seen) begin
      if (item.host_tx !== 0 || item.packet_valid !== 1 ||
          t.packet_valid !== 1 || t.host_tx !== 1 || t.address !== c.address ||
          model.token_epoch != c.epoch || model.token_generation != c.generation ||
          c.status_acked !== 0 || c.ocp_get_length() != 4 || c.data.size() != 0 ||
          model.accepted_bytes != model.fifo_depth_words*4 || actual_dma_bytes != 0 ||
          dma_released || !dma_hold_entered)
        `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "NAK witness lacks held full FIFO and original live DATA context")
      if (t.pid == svt_usb_packet::OUT) begin
        if (model.candidate == null || model.candidate.pid != svt_usb_packet::DATA1 ||
            model.candidate.bytes.size() != 4)
          `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "OUT/NAK lacks the attempted capacity+1 DWORD")
        foreach (model.candidate.bytes[i])
          if (model.candidate.bytes[i] !== expected_image[model.fifo_depth_words*4+i])
            `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "Rejected DWORD differs from next ordered image bytes")
        nak_count++;
      end else begin
        if (ocp_cfg.full_speed || model.candidate != null)
          `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "PING witness is not a legal HS DATA-stage query")
        ping_nak_count++;
      end
      expected_generation = c.generation;
      if (!blocked_seen && ocp_check_canary("blocked",item,c.epoch,c.generation))
        expected_generation++;
      if (model.token_generation != expected_generation)
        `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "NAK witness lacks held full FIFO and original live DATA context")
      if (!blocked_seen) begin
        blocked_seen = 1;
        blocked_control = c;
        blocked_generation = c.generation;
        blocked_epoch = c.epoch;
        blocked_order = item.order;
        `uvm_info("OCP_FIFO_EP0_BLOCKED", $sformatf(
          "Native %s/NAK at full capacity addr=%0d epoch=%0d generation=%0d order=%0d",
          t.pid.name(),c.address,c.epoch,c.generation,blocked_order), UVM_NONE)
      end else if (blocked_control != c)
        `uvm_fatal("OCP_FIFO_EP0_BLOCKED", "Blocking witness crossed original control identity")
    end
  endfunction

  virtual function void ocp_check_event_after(usb_ocp_event item);
    usb_ocp_base_control c;
    logic [7:0] expected_setup[8];
    int unsigned expected_full_bytes;
    int slot;
    if (!experiment_armed) return;
    c = model.control[1];
    if (model.accepted_bytes > expected_image.size() ||
        (model.accepted_bytes >= model.returned_bytes &&
          model.accepted_bytes-model.returned_bytes > model.fifo_depth_words*4))
      `uvm_fatal("OCP_FIFO_EP0_OVERRUN", "Accepted byte ledger exceeds image or full advertised capacity")
    if (model.accepted_bytes > accepted_before_event) begin
      if (data_before_event == null)
        `uvm_fatal("OCP_FIFO_EP0_IMAGE", "Acceptance lacks independent native DATA snapshot")
      foreach (data_before_event.bytes[i])
        if (data_before_event.bytes[i] !== expected_image[accepted_before_event+i])
          `uvm_fatal("OCP_FIFO_EP0_IMAGE", "Accepted image bytes are duplicated, missing, reordered or corrupt")
      if (!full_prefix_seen && model.accepted_bytes == model.fifo_depth_words*4 &&
          actual_dma_bytes == 0) begin
        full_prefix_seen = 1;
        full_order = item.order;
        `uvm_info("OCP_FIFO_EP0_CAPACITY", $sformatf(
          "ACK/NYET-qualified prefix fills all advertised words=%0d order=%0d",
          model.fifo_depth_words,full_order), UVM_NONE)
      end
      if (replacement_seen) begin
        if (!drain_seen || !empty_status_seen)
          `uvm_fatal("OCP_FIFO_EP0_RESUBMIT", "Post-replacement bytes accepted before real drain and empty status")
        if (!resubmitted_seen)
          `uvm_info("OCP_FIFO_EP0_RESUBMIT", $sformatf(
            "Fresh OCP command accepted next unique image bytes at offset=%0d after real drain order=%0d",
            accepted_before_event,drain_order), UVM_NONE)
        resubmitted_seen = 1;
      end
    end
    if (model.dev0_ep0_write_replacements > replacements_before_event) begin
      if (!blocked_seen || control_before_event != blocked_control ||
          blocked_control.status_acked !== 0 || blocked_control.data.size() != 0 ||
          token_before_event == null || token_before_event.order <= blocked_order ||
          actual_dma_bytes != 0 || dma_released || c.setup !== CONFIGURATION_SETUP)
        `uvm_fatal("OCP_FIFO_EP0_REPLACEMENT", "Replacement lacks actual same-device SETUP before blocked STATUS completion")
      expected_setup = CONFIGURATION_SETUP;
      if (ocp_check_canary("replacement",item,blocked_epoch,blocked_generation))
        expected_setup[6] = 8'd2;
      if (c.setup !== expected_setup)
        `uvm_fatal("OCP_FIFO_EP0_REPLACEMENT", "Replacement lacks actual same-device SETUP before blocked STATUS completion")
      replacement_seen = 1;
      replacement_order = token_before_event.order;
      standard_control[0] = c;
      standard_generation[0] = c.generation;
      standard_epoch[0] = c.epoch;
      `uvm_info("OCP_FIFO_EP0_REPLACEMENT", $sformatf(
        "ACK-qualified non-OCP SETUP replaced blocked epoch=%0d generation=%0d setup_order=%0d",
        blocked_epoch,blocked_generation,replacement_order), UVM_NONE)
    end
    if (replacement_seen && standard_control[1] == null &&
        c.generation > standard_generation[0] &&
        c.active === 1 && c.setup === DESCRIPTOR_SETUP) begin
      if (!standard_native[0])
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Next peer SETUP preceded prior joined proof")
      standard_control[1] = c;
      standard_generation[1] = c.generation;
      standard_epoch[1] = c.epoch;
    end
    foreach (standard_control[i])
      if (standard_control[i] != null && !standard_native[i] &&
          (c.generation != standard_generation[i] || c.epoch != standard_epoch[i]))
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Peer context changed before native/SRAM proof joined")
    ocp_check_pending_standard_axi();
    // The predictor reuses a control object for ordinary later SETUPs.
    // Preserve completed first-response proof before the second SETUP.
    slot = ocp_check_standard_slot(c);
    if (slot >= 0 && c.status_acked === 1) standard_status[slot] = 1;
    if (item.kind == usb_ocp_event::USB_TRANSFER && replacement_seen &&
        item.transfer_ok === 1 && item.address === model.address[1] &&
        item.endpoint === 0 && item.setup[0] === 8'h80 &&
        item.setup[1] inside {svt_usb_types::GET_CONFIGURATION,svt_usb_types::GET_DESCRIPTOR}) begin
      slot = (item.setup[1] == svt_usb_types::GET_CONFIGURATION) ? 0 : 1;
      if (standard_completion[slot] != null || ocp_check_standard_slot(c) != slot ||
          c.epoch != standard_epoch[slot] || item.setup !== c.setup ||
          item.transfer_start_order >= c.status_setup_order ||
          item.order <= c.status_setup_order || !standard_status[slot])
        `uvm_fatal("OCP_FIFO_EP0_SRAM", "Native peer completion lacks unique generation-qualified STATUS context")
      standard_completion[slot] = item;
      `uvm_info("OCP_FIFO_EP0_PEER_NATIVE", $sformatf(
        "peer=%0d epoch=%0d generation=%0d setup_order=%0d native_order=%0d",
        slot,standard_epoch[slot],standard_generation[slot],c.status_setup_order,
        item.order), UVM_NONE)
    end
    ocp_check_join_standard_proofs(item.order);
    if (model.replacement_crosschecks > crosschecks_before_event) begin
      if (!replacement_seen || !native_completion_seen ||
          model.checked_replacement_bytes[1].size() != 0)
        `uvm_fatal("OCP_FIFO_EP0_RETIRE", "Blocked native retirement lacks zero unaccepted-byte prefix")
      native_retired = 1;
    end
    if (item.kind == usb_ocp_event::USB_TRANSFER &&
        item.setup[0] === 8'ha1 && item.setup[2] === OCP_CMD_INDIRECT_FIFO_STATUS &&
        item.transfer_ok === 1 && full_prefix_seen) begin
      if (!dma_released) begin
        if (model.accepted_bytes != model.fifo_depth_words*4 || model.returned_bytes != 0 ||
            item.bytes.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS ||
            item.bytes[0] !== OCP_IFS_FULL_MASK)
          `uvm_fatal("OCP_FIFO_EP0_CAPACITY", "Full prefix lacks exact live FIFO full status")
        expected_full_bytes = model.fifo_depth_words*4;
        if (!full_status_seen && ocp_check_canary("full",item,c.epoch,c.generation))
          expected_full_bytes += 4;
        if (model.accepted_bytes != expected_full_bytes)
          `uvm_fatal("OCP_FIFO_EP0_CAPACITY", "Full prefix lacks exact live FIFO full status")
        full_status_seen = 1;
        `uvm_info("OCP_FIFO_EP0_FULL_STATUS", "Live native/monitor FIFO status confirms full advertised capacity", UVM_NONE)
      end else if (drain_seen && model.returned_bytes == model.accepted_bytes &&
                    item.bytes[0] === OCP_IFS_EMPTY_MASK)
        empty_status_seen = 1;
    end
  endfunction

  function void ocp_check_release_dma();
    if (dma_released || !dma_hold_entered || !full_prefix_seen || !full_status_seen ||
        !blocked_seen || !replacement_seen || !native_retired ||
        !standard_native[0] || !standard_native[1] || actual_dma_bytes != 0 ||
        model.accepted_bytes != model.fifo_depth_words*4 || pending_standard_axi.size() != 0)
      `uvm_fatal("OCP_FIFO_EP0_BARRIER", "Planned DMA release precedes full/blocked/replacement/native/SRAM obligations")
    dma_released = 1;
    `uvm_info("OCP_FIFO_EP0_RELEASE", "Release planned Caliptra DMA hold; accepted-byte ledger retained", UVM_NONE)
  endfunction

  virtual function void ocp_check_replacements();
    if (canary_mode != "")
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Selected FIFO EP0 canary reached final checks without targeted rejection")
    if (!experiment_armed || !full_prefix_seen || !full_status_seen || !blocked_seen ||
        !replacement_seen || !native_retired || !dma_released || !drain_seen ||
        !empty_status_seen || !resubmitted_seen || standard_crosschecks != 2 ||
        model.dev0_ep0_read_replacements != 0 || model.dev0_ep0_write_replacements != 1 ||
        model.replacement_crosschecks != 1 || model.replaced_controls[1].size() != 0 ||
        model.checked_replacement_valid[1] || deferred_transfer_aborts.size() != 0 ||
        actual_dma_bytes != expected_image.size() || pending_standard_axi.size() != 0 ||
        !(full_order < blocked_order && blocked_order < replacement_order &&
          replacement_order < drain_order && blocked_order < native_order &&
          native_order < drain_order))
      `uvm_fatal("OCP_FIFO_EP0_INCOMPLETE", "Unreached capacity/block/replacement/SRAM/retirement/drain/resubmission obligations")
    if (negative_replacement || negative_abort_prefix)
      `uvm_fatal("OCP_FIFO_EP0_GUARD", "Use only row-owned controls, not other replacement checker injections")
    `uvm_info("OCP_FIFO_EP0_EVIDENCE", $sformatf(
      "capacity=%0d OUT_NAK=%0d PING_NAK=%0d full_order=%0d blocked_order=%0d replacement_order=%0d native_order=%0d drain_order=%0d standard_native=%p SRAM_setup=%p SRAM_response=%p accepted=%0d DMA=%0d",
      model.fifo_depth_words,nak_count,ping_nak_count,full_order,blocked_order,
      replacement_order,native_order,drain_order,standard_native,setup_reads,
      response_writes,model.accepted_bytes,actual_dma_bytes), UVM_NONE)
  endfunction
endclass
