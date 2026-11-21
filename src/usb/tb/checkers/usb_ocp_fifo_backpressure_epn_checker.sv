// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_fifo_backpressure_epn_checker extends usb_ocp_scoreboard;
  `uvm_component_utils(usb_ocp_fifo_backpressure_epn_checker)
  usb_ocp_base_env_cfg ocp_cfg;
  usb_ocp_base_epn_model epn;
  int unsigned epn_device = 1;
  bytes_t expected_image;
  string canary_mode;
  bit canary_applied;
  bit experiment_armed;
  bit dma_hold_entered;
  bit dma_released;
  bit full_prefix_seen;
  bit full_status_seen;
  bit blocked_seen;
  bit overlap_joined;
  bit proof_consumed;
  bit retry_accepted;
  bit retry_native;
  bit retry_joined;
  time witness_timeout = 2ms;
  int unsigned actual_dma_bytes;
  int unsigned nak_count;
  int unsigned ping_nak_count;
  int unsigned blocked_epoch;
  int unsigned blocked_generation;
  logic [6:0] blocked_address;
  logic [7:0] blocked_setup[8];
  longint unsigned full_order;
  longint unsigned blocked_order;
  longint unsigned proof_order;
  longint unsigned release_order;
  longint unsigned first_dma_order;
  longint unsigned first_dma_address_floor;
  longint unsigned retry_data_order;
  realtime release_at;
  longint unsigned retry_order;
  longint unsigned native_order;
  int unsigned accepted_before_event;
  usb_ocp_event data_before_event;
  usb_ocp_event overlap_actual[2];
  // Extra passive proof of firmware buffer initialization and exact arms.
  // Existing EPN ledgers still own packet/native/retirement/payload checking.
  int unsigned sram_phase[2];
  int unsigned sram_bytes[2];
  bit sram_armed[2][2];
  covergroup held_service_cov with function sample(int peer, int kind, int dir);
    option.per_instance = 1;
    peer_cp: coverpoint peer { bins dev0 = {1}; bins dev1 = {2}; }
    kind_cp: coverpoint kind { bins bulk = {1}; bins interrupt_type = {2}; bins iso = {3}; }
    dir_cp: coverpoint dir { bins out_dir = {0}; bins in_dir = {1}; }
    service_cross: cross peer_cp, kind_cp, dir_cp;
  endgroup

  function new(string name = "usb_ocp_fifo_backpressure_epn_checker",
      uvm_component parent = null);
    super.new(name,parent);
    sram_phase = '{default:0};
    sram_bytes = '{default:0};
    sram_armed = '{default:'{default:0}};
    held_service_cov = new();
  endfunction

  static function string ocp_check_control_args(bit owner);
    uvm_cmdline_processor cli;
    string args[$];
    string keys[4] = '{"+usb_ocp_fifo_epn_peer=",
      "+usb_ocp_fifo_epn_variant=","+usb_ocp_negative_fifo_epn=","+usb_ocp_epn_type="};
    int counts[4] = '{default:0};
    int selected;
    int negatives = 0;
    string value;
    string mode = "";
    bit fifo_arg;
    cli = uvm_cmdline_processor::get_inst();
    cli.get_args(args);
    foreach (args[i]) begin
      fifo_arg = uvm_is_match("+usb_ocp_fifo*",args[i]) ||
        uvm_is_match("+usb_ocp_negative_fifo*",args[i]);
      if (!owner) begin
        if (uvm_is_match("+usb_ocp_fifo_epn*",args[i]) ||
            uvm_is_match("+usb_ocp_negative_fifo_epn*",args[i]))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
            "Private FIFO EPN controls require usb_ocp_fifo_backpressure_epn_test",
            UVM_NONE, `__FILE__, `__LINE__);
        continue;
      end
      if (!fifo_arg && !uvm_is_match("+usb_ocp_epn*",args[i]) &&
          !uvm_is_match("+usb_ocp_negative*",args[i])) continue;
      // Reuse only the comparison-only EPN payload rejection path.
      if (args[i] == "+usb_ocp_negative_epn_payload") begin
        negatives++;
        if (negatives > 1)
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
            "Select exactly one private rejection control", UVM_NONE, `__FILE__, `__LINE__);
        continue;
      end
      selected = -1;
      foreach (keys[k])
        if (uvm_is_match({keys[k],"*"},args[i])) selected = k;
      if (selected < 0)
        uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
          "Unknown, bare or foreign FIFO EPN control", UVM_NONE, `__FILE__, `__LINE__);
      if (selected < 0) return mode;
      counts[selected]++;
      if (counts[selected] > 1)
        uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
          "Duplicate FIFO EPN selector", UVM_NONE, `__FILE__, `__LINE__);
      value = "";
      if (args[i].len() > keys[selected].len())
        value = args[i].substr(keys[selected].len(),args[i].len()-1);
      case (selected)
        0: if (!(value inside {"DEV0","DEV1"}))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
            "FIFO EPN peer must be DEV0 or DEV1", UVM_NONE, `__FILE__, `__LINE__);
        1: if (!(value inside {"partial","exact","capacity_plus_one"}))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
            "Unknown or empty FIFO EPN image variant", UVM_NONE, `__FILE__, `__LINE__);
        2: begin
          negatives++;
          if (negatives > 1 || !(value inside {"full","blocked","overlap","release"}))
            uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
              "Select one valid FIFO EPN rejection operand", UVM_NONE, `__FILE__, `__LINE__);
          mode = value;
        end
        3: if (!(value inside {"BULK","INTERRUPT","ISOCHRONOUS"}))
          uvm_pkg::uvm_report_fatal("OCP_FIFO_EPN_GUARD",
            "Unknown or empty EPN transfer type", UVM_NONE, `__FILE__, `__LINE__);
      endcase
    end
    return mode;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    canary_mode = ocp_check_control_args(1);
  endfunction

  function bit ocp_check_canary(string gate);
    if (canary_mode != gate) return 0;
    if (canary_applied || !experiment_armed || dma_released || epn == null)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Rejection operand lacks unique owned held experiment")
    canary_applied = 1;
    `uvm_info("OCP_FIFO_EPN_CANARY",$sformatf(
      "gate=%s epoch=%0d generation=%0d",gate,
      model.control[1].epoch,model.control[1].generation),UVM_NONE)
    return 1;
  endfunction

  function void ocp_configure_experiment(bytes_t image_bytes);
    epn = model.ocp_get_epn(epn_device);
    if (experiment_armed || ocp_cfg == null || epn == null || !epn.enabled ||
        !epn.configured || !model.fifo_discovered || model.accepted_bytes != 0 ||
        image_bytes.size() <= model.fifo_depth_words*4)
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Fresh discovered FIFO and enabled discovered EPN profile required")
    expected_image = image_bytes;
    experiment_armed = 1;
    `uvm_info("OCP_FIFO_EPN_PLAN",$sformatf(
      "peer_slot=%0d capacity_words=%0d image_words=%0d max_write=%0d max_transfer_words=%0d",
      epn_device,model.fifo_depth_words,image_bytes.size()/4,model.max_write,
      model.fifo_max_words),UVM_NONE)
  endfunction

  function void ocp_check_held_window();
    usb_ocp_base_control c;
    c = model.control[1];
    if (!blocked_seen || !dma_hold_entered || dma_released || actual_dma_bytes != 0 ||
        model.returned_bytes != 0 || model.accepted_bytes != model.fifo_depth_words*4 ||
        !full_prefix_seen || !full_status_seen || c.active !== 1 || c.status_acked !== 0 ||
        c.address !== blocked_address || c.epoch != blocked_epoch ||
        c.generation != blocked_generation || c.setup !== blocked_setup || c.data.size() != 0)
      `uvm_fatal("OCP_FIFO_EPN_OVERLAP", "Lost exact full/blocked/held zero-DMA OCP window")
    ocp_check_no_dma_admission();
  endfunction

  function void ocp_check_no_dma_admission();
    usb_ocp_event actual;
    // Address admission is already passively captured by the ordinary AXI
    // callback. An unfinished read cannot hide behind completion latency.
    foreach (observer.accepted_axi[key]) begin
      actual = observer.accepted_axi[key];
      if (actual.manager == 0 && !actual.write_access &&
          model.recovery_register.exists(actual.axi_address) &&
          model.recovery_register[actual.axi_address] == "INDIRECT_FIFO_DATA")
        `uvm_fatal("OCP_FIFO_EPN_DMA", "FIFO DMA address admitted while first-DMA hold is owned")
    end
  endfunction

  function void ocp_check_sram(usb_ocp_event item);
    usb_ocp_base_epn_model ledger;
    usb_ep_entry_t actual_entry;
    usb_ep_entry_t expected_entry;
    usb_direction_e direction;
    bytes_t expected;
    logic [63:0] offset;
    logic [31:0] buffer_address;
    int phase;
    int byte_offset;
    ledger = model.ocp_get_epn(epn_device);
    // SRAM preparation can precede SET_INTERFACE status and bus enable.
    if (ledger == null || item.manager != ((epn_device == 1) ? 1 : 3) ||
        !item.write_access) return;
    offset = item.axi_address-ledger.memory_base;
    for (int dir = 0; dir < 2; dir++) begin
      if (ledger.discovery.endpoints[dir] == null) continue;
      phase = sram_phase[dir];
      direction = dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT;
      buffer_address = usb_ocp_base_epn_profile::ocp_get_buffer(direction);
      if (offset >= buffer_address && offset < buffer_address+64) begin
        expected = usb_ocp_base_epn_profile::ocp_prepare_stream(
          direction,phase,ledger.payload_lengths[dir][phase],ledger.data_tag);
        byte_offset = int'(offset-buffer_address);
        if (phase > 1 || byte_offset != sram_bytes[dir] ||
            byte_offset >= expected.size() || item.response_ok !== 1 ||
            item.axi_beats != 1 || item.bytes.size() != 4 || item.strobes.size() != 4)
          `uvm_fatal("OCP_FIFO_EPN_SRAM", "EPN initialization lacks exact ordered DWORD context")
        foreach (item.bytes[i])
          if (item.strobes[i] !== 1 || item.bytes[i] !==
              ((dir && byte_offset+i < expected.size()) ? expected[byte_offset+i] : 8'hee))
            `uvm_fatal("OCP_FIFO_EPN_SRAM", "EPN initialized payload/padding/strobes differ")
        sram_bytes[dir] += 4;
      end
      if (offset == ledger.list_base+ledger.discovery.endpoints[dir].entry_offset() &&
          item.bytes.size() == 4) begin
        actual_entry = model.ocp_get_le32(item.bytes,0);
        if (actual_entry.active !== 1) continue;
        if (phase > 1)
          `uvm_fatal("OCP_FIFO_EPN_SRAM", "Extra EPN arm")
        expected = usb_ocp_base_epn_profile::ocp_prepare_stream(
          direction,phase,ledger.payload_lengths[dir][phase],ledger.data_tag);
        expected_entry = '0;
        expected_entry.active = 1;
        expected_entry.nbytes = 15'(expected.size());
        expected_entry.buffer_offset = 11'(buffer_address >> 6);
        expected_entry.ep_type =
          (ledger.discovery.endpoints[dir].transfer_type != USB_TRANSFER_TYPE_BULK);
        expected_entry.toggle_value =
          (ledger.discovery.endpoints[dir].transfer_type == USB_TRANSFER_TYPE_INTERRUPT);
        if (item.response_ok !== 1 || item.axi_beats != 1 || item.strobes.size() != 4 ||
            actual_entry !== expected_entry || sram_bytes[dir] != ((expected.size()+3)/4)*4)
          `uvm_fatal("OCP_FIFO_EPN_SRAM", "EPN arm precedes initialized buffer or differs from exact entry")
        foreach (item.strobes[i])
          if (item.strobes[i] !== 1)
            `uvm_fatal("OCP_FIFO_EPN_SRAM", "EPN arm requires all byte lanes")
        sram_armed[dir][phase] = 1;
        sram_phase[dir]++;
        sram_bytes[dir] = 0;
      end
    end
  endfunction

  virtual function void ocp_check_event_before(usb_ocp_event item);
    usb_ocp_base_control c;
    usb_ocp_event t;
    int unsigned expected_generation;
    // Buffer service can precede the image; retain both read/write phases.
    if (item.kind == usb_ocp_event::AXI_COMPLETED) ocp_check_sram(item);
    if (!experiment_armed) return;
    accepted_before_event = model.accepted_bytes;
    data_before_event = model.candidate;
    c = model.control[1];
    t = model.token;
    if (blocked_seen && !dma_released) begin
      ocp_check_held_window();
      // No unrelated EP0 SETUP, including a peer SETUP, earns EPN credit.
      if (item.kind == usb_ocp_event::USB_PACKET && item.host_tx === 1 &&
          item.pid == svt_usb_packet::SETUP)
        `uvm_fatal("OCP_FIFO_EPN_OVERLAP", "Unrelated SETUP inside owned blocked window")
    end
    if (item.kind == usb_ocp_event::AXI_COMPLETED && item.manager == 0 &&
        !item.write_access && model.recovery_register.exists(item.axi_address) &&
        model.recovery_register[item.axi_address] == "INDIRECT_FIFO_DATA") begin
      if (!dma_released || !proof_consumed || !overlap_joined || !dma_hold_entered ||
          item.response_ok !== 1 || item.axi_burst !== AAXI_BURST_FIXED ||
          item.axi_beat_bytes != 4 || item.bytes.size() != item.axi_beats*4 ||
          item.axi_address_order_floor < release_order || item.axi_address_at < release_at)
        `uvm_fatal("OCP_FIFO_EPN_DMA", "DMA precedes consumed held proof or lacks FIXED DWORD context")
      actual_dma_bytes += item.bytes.size();
      if (first_dma_order == 0) begin
        first_dma_order = item.order;
        first_dma_address_floor = item.axi_address_order_floor;
      end
    end
    // USB2 8.5.1/8.5.3: not STATUS NAK, submission, pause, or NYET.
    if (item.kind != usb_ocp_event::USB_PACKET || item.pid != svt_usb_packet::NAK ||
        t == null || t.endpoint !== 0 || model.token_device != 1 ||
        !(t.pid inside {svt_usb_packet::OUT,svt_usb_packet::PING}) ||
        c.active !== 1 || c.setup[0] !== 8'h21 ||
        c.ocp_get_value() !== 16'(OCP_CMD_INDIRECT_FIFO_DATA) ||
        !full_status_seen || dma_released) return;
    if (item.host_tx !== 0 || item.packet_valid !== 1 ||
        t.packet_valid !== 1 || t.host_tx !== 1 || t.address !== c.address ||
        model.token_epoch != c.epoch || model.token_generation != c.generation ||
        c.status_acked !== 0 || c.ocp_get_length() != 4 || c.data.size() != 0 ||
        model.accepted_bytes != model.fifo_depth_words*4 || actual_dma_bytes != 0 ||
        model.returned_bytes != 0 || !dma_hold_entered)
      `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "NAK lacks full capacity, hold and original DATA-stage identity")
    if (t.pid == svt_usb_packet::OUT) begin
      if (model.candidate == null || model.candidate.pid != svt_usb_packet::DATA1 ||
          model.candidate.bytes.size() != 4)
        `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "OUT/NAK lacks attempted capacity+1 DWORD")
      foreach (model.candidate.bytes[i])
        if (model.candidate.bytes[i] !== expected_image[model.fifo_depth_words*4+i])
          `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "Rejected DWORD differs from next image bytes")
      nak_count++;
    end else begin
      if (ocp_cfg.full_speed || model.candidate != null)
        `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "PING is not a legal HS DATA-stage query")
      ping_nak_count++;
    end
    expected_generation = c.generation;
    if (!blocked_seen && ocp_check_canary("blocked")) expected_generation++;
    if (model.token_generation != expected_generation)
      `uvm_fatal("OCP_FIFO_EPN_BLOCKED", "NAK lacks full capacity, hold and original DATA-stage identity")
    if (!blocked_seen) begin
      blocked_seen = 1;
      blocked_epoch = c.epoch;
      blocked_generation = c.generation;
      blocked_address = c.address;
      blocked_setup = c.setup;
      blocked_order = item.order;
      `uvm_info("OCP_FIFO_EPN_BLOCKED",$sformatf(
        "%s/NAK addr=%0d epoch=%0d generation=%0d order=%0d accepted=%0d DMA=%0d",
        t.pid.name(),c.address,c.epoch,c.generation,item.order,
        model.accepted_bytes,actual_dma_bytes),UVM_NONE)
    end
  endfunction

  virtual function void ocp_check_event_after(usb_ocp_event item);
    usb_ocp_base_control c;
    int expected_full_bytes;
    int expected_generation;
    c = model.control[1];
    if (!experiment_armed) return;
    if (model.accepted_bytes > expected_image.size())
      `uvm_fatal("OCP_FIFO_EPN_IMAGE", "Accepted bytes exceed exact image")
    if (model.accepted_bytes > accepted_before_event) begin
      if (data_before_event == null ||
          data_before_event.bytes.size() != model.accepted_bytes-accepted_before_event)
        `uvm_fatal("OCP_FIFO_EPN_IMAGE", "Acceptance lacks exact passive DATA snapshot")
      foreach (data_before_event.bytes[i])
        if (data_before_event.bytes[i] !== expected_image[accepted_before_event+i])
          `uvm_fatal("OCP_FIFO_EPN_IMAGE", "Accepted bytes duplicated, missing, reordered or corrupt")
      if (!dma_released && model.accepted_bytes > model.fifo_depth_words*4)
        `uvm_fatal("OCP_FIFO_EPN_CAPACITY", "Accepted beyond full capacity while DMA held")
      if (!full_prefix_seen && model.accepted_bytes == model.fifo_depth_words*4 &&
          actual_dma_bytes == 0 && model.returned_bytes == 0) begin
        full_prefix_seen = 1;
        full_order = item.order;
        `uvm_info("OCP_FIFO_EPN_CAPACITY",$sformatf(
          "All advertised words=%0d accepted at order=%0d with zero DMA",
          model.fifo_depth_words,full_order),UVM_NONE)
      end
      if (accepted_before_event == model.fifo_depth_words*4) begin
        if (!dma_released || !proof_consumed || retry_accepted ||
            c.address !== blocked_address || c.epoch != blocked_epoch ||
            c.generation != blocked_generation || c.setup !== blocked_setup ||
            data_before_event.bytes.size() != 4)
          `uvm_fatal("OCP_FIFO_EPN_RETRY", "Next bytes do not belong to naturally retried original blocked request")
        retry_accepted = 1;
        retry_order = item.order;
        retry_data_order = data_before_event.order;
      end
    end
    if (item.kind == usb_ocp_event::USB_TRANSFER && item.endpoint === 0 &&
        item.setup[0] === 8'ha1 && item.setup[2] === OCP_CMD_INDIRECT_FIFO_STATUS &&
        item.transfer_ok === 1 && full_prefix_seen && !dma_released) begin
      if (item.address !== model.address[1] ||
          model.transfer_crosschecks[1] != model.usb_completions[1] ||
          model.accepted_bytes != model.fifo_depth_words*4 || model.returned_bytes != 0 ||
          actual_dma_bytes != 0 || !dma_hold_entered ||
          item.bytes.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS ||
          item.bytes[0] !== OCP_IFS_FULL_MASK)
        `uvm_fatal("OCP_FIFO_EPN_CAPACITY", "Full prefix lacks consumed exact native/packet full status")
      ocp_check_no_dma_admission();
      expected_full_bytes = model.fifo_depth_words*4;
      if (!full_status_seen && ocp_check_canary("full")) expected_full_bytes += 4;
      if (model.accepted_bytes != expected_full_bytes)
        `uvm_fatal("OCP_FIFO_EPN_CAPACITY", "Full prefix lacks consumed exact native/packet full status")
      full_status_seen = 1;
      `uvm_info("OCP_FIFO_EPN_FULL_STATUS", "Consumed native and packet FIFO_STATUS proves full capacity",UVM_NONE)
    end
    if (blocked_seen && !dma_released) begin
      ocp_check_held_window();
      for (int dir = 0; dir < 2; dir++) begin
        if (epn.accepted[dir] == 2 &&
            (epn.accepted_token[dir][1] <= blocked_order ||
             epn.accepted_data[dir][1] <= blocked_order ||
             epn.accepted_order[dir][1] <= blocked_order ||
             epn.accepted_generation[dir][1] != blocked_generation))
          `uvm_fatal("OCP_FIFO_EPN_OVERLAP", "Write-phase EPN acceptance is outside owned blocked generation")
        if (item.kind == usb_ocp_event::USB_TRANSFER && item.address === epn.address &&
            item.endpoint === 4'(epn.discovery.endpoints[dir].ep_number) &&
            item.transfer_type === epn.ocp_get_transfer_type(dir)) begin
          if (overlap_actual[dir] != null || epn.crosschecked[dir] != 2 ||
              item.transfer_start_order <= blocked_order)
            `uvm_fatal("OCP_FIFO_EPN_OVERLAP", "Native EPN completion lacks unique held-window submission/acceptance")
          overlap_actual[dir] = item;
        end
      end
      // Native completion and firmware AXI callbacks may arrive in either
      // order. Join only consumed ledgers, not host return or queue intent.
      if (!overlap_joined && overlap_actual[0] != null && overlap_actual[1] != null &&
          epn.ocp_check_drained() && sram_armed[0][1] && sram_armed[1][1] &&
          deferred_axi.size() == 0) begin
        expected_generation = blocked_generation;
        if (ocp_check_canary("overlap")) expected_generation++;
        if (epn.accepted_generation[0][1] != expected_generation ||
            epn.accepted_generation[1][1] != expected_generation)
          `uvm_fatal("OCP_FIFO_EPN_OVERLAP", "Write-phase EPN acceptance is outside owned blocked generation")
        overlap_joined = 1;
        proof_order = item.order;
        for (int dir = 0; dir < 2; dir++)
          held_service_cov.sample(epn_device,int'(epn.discovery.endpoints[dir].transfer_type),dir);
        `uvm_info("OCP_FIFO_EPN_JOIN",$sformatf(
          "peer=%0d epoch=%0d generation=%0d blocked=%0d proof=%0d native=%0d/%0d accepted=%p monitor=%p SRAM=%p DMA=%0d",
          epn_device,blocked_epoch,blocked_generation,blocked_order,proof_order,
          overlap_actual[0].order,overlap_actual[1].order,epn.accepted,
          epn.crosschecked,epn.memory_checked,actual_dma_bytes),UVM_NONE)
      end
    end
    if (item.kind == usb_ocp_event::USB_TRANSFER && blocked_seen && !retry_native &&
        item.endpoint === 0 && item.address === blocked_address &&
        item.setup === blocked_setup) begin
      if (!retry_accepted || !dma_released ||
          c.epoch != blocked_epoch || c.generation != blocked_generation ||
          c.status_acked !== 1 || item.transfer_ok !== 1 ||
          item.transfer_start_order >= blocked_order ||
          model.transfer_crosschecks[1] != model.usb_completions[1])
        `uvm_fatal("OCP_FIFO_EPN_RETRY", "Blocked request lacks same-generation successful STATUS/native completion")
      retry_native = 1;
      native_order = item.order;
    end
    // Do not impose callback-order causality: real AXI completion may follow
    // the retry ACK/native callback. Neither alone grants retry/drain credit.
    if (!retry_joined && retry_accepted && retry_native && first_dma_order != 0 &&
        model.returned_bytes >= 64 && model.compared_bytes >= 64 &&
        deferred_axi.size() == 0) begin
      if (first_dma_address_floor > retry_data_order)
        `uvm_fatal("OCP_FIFO_EPN_RETRY", "Original request accepted DATA before real DMA address admission")
      retry_joined = 1;
      `uvm_info("OCP_FIFO_EPN_RETRY",$sformatf(
        "Original epoch=%0d generation=%0d retried=%0d DATA=%0d native=%0d DMA_address_floor=%0d first_DMA=%0d accepted=%0d returned=%0d compared=%0d",
        blocked_epoch,blocked_generation,retry_order,retry_data_order,native_order,
        first_dma_address_floor,first_dma_order,
        model.accepted_bytes,model.returned_bytes,model.compared_bytes),UVM_NONE)
    end
  endfunction

  task ocp_check_proof_barrier(bit retry_proof = 0);
    bit ready;
    if (ocp_cfg == null || (retry_proof ? !dma_released : dma_released))
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Invalid owned checker proof barrier")
    ready = 0;
    fork
      begin
        fork
          begin
            wait ((retry_proof ? retry_joined : overlap_joined) &&
                  !busy && deferred_axi.size() == 0);
            ready = 1;
          end
          begin #(witness_timeout); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (!ready)
      `uvm_fatal("OCP_FIFO_EPN_WAIT",$sformatf(
        "Consumed proof timeout retry=%0b full=%0b blocked=%0b overlap=%0b native=%0b/%0b SRAM=%p DMA=%0d accepted=%0d returned=%0d compared=%0d; remaining obligations retained",
        retry_proof,full_status_seen,blocked_seen,overlap_joined,
        overlap_actual[0] != null,overlap_actual[1] != null,
        epn.memory_checked,actual_dma_bytes,model.accepted_bytes,
        model.returned_bytes,model.compared_bytes))
    if (!retry_proof) begin
      ocp_check_held_window();
      if (proof_consumed)
        `uvm_fatal("OCP_FIFO_EPN_GUARD", "Duplicate release proof consumption")
      proof_consumed = 1;
    end
    `uvm_info("OCP_FIFO_EPN_PROOF_BARRIER",$sformatf(
      "retry=%0b proof_order=%0d consumed=%0b pending_AXI=%0d",
      retry_proof,proof_order,proof_consumed,deferred_axi.size()),UVM_NONE)
  endtask

  function void ocp_check_release_dma();
    int expected_proofs;
    ocp_check_held_window();
    if (!overlap_joined || !proof_consumed || busy || deferred_axi.size() != 0 ||
        !epn.ocp_check_drained() || proof_order <= blocked_order)
      `uvm_fatal("OCP_FIFO_EPN_BARRIER", "Release precedes consumed packet/native/SRAM proof")
    expected_proofs = 1;
    if (ocp_check_canary("release")) expected_proofs++;
    if (int'(proof_consumed) != expected_proofs)
      `uvm_fatal("OCP_FIFO_EPN_BARRIER", "Release precedes consumed packet/native/SRAM proof")
    release_order = observer.next_order;
    release_at = $realtime;
    dma_released = 1;
    `uvm_info("OCP_FIFO_EPN_RELEASE", "Release planned first-DMA hold; original request must naturally retry",UVM_NONE)
  endfunction

  virtual function void ocp_check_replacements();
    if (canary_mode != "")
      `uvm_fatal("OCP_FIFO_EPN_GUARD", "Selected rejection control reached final checks without rejection")
    if (!experiment_armed || !full_prefix_seen || !full_status_seen || !blocked_seen ||
        !overlap_joined || !proof_consumed || !dma_released || !retry_joined ||
        actual_dma_bytes != expected_image.size() || model.accepted_bytes != expected_image.size() ||
        model.dev0_ep0_read_replacements != 0 || model.dev0_ep0_write_replacements != 0 ||
        model.replacement_crosschecks != 0 || deferred_transfer_aborts.size() != 0 ||
        !epn.ocp_check_drained() ||
        !(full_order < blocked_order && blocked_order < proof_order &&
          proof_order < release_order && release_order <= first_dma_order &&
          release_order <= retry_order))
      `uvm_fatal("OCP_FIFO_EPN_INCOMPLETE", "Missing full/blocked/held EPN/retry/exact DMA obligations")
    `uvm_info("OCP_FIFO_EPN_EVIDENCE",$sformatf(
      "peer=%0d type=%s OUT_NAK=%0d PING_NAK=%0d full=%0d blocked=%0d proof=%0d release=%0d first_DMA=%0d retry=%0d native=%0d image_bytes=%0d DMA=%0d",
      epn_device,epn.discovery.endpoints[0].transfer_type.name(),nak_count,ping_nak_count,
      full_order,blocked_order,proof_order,release_order,first_dma_order,retry_order,
      native_order,expected_image.size(),actual_dma_bytes),UVM_NONE)
  endfunction
endclass
