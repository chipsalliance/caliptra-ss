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

class usb_ocp_scoreboard extends uvm_component;
  `uvm_component_utils(usb_ocp_scoreboard)
  typedef logic [7:0] bytes_t[$];
  usb_ocp_observer observer;
  usb_ocp_predictor model;
  usb_ocp_suspend_model l2_model;
  usb_ocp_event deferred_axi[$];
  usb_ocp_event deferred_transfer_aborts[$];
  int unsigned event_count;
  logic busy;
  bit negative_payload;
  bit negative_activation;
  bit negative_dma;
  bit negative_overlap;
  bit negative_replacement;
  bit negative_abort_prefix;
  bit negative_payload_applied;
  bit negative_epn_overlap;
  bit negative_epn_payload;
  bit negative_epn_native;
  bit negative_epn_nak;
  bit negative_mixed_peer;

  covergroup mixed_stream_cov with function sample(int device, int stream_phase, int direction);
    option.per_instance = 1;
    device_cp: coverpoint device { bins dev0 = {1}; bins dev1 = {2}; }
    phase_cp: coverpoint stream_phase { bins read_window = {0}; bins write_window = {1}; }
    direction_cp: coverpoint direction { bins out_stream = {0}; bins in_stream = {1}; }
    streams: cross device_cp, phase_cp, direction_cp;
  endgroup

  function new(string name = "usb_ocp_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    event_count = 0;
    busy = 0;
    mixed_stream_cov = new();
    mixed_stream_cov.option.weight = 0;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    model = usb_ocp_predictor::type_id::create("model");
    negative_payload = $test$plusargs("usb_ocp_negative_payload");
    negative_activation = $test$plusargs("usb_ocp_negative_activation");
    negative_dma = $test$plusargs("usb_ocp_negative_dma");
    negative_overlap = $test$plusargs("usb_ocp_negative_overlap");
    negative_replacement = $test$plusargs("usb_ocp_negative_replacement");
    negative_abort_prefix = $test$plusargs("usb_ocp_negative_abort_prefix");
    negative_epn_overlap = $test$plusargs("usb_ocp_negative_epn_overlap");
    negative_epn_payload = $test$plusargs("usb_ocp_negative_epn_payload");
    negative_epn_native = $test$plusargs("usb_ocp_negative_epn_native");
    negative_epn_nak = $test$plusargs("usb_ocp_negative_epn_nak");
    negative_mixed_peer = $test$plusargs("usb_ocp_negative_mixed_peer");
    if (negative_payload || negative_activation || negative_dma || negative_overlap ||
        negative_replacement || negative_abort_prefix || negative_epn_overlap ||
        negative_epn_payload || negative_epn_native || negative_epn_nak || negative_mixed_peer)
      `uvm_info("OCP_NEGATIVE_CONTROL", "Checker-only negative control enabled; this run MUST fail", UVM_NONE)
  endfunction

  function void ocp_check_bytes(bytes_t actual, bytes_t expected, string label);
    if (actual.size() != expected.size())
      `uvm_fatal("OCP_RESPONSE", $sformatf("%s length actual=%0d expected=%0d",
                 label, actual.size(), expected.size()))
    foreach (expected[i])
      if (actual[i] !== expected[i])
        `uvm_fatal("OCP_RESPONSE", $sformatf("%s byte %0d actual=%02h expected=%02h",
                   label, i, actual[i], expected[i]))
  endfunction

  function void ocp_check_discovery(bytes_t data);
    int unsigned pos;
    int unsigned interfaces;
    int unsigned functions;
    logic associated;
    logic [7:0] iface;
    int unsigned rd;
    int unsigned wr;
    if (data.size() < 9 || data[0] !== 9 || data[1] !== 2 ||
        {data[3],data[2]} !== data.size())
      `uvm_fatal("OCP_DISCOVERY", "Malformed configuration descriptor")
    pos = 9;
    interfaces = 0;
    functions = 0;
    associated = 0;
    while (pos < data.size()) begin
      if (data[pos] < 2 || pos + data[pos] > data.size())
        `uvm_fatal("OCP_DISCOVERY", "Descriptor length crosses configuration boundary")
      if (data[pos+1] == 4) begin
        associated = 0;
        if (data[pos] != 9) `uvm_fatal("OCP_DISCOVERY", "Interface length is not nine")
        if (data[pos+5] === 8'hef && data[pos+6] === 8'h08 &&
            data[pos+7] === 8'h01) begin
          if (data[pos+3] !== 0 || data[pos+4] !== 0)
            `uvm_fatal("OCP_DISCOVERY", "OCP interface has alternate setting or EPN")
          interfaces++;
          associated = 1;
          iface = data[pos+2];
        end
      end
      if (data[pos+1] == OCP_USB_FUNC_DESC_TYPE && associated) begin
        if (data[pos] != OCP_USB_FUNC_DESC_LEN ||
            data[pos+2] !== OCP_USB_FUNC_DESC_SUBTYPE || data[pos+3] !== 0 ||
            {data[pos+9],data[pos+8]} !== OCP_USB_BCD_VERSION_1P1)
          `uvm_fatal("OCP_DISCOVERY", "Invalid OCP functional descriptor")
        wr = {data[pos+5],data[pos+4]};
        rd = {data[pos+7],data[pos+6]};
        if (rd < OCP_USB_MIN_TRANSFER_SIZE || wr < OCP_USB_MIN_TRANSFER_SIZE)
          `uvm_fatal("OCP_DISCOVERY", "OCP advertised limits below minimum")
        functions++;
      end
      pos += data[pos];
    end
    if (interfaces != 1 || functions != 1)
      `uvm_fatal("OCP_DISCOVERY", "OCP interface/associated functional descriptor is not unique")
    // Validate before committing discovery into the predictor.
    model.interface_number = iface;
    model.max_read = rd;
    model.max_write = wr;
    model.discovery_seen = 1;
  endfunction

  function void ocp_check_capabilities(bytes_t data);
    logic [15:0] caps;
    if (data.size() != OCP_SPEC_LEN_PROT_CAP)
      `uvm_fatal("OCP_CAP", "PROT_CAP length mismatch")
    foreach (OCP_SPEC_PROT_CAP_MAGIC[i])
      if (data[i] !== OCP_SPEC_PROT_CAP_MAGIC[i])
        `uvm_fatal("OCP_CAP", "PROT_CAP magic mismatch")
    caps = {data[11],data[10]};
    if (data[8] !== OCP_SPEC_VERSION_MAJOR || data[9] !== OCP_SPEC_VERSION_MINOR ||
        (caps & OCP_CAP_RESERVED_MASK) !== 0 ||
        !caps[OCP_CAP_IDENTIFICATION] || !caps[OCP_CAP_DEVICE_STATUS] ||
        !caps[OCP_CAP_PUSH_C_IMAGE] || !caps[OCP_CAP_INDIRECT_FIFO] ||
        data[12] == 0)
      `uvm_fatal("OCP_CAP", "Required OCP FIFO/push capabilities absent or malformed")
    if (!caps[OCP_CAP_INDIRECT_CTRL])
      `uvm_error("OCP_CAP_INDIRECT_CTRL", $sformatf(
        "OCP 1.1 Section 9.2 requires INDIRECT_CTRL with Push C-image; capabilities=0x%04h. Continuing with advertised INDIRECT_FIFO.", caps))
    model.cms_count = data[12];
    model.capabilities_seen = 1;
  endfunction

  function void ocp_check_fifo_status(bytes_t data);
    int unsigned depth;
    int unsigned max_words;
    int unsigned wr;
    int unsigned rd;
    int unsigned occupancy;
    if (!model.capabilities_seen || data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)
      `uvm_fatal("OCP_FIFO_STATUS", "FIFO status without capability or wrong length")
    foreach (data[i])
      if ($isunknown(data[i]))
        `uvm_fatal("OCP_FIFO_STATUS", "Unknown FIFO status byte")
    if (data[3] !== 0 || data[2] !== 0 ||
        (data[0] & OCP_IFS_STATUS_RSVD_MASK) !== 0 || (data[0][0] && data[0][1]))
      `uvm_fatal("OCP_FIFO_STATUS", "Invalid reserved bits or full/empty flags")
    if (model.fifo_discovered && data[1] !== OCP_REGION_RECOVERY_CODE_WO)
      `uvm_fatal("OCP_FIFO_STATUS", "Selected recovery FIFO changed region type")
    // OCP 1.1 8.2.5/9.2: a CMS scan may encounter a memory window (reported
    // as unsupported here), log FIFO, or vendor FIFO before recovery storage.
    // Unsupported-region geometry is not a usable FIFO geometry.
    if (data[1] === OCP_REGION_UNSUPPORTED) return;
    if (!(data[1] inside {OCP_REGION_RECOVERY_CODE_WO,OCP_REGION_DEBUG_LOG_RO,
                         OCP_REGION_VENDOR_WO,OCP_REGION_VENDOR_RO}))
      `uvm_fatal("OCP_FIFO_STATUS", "Reserved FIFO region type")
    depth = model.ocp_get_le32(data,12);
    max_words = model.ocp_get_le32(data,16);
    wr = model.ocp_get_le32(data,4);
    rd = model.ocp_get_le32(data,8);
    if (depth == 0 || max_words == 0 || wr >= depth || rd >= depth ||
        ((wr == rd) != (data[0][0] || data[0][1])))
      `uvm_fatal("OCP_FIFO_STATUS", "Invalid FIFO bounds or index/flag consistency")
    // Non-target FIFOs may legitimately contain data. Validate their shape,
    // but do not initialize or alter the recovery FIFO geometry/byte ledger.
    if (data[1] !== OCP_REGION_RECOVERY_CODE_WO) return;
    if (!model.fifo_discovered) begin
      if (wr != 0 || rd != 0 || data[0] !== OCP_IFS_EMPTY_MASK)
        `uvm_fatal("OCP_FIFO_STATUS", "FIFO not empty before initial image")
    end else begin
      if (depth != model.fifo_depth_words || max_words != model.fifo_max_words)
        `uvm_fatal("OCP_FIFO_STATUS", "FIFO geometry changed")
      // Pending-image L2 also reads live status between completed CONTROLs.
      occupancy = (model.accepted_bytes - model.returned_bytes)/4;
      if (occupancy > depth || wr != (model.accepted_bytes/4)%depth ||
          rd != (model.returned_bytes/4)%depth ||
          data[0][0] !== (occupancy == 0) || data[0][1] !== (occupancy == depth))
        `uvm_fatal("OCP_FIFO_STATUS", "FIFO indices/occupancy differ from accepted USB and AXI ledger")
    end
    // Full capacity is depth, including equal indices while full.
    model.fifo_depth_words = depth;
    model.fifo_max_words = max_words;
    model.fifo_discovered = 1;
  endfunction

  function void ocp_check_status_version(usb_ocp_base_control c, logic [31:0] actual);
    logic found;
    if (!c.status_read || !c.status_frozen || c.status_versions.size() == 0 ||
        c.status_data_order <= c.status_setup_order)
      `uvm_fatal("OCP_STATUS", "Status read lacks a frozen, independently established expectation")
    found = 0;
    foreach (c.status_versions[i]) begin
      // The first entry is the latest version at SETUP, or the first
      // completed write within that read. Every additional entry must be an
      // overlapping update. No write at/after response DATA is admissible.
      if (c.status_versions[i].valid !== 1'b1 ||
          c.status_versions[i].order >= c.status_data_order ||
          (i != 0 && c.status_versions[i].order <= c.status_setup_order))
        `uvm_fatal("OCP_STATUS", "Status expectation version lies outside this read's observation interval")
      if (i != 0 && c.status_versions[i].order <= c.status_versions[i-1].order)
        `uvm_fatal("OCP_STATUS", "Read status versions are not strictly ordered")
      if (actual === c.status_versions[i].value) found = 1;
    end
    if (!found)
      `uvm_fatal("OCP_STATUS",$sformatf(
        "Stale/unprogrammed status cmd=%02h epoch=%0d generation=%0d SETUP=%0d DATA=%0d actual=%08h versions=%p",
        c.setup[2],c.epoch,c.generation,c.status_setup_order,c.status_data_order,
        actual,c.status_versions))
  endfunction

  function void ocp_check_control(int device);
    usb_ocp_base_control c;
    usb_ocp_base_epn_model epn;
    c = model.control[device];
    epn = model.ocp_get_epn(device);
    if (c.setup[0][7] && c.expected.size() != 0)
      ocp_check_bytes(c.data,c.expected,"standard control response");
    if (c.setup[1] === 6 && c.setup[0][6:5] === 0) begin
      if (c.setup[3] == 1) begin
        if (c.data.size() != 18 || c.data[0] !== 18 || c.data[1] !== 1 ||
            c.data[7] !== 64 || c.data[17] !== 1)
          `uvm_fatal("OCP_DESCRIPTOR", "Device descriptor malformed")
        if (device == 0 && c.data[4] !== 9)
          `uvm_fatal("OCP_DESCRIPTOR", "Upstream device is not a hub")
        if (device == 0 && (!model.hub_identity_programmed ||
            model.ocp_get_le32(c.data,8) !== model.hub_identity_expected))
          `uvm_fatal("OCP_DESCRIPTOR", "Hub identity differs from accepted AXI descriptor programming")
        model.device_identity[device] = model.ocp_get_le32(c.data,8);
        foreach (model.device_descriptor_seen[i])
          if (i != device && model.device_descriptor_seen[i] &&
              model.device_identity[i] === model.device_identity[device])
            `uvm_fatal("OCP_DESCRIPTOR", "Hub/dev0/dev1 identities are not unique")
        model.device_descriptor_seen[device] = 1;
      end
      if (c.setup[3] == 2 && c.data.size() > 9) begin
        if (c.data[0] !== 9 || c.data[1] !== 2 ||
            {c.data[3],c.data[2]} !== c.data.size() || c.data[5] !== 1)
          `uvm_fatal("OCP_DESCRIPTOR", "Configuration descriptor malformed")
        model.config_descriptor_seen[device] = 1;
        if (device == 1) ocp_check_discovery(c.data);
        if (epn != null) epn.discovery.ocp_check_parse(c.data);
      end
    end
    if (device == 0 && c.setup[0] === 8'ha0 && c.setup[1] === 6) begin
      if (c.data.size() != 9 || c.data[0] !== 9 || c.data[1] !== 8'h29 ||
          c.data[2] !== 2)
        `uvm_fatal("OCP_DESCRIPTOR", "Hub does not expose two ports")
      model.hub_descriptor_seen = 1;
    end
    if (device == 1 && c.setup[0] === 8'ha1) begin
      case (c.setup[2])
        OCP_CMD_PROT_CAP: ocp_check_capabilities(c.data);
        OCP_CMD_INDIRECT_FIFO_CTRL: begin
          if (l2_model == null)
            `uvm_fatal("OCP_MODEL", "Unmodeled bringup OCP read")
          // OCP 1.1 9.2: readback is checked against accepted USB programming,
          // not a RAL reset value or a host-to-firmware side channel.
          if (c.data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL ||
              c.data[0] !== model.selected_cms || c.data[1] !== 0 ||
              model.ocp_get_le32(c.data,2) !== model.image_words)
            `uvm_error("OCP_L2_RETENTION", "USB image control readback lost accepted CMS/image length")
        end
        OCP_CMD_INDIRECT_FIFO_STATUS: ocp_check_fifo_status(c.data);
        OCP_CMD_DEVICE_STATUS: begin
          if (c.data.size() != OCP_SPEC_MIN_LEN_DEVICE_STATUS ||
              c.data[1] !== OCP_PROTOCOL_ERROR_NONE || c.data[6] !== 0)
            `uvm_fatal("OCP_STATUS", "Malformed DEVICE_STATUS or protocol error")
          ocp_check_status_version(c,{c.data[3],c.data[2],c.data[1],c.data[0]});
          if (c.data[OCP_OFF_DS_STATUS] === OCP_DEVICE_STATUS_RECOVERY_MODE)
            model.recovery_mode_seen = 1;
          if (c.data[0] === OCP_DEVICE_STATUS_RECOVERY_PENDING) model.pending_seen = 1;
          if (c.data[0] === OCP_DEVICE_STATUS_RUNNING_RECOVERY) begin
            if (!model.activation_observed || !model.activation_cleared)
              `uvm_fatal("OCP_ACTIVATION", "Final status without fresh AXI activation/clear")
            model.final_status_seen = 1;
          end
        end
        OCP_CMD_RECOVERY_STATUS: begin
          if (c.data.size() != OCP_SPEC_LEN_RECOVERY_STATUS)
            `uvm_fatal("OCP_STATUS", "RECOVERY_STATUS length mismatch")
          ocp_check_status_version(c,{16'b0,c.data[1],c.data[0]});
        end
        OCP_CMD_RECOVERY_CTRL: begin
          if (c.data.size() != OCP_SPEC_LEN_RECOVERY_CTRL ||
              {c.data[2],c.data[1],c.data[0]} !== model.recovery_ctrl)
            `uvm_fatal("OCP_ACTIVATION", "USB RECOVERY_CTRL differs from independently predicted control")
          if (model.activation_cleared && c.data[2] === 0) model.clear_seen = 1;
        end
        default: `uvm_fatal("OCP_MODEL", "Unmodeled bringup OCP read")
      endcase
    end
  endfunction

  function void ocp_check_fifo_bytes();
    logic [7:0] expected;
    logic [7:0] actual;
    while (model.fifo_expected.size() != 0 && model.fifo_actual.size() != 0) begin
      expected = model.fifo_expected.pop_front();
      actual = model.fifo_actual.pop_front();
      if (negative_payload && !negative_payload_applied) begin
        actual ^= 8'h01;
        negative_payload_applied = 1;
      end
      if (actual !== expected)
        `uvm_fatal("OCP_IMAGE", $sformatf("Byte %0d actual=%02h expected=%02h",
                   model.compared_bytes,actual,expected))
      model.compared_bytes++;
    end
  endfunction

  function void ocp_check_axi(usb_ocp_event item);
    logic [31:0] word;
    string reg_name;
    int dev;
    if (!item.response_ok)
      `uvm_fatal("OCP_AXI", "Completed AXI response is not OKAY")
    foreach (model.epn_models[i])
      if (model.epn_models[i] != null) model.epn_models[i].ocp_check_axi(item);
    word = model.ocp_get_le32(item.bytes,0);
    if (item.manager inside {0,2} && item.write_access) begin
      dev = (item.manager == 0) ? 0 : 1;
      if (item.axi_address == model.device_command_address[dev])
        model.device_prepared[dev] =
          ((word & (model.device_enable_mask[dev] | model.device_connect_mask[dev])) ===
                   (model.device_enable_mask[dev] | model.device_connect_mask[dev]));
    end
    if (item.manager != 0) return;
    if (item.axi_address == model.hub_identity_address && item.write_access) begin
      model.hub_identity_expected = word;
      model.hub_identity_programmed = 1;
    end
    if (item.axi_address == model.hub_control_address && item.write_access) begin
      if ((word & model.hub_connect_mask) != 0) begin
        if (!model.hub_enabled || !model.device_prepared[0] || !model.device_prepared[1])
          `uvm_fatal("OCP_HUB", "HUB_CONNECT before prior HUB_EN/both prepared devices")
        model.hub_connected = 1;
      end
      if ((word & model.hub_enable_mask) != 0) model.hub_enabled = 1;
    end
    if (!model.recovery_register.exists(item.axi_address)) return;
    reg_name = model.recovery_register[item.axi_address];
    if ((item.axi_beats != 1 || item.bytes.size() != 4) &&
        (item.write_access || reg_name != "INDIRECT_FIFO_DATA"))
      `uvm_fatal("OCP_AXI", "Only FIFO DMA reads may use multi-beat recovery accesses")
    if (item.write_access) begin
      case (reg_name)
        "DEVICE_STATUS_0": begin
          if (word[7:0] === OCP_DEVICE_STATUS_RECOVERY_PENDING &&
              (model.returned_bytes == 0 || model.returned_bytes != model.image_words*4))
            `uvm_fatal("OCP_PENDING", "Firmware Pending before exact image consumption")
          if (word[7:0] === OCP_DEVICE_STATUS_RUNNING_RECOVERY && !model.activation_observed)
            `uvm_fatal("OCP_ACTIVATION", "Firmware final status before fresh activation")
        end
        "RECOVERY_CTRL": begin
          if (word[23:16] !== 0)
            `uvm_fatal("OCP_OWNERSHIP", "Firmware must not synthesize activation")
          if (model.activation_request) begin
            if (!model.activation_observed)
              `uvm_fatal("OCP_ACTIVATION", "Firmware clear before fresh AXI activation read")
            model.activation_cleared = 1;
          end
          model.recovery_ctrl = word[23:0];
        end
        default: begin end
      endcase
    end else begin
      case (reg_name)
        "INDIRECT_FIFO_DATA": begin
          int unsigned remaining;
          int unsigned expected_words;
          int unsigned observed_words;
          if (model.returned_bytes >= model.image_words*4 ||
              item.axi_burst !== AAXI_BURST_FIXED)
            `uvm_fatal("OCP_DMA", "FIFO DMA overread or non-FIXED burst")
          remaining = model.image_words-model.returned_bytes/4;
          expected_words = (remaining > 16) ? 16 : remaining;
          observed_words = item.axi_beats;
          if (negative_dma) observed_words--;
          if (observed_words != expected_words)
            `uvm_fatal("OCP_DMA", $sformatf(
              "FIFO DMA burst differs from 64-byte/tail contract: observed=%0d expected=%0d",
              observed_words,expected_words))
          foreach (item.bytes[i]) model.fifo_actual.push_back(item.bytes[i]);
          model.returned_bytes += item.bytes.size();
          ocp_check_fifo_bytes();
        end
        "INDIRECT_FIFO_CTRL_1": begin
          if (word != 0) begin
            if (word !== model.image_words)
              `uvm_fatal("OCP_SIZE", "AXI image size differs from accepted USB command")
            model.image_size_reads++;
          end
        end
        "INDIRECT_FIFO_CTRL_0": begin
          if (word[15:0] !== {8'h00,model.selected_cms})
            `uvm_fatal("OCP_CONTROL", "AXI FIFO control differs from accepted USB command")
          model.control_reads++;
        end
        "RECOVERY_CTRL": begin
          if (!model.activation_request) begin
            if (word[23:0] !== model.recovery_ctrl)
              `uvm_fatal("OCP_ACTIVATION", "Activation baseline differs from firmware programming")
            if (word[23:16] === 0) model.baseline_zero = 1;
          end else if (word[23:16] === OCP_RC_ACTIVATE_CODE) begin
            if (!model.baseline_zero || word[23:0] !== model.recovery_ctrl)
              `uvm_fatal("OCP_ACTIVATION", "Stale/wrong AXI activation")
            if (!negative_activation) model.activation_observed = 1;
          end
        end
        default: begin end
      endcase
    end
  endfunction

  function bit ocp_check_replaced_transfer(usb_ocp_event item);
    int device;
    int index;
    usb_ocp_base_control c;
    logic [7:0] expected_byte;
    device = -1;
    index = -1;
    foreach (model.replaced_controls[d,i])
      if (model.replaced_controls[d][i].address === item.address &&
          model.replaced_controls[d][i].setup === item.setup &&
          item.transfer_start_order < model.replaced_controls[d][i].replaced_at) begin
        if (device != -1)
          `uvm_fatal("OCP_SUPERSESSION", "Ambiguous replaced monitor-transfer identity")
        device = d;
        index = i;
      end
    if (device == -1) return 0;
    c = model.replaced_controls[device][index];
    if (c.status_acked)
      `uvm_fatal("OCP_SUPERSESSION", "Replaced transfer was already STATUS-complete")
    // An aborted OUT descriptor may retain unaccepted payload. Only the
    // ACK-qualified packet prefix can advance the host's image offset.
    if (item.bytes.size() < c.data.size())
      `uvm_fatal("OCP_SUPERSESSION", "Native abort snapshot omits ACK-qualified bytes")
    foreach (c.data[i]) begin
      expected_byte = c.data[i];
      if (negative_abort_prefix && !c.setup[0][7] && i == 0)
        expected_byte ^= 8'h01;
      if (item.bytes[i] !== expected_byte)
        `uvm_fatal("OCP_SUPERSESSION",$sformatf(
          "Replaced packet/transfer prefix differs: byte=%0d expected=%02h actual=%02h negative_abort_prefix=%0b",
          i,expected_byte,item.bytes[i],negative_abort_prefix))
    end
    if (model.checked_replacement_valid[device])
      `uvm_fatal("OCP_SUPERSESSION", "Prior checked prefix was not consumed")
    model.checked_replacement_bytes[device] = c.data;
    model.checked_replacement_serial[device] = item.transfer_serial;
    model.checked_replacement_valid[device] = 1;
    model.replaced_controls[device].delete(index);
    model.replacement_crosschecks++;
    `uvm_info("OCP_SUPERSESSION",$sformatf(
      "Checked replaced control slot=%0d generation=%0d accepted_bytes=%0d native_ok=%0b results=%h",
      device,c.generation,c.data.size(),item.transfer_ok,item.results),UVM_LOW)
    return 1;
  endfunction

  function void ocp_check_transfer(usb_ocp_event item);
    int device;
    usb_ocp_base_control c;
    usb_ocp_base_epn_model epn;
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed_results;
    if (item.transfer_type != svt_usb_transfer::CONTROL_TRANSFER) begin
      device = model.ocp_find_device(item.address);
      epn = model.ocp_get_epn(device);
      if (epn == null) `uvm_fatal("OCP_EPN_CORRELATION", "Unexpected EPN transfer")
      epn.ocp_check_transfer(item);
      return;
    end
    allowed_results = 0;
    if (!item.setup[0][7]) allowed_results[5] = 1;
    if (item.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1) begin
      allowed_results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] = 1;
      if (item.transfer_ok || !model.require_dev0_ep0_replacement || item.endpoint !== 0 ||
          item.address !== model.address[1] ||
          !(item.setup[0] inside {8'ha1,8'h21}) ||
          !(item.setup[2] inside {OCP_CMD_PROT_CAP,OCP_CMD_INDIRECT_FIFO_DATA}) ||
          (item.results & ~allowed_results) !== 0)
        `uvm_fatal("OCP_SUPERSESSION", "Unexpected native abort or additional transfer failure")
      if (ocp_check_replaced_transfer(item)) return;
      c = model.control[1];
      if (!c.active || c.address !== item.address || c.setup !== item.setup)
        `uvm_fatal("OCP_SUPERSESSION", "Native abort lacks a pending matching control context")
      if (deferred_transfer_aborts.size() >= 16384)
        `uvm_fatal("OCP_SUPERSESSION", "Unproved native-abort queue exceeded bound")
      // The monitor may end before the new SETUP. Retain the actual until
      // accepted wire supersession permits its mandatory prefix cross-check.
      deferred_transfer_aborts.push_back(item);
      return;
    end
    // SET_ADDRESS completes at the old address, retained in control context.
    device = -1;
    foreach (model.control[i])
      if (model.control[i].status_acked && model.control[i].address === item.address &&
          model.control[i].setup === item.setup &&
          model.transfer_crosschecks[i] < model.usb_completions[i]) device = i;
    if (device < 0)
      `uvm_fatal("OCP_CROSSCHECK", "Transfer completion has no matching ACK-qualified control")
    c = model.control[device];
    allowed_results = 0;
    // SVT results bit 5 also describes the IN status ZLP after control-OUT data.
    if (!c.setup[0][7]) allowed_results[5] = 1;
    if (!item.transfer_ok || (item.results & ~allowed_results) !== 0)
      `uvm_fatal("OCP_CROSSCHECK", "VIP control transfer failed")
    ocp_check_bytes(item.bytes,c.data,"packet/transfer cross-check");
    model.transfer_crosschecks[device]++;
  endfunction

  task run_phase(uvm_phase phase);
    usb_ocp_event item;
    usb_ocp_event axi;
    int device;
    if (observer == null) `uvm_fatal("OCP_SCOREBOARD", "Missing observer")
    forever begin
      observer.ocp_wait_snapshot(item);
      busy = 1;
      event_count++;
      case (item.kind)
        usb_ocp_event::USB_PACKET: begin
          if (l2_model != null) l2_model.ocp_capture_packet(item);
          model.ocp_observe_packet(item);
        end
        usb_ocp_event::USB_TRANSFER: begin
          ocp_check_transfer(item);
          if (l2_model != null) l2_model.ocp_capture_transfer(item);
        end
        usb_ocp_event::AXI_COMPLETED: begin
          // Record status expectation evidence now, in observer order. Do not
          // let the later ledger flush move a write backward across USB DATA.
          // FIFO/activation accounting still consumes every deferred actual.
          model.ocp_record_status_programming(item);
          if (l2_model != null) l2_model.ocp_capture_axi(item);
          if (deferred_axi.size() >= 16384)
            `uvm_fatal("OCP_DRAIN", "Deferred completed-AXI queue exceeded bound")
          deferred_axi.push_back(item);
        end
      endcase
      for (int i = 0; i < deferred_transfer_aborts.size();) begin
        if (ocp_check_replaced_transfer(deferred_transfer_aborts[i]))
          deferred_transfer_aborts.delete(i);
        else i++;
      end
      // Hardware may expose a received OUT DWORD before its ACK finishes on
      // the wire. Retain the completed AXI actual, then compare after the
      // transaction's acceptance decision; never discard an early result.
      if (model.token == null) begin
        while (deferred_axi.size() != 0) begin
          axi = deferred_axi.pop_front();
          ocp_check_axi(axi);
        end
      end
      ocp_check_fifo_bytes();
      while (model.ready_controls.size() != 0) begin
        device = model.ready_controls.pop_front();
        ocp_check_control(device);
      end
      busy = 0;
    end
  endtask

  function bit ocp_check_drained();
    foreach (model.epn_models[i])
      if (model.epn_models[i] != null && !model.epn_models[i].ocp_check_drained()) return 0;
    if (busy || !observer.ocp_check_drained() || deferred_axi.size() != 0 ||
        deferred_transfer_aborts.size() != 0 ||
        model.token != null || model.ready_controls.size() != 0 ||
        model.fifo_expected.size() != 0 || model.fifo_actual.size() != 0) return 0;
    foreach (model.control[i])
      if (model.control[i].active ||
          model.replaced_controls[i].size() != 0 ||
          model.checked_replacement_valid[i] ||
          model.transfer_crosschecks[i] != model.usb_completions[i]) return 0;
    return 1;
  endfunction

  function void ocp_check_replacements();
    if (!model.require_dev0_ep0_replacement) return;
    if (negative_replacement)
      model.dev0_ep0_write_replacements = 0;
    if (model.dev0_ep0_read_replacements == 0 ||
        model.dev0_ep0_write_replacements == 0 ||
        model.replacement_crosschecks != model.dev0_ep0_read_replacements +
                                        model.dev0_ep0_write_replacements)
      `uvm_fatal("OCP_SUPERSESSION",$sformatf(
        "Missing ACK-qualified replacement or prefix cross-check: read=%0d write=%0d crosschecks=%0d negative=%0b",
        model.dev0_ep0_read_replacements,model.dev0_ep0_write_replacements,
        model.replacement_crosschecks,negative_replacement))
    if (model.replaced_controls[1].size() != 0 ||
        model.checked_replacement_valid[1] || deferred_transfer_aborts.size() != 0)
      `uvm_fatal("OCP_SUPERSESSION", "Replacement phase has unconsumed control/prefix obligations")
  endfunction

  function void ocp_check_mixed_windows();
    bit peer_seen;
    if (!model.require_mixed_epn) return;
    peer_seen = (model.epn_models[1] != null);
    if (negative_mixed_peer) peer_seen = 0;
    if (!peer_seen || model.epn_models[0] == null ||
        !model.require_dev0_ep0_replacement ||
        model.mixed_generation[0] == 0 ||
        model.mixed_generation[1] <= model.mixed_generation[0])
      `uvm_fatal("OCP_MIXED_PEER", "Missing required paired-device original-control proof")
    foreach (model.epn_models[port])
      for (int dir = 0; dir < 2; dir++)
        for (int stream_phase = 0; stream_phase < 2; stream_phase++) begin
          if (model.epn_models[port].device != port+1 ||
              model.epn_models[port].accepted_generation[dir][stream_phase] !=
                model.mixed_generation[stream_phase])
            `uvm_fatal("OCP_MIXED_WINDOW", "Mixed stream belongs to the wrong device or original generation")
          mixed_stream_cov.sample(port+1,stream_phase,dir);
        end
    if (mixed_stream_cov.get_inst_coverage() != 100.0)
      `uvm_fatal("OCP_MIXED_COVERAGE", "Mixed device/phase/direction coverage is incomplete")
    `uvm_info("OCP_MIXED_EVIDENCE",$sformatf(
      "Both device IN/OUT ledgers match original generations=%p; replacements=%0d/%0d; mixed coverage=%0.1f",
      model.mixed_generation,model.dev0_ep0_read_replacements,
      model.dev0_ep0_write_replacements,mixed_stream_cov.get_inst_coverage()),UVM_LOW)
  endfunction

  function void ocp_check_complete();
    bit read_epn_window_seen;
    bit write_epn_window_seen;
    usb_ocp_base_epn_model epn;
    if (l2_model != null) l2_model.ocp_check_complete();
    if ($test$plusargs("usb_ocp_control_zlp_canary")) begin
      if (model.control_data_stage_errors != 1)
        `uvm_fatal("OCP_CONTROL_DATA_CANARY", $sformatf(
          "Expected one excess control DATA error, observed=%0d",model.control_data_stage_errors))
      `uvm_info("OCP_CONTROL_DATA_CANARY", "Checked one excess accepted control DATA transaction", UVM_NONE)
    end
    ocp_check_replacements();
    // Remove only a private write-window check operand for this injection.
    // Canonical packet snapshots, acceptance counters, and SRAM proof survive.
    foreach (model.epn_models[port]) begin
      epn = model.epn_models[port];
      if (epn == null) continue;
      read_epn_window_seen = (epn.accepted[0] >= 1 && epn.accepted[1] >= 1);
      write_epn_window_seen = (epn.accepted[0] == 2 && epn.accepted[1] == 2);
      if (negative_epn_overlap) write_epn_window_seen = 0;
      if (!read_epn_window_seen || !write_epn_window_seen || !epn.ocp_check_drained())
        `uvm_fatal("OCP_EPN_OVERLAP", "Missing checked IN/OUT EPN overlap in both OCP windows")
      `uvm_info("OCP_EPN_EVIDENCE",$sformatf(
        "slot=%0d type=%s accepted=%p monitor=%p SRAM=%p token_orders=%p data_orders=%p generations=%p SOFs=%p",
        epn.device,epn.discovery.endpoints[0].transfer_type.name(),
        epn.accepted,epn.crosschecked,epn.memory_checked,
        epn.accepted_token,epn.accepted_data,
        epn.accepted_generation,epn.accepted_sof),UVM_LOW)
    end
    ocp_check_mixed_windows();
    // Checker-only injection removes write-window evidence, not USB stimulus
    // or mandatory packet/transfer checks.
    if (model.require_dev1_ep0_overlap && negative_overlap)
      model.dev1_ep0_write_overlap = 0;
    if (model.require_dev1_ep0_overlap &&
        (model.dev1_ep0_read_overlap == 0 ||
         model.dev1_ep0_write_overlap == 0 || observer.reordered_completions == 0))
      `uvm_fatal("OCP_OVERLAP", $sformatf(
        "Missing wire overlap or reordered routing: read_tokens=%0d write_tokens=%0d reordered=%0d negative=%0b",
        model.dev1_ep0_read_overlap,model.dev1_ep0_write_overlap,
        observer.reordered_completions,negative_overlap))
    if (!ocp_check_drained() || event_count == 0 || observer.packet_count == 0 ||
        !model.hub_enabled || !model.hub_connected || !model.hub_descriptor_seen ||
        !model.discovery_seen || !model.capabilities_seen || !model.fifo_discovered ||
        !model.recovery_mode_seen || !model.baseline_zero ||
        !model.pending_seen || !model.activation_request ||
        !model.activation_status_acked || !model.activation_observed ||
        !model.activation_cleared || !model.clear_seen || !model.final_status_seen ||
        model.accepted_bytes == 0 || model.accepted_bytes != model.returned_bytes ||
        model.compared_bytes != model.accepted_bytes ||
        model.accepted_bytes != model.image_words*4 ||
        model.image_size_reads == 0 || model.control_reads == 0)
      `uvm_fatal("OCP_INCOMPLETE", "Missing image, discovery, activation, or drained checker evidence")
    foreach (model.enumerated[i])
      if (!model.enumerated[i] || !model.device_descriptor_seen[i] ||
          !model.config_descriptor_seen[i] || model.transfer_crosschecks[i] == 0)
        `uvm_fatal("OCP_INCOMPLETE", $sformatf("Device %0d not fully enumerated/checked",i))
    `uvm_info("OCP_EVIDENCE",$sformatf(
      "packets=%0d transfers=%p axi=%p accepted=%0d returned=%0d compared=%0d recovery_mode=%0b fresh_activation=%0b",
      observer.packet_count,model.transfer_crosschecks,observer.axi_count,
      model.accepted_bytes,model.returned_bytes,model.compared_bytes,
      model.recovery_mode_seen,model.activation_observed),UVM_LOW)
    if (model.require_dev1_ep0_overlap)
      `uvm_info("OCP_OVERLAP",$sformatf(
        "Checked dev1 EP0 inside OCP read/write windows: read_tokens=%0d write_tokens=%0d reordered=%0d",
        model.dev1_ep0_read_overlap,model.dev1_ep0_write_overlap,
        observer.reordered_completions),UVM_LOW)
    if (model.require_dev0_ep0_replacement)
      `uvm_info("OCP_SUPERSESSION",$sformatf(
        "Checked native same-EP0 replacement: read=%0d write=%0d crosschecks=%0d",
        model.dev0_ep0_read_replacements,model.dev0_ep0_write_replacements,
        model.replacement_crosschecks),UVM_LOW)
  endfunction
endclass
