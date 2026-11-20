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

class usb_ocp_predictor extends uvm_object;
  `uvm_object_utils(usb_ocp_predictor)
  // OCP Recovery 1.1 9.2, RECOVERY_CTRL image-selection/activation codes.
  localparam logic [7:0] OCP_RC_IMAGE_SEL_NONE = 8'h00;
  localparam logic [7:0] OCP_RC_NO_ACTIVATE_CODE = 8'h00;
  typedef logic [7:0] bytes_t[$];
  typedef usb_ocp_base_control::status_version_t status_version_t;
  localparam int unsigned STATUS_VERSION_LIMIT = 64;

  // Completed-write evidence is ordered independently of the deferred AXI
  // ledger. Only the latest version survives between USB reads.
  status_version_t current_status[2];
  status_version_t setup_status_versions[2][$];

  usb_ocp_base_control control[3];
  usb_ocp_base_control replaced_controls[3][$];
  logic [6:0] address[3] = '{0,126,127};
  int unsigned default_device;
  int unsigned ready_controls[$];
  usb_ocp_event token;
  usb_ocp_event candidate;
  int unsigned token_device;
  int unsigned token_epoch;
  int unsigned token_generation;
  int unsigned usb_completions[3];
  int unsigned control_data_stage_errors = 0;
  int unsigned transfer_crosschecks[3];
  logic enumerated[3];
  logic device_descriptor_seen[3];
  logic [31:0] device_identity[3];
  logic config_descriptor_seen[3];
  logic hub_descriptor_seen;
  logic hub_enabled;
  logic hub_connected;
  logic device_prepared[2];
  logic [31:0] hub_enable_mask;
  logic [31:0] hub_connect_mask;
  logic [63:0] hub_control_address;
  logic [63:0] hub_identity_address;
  logic [31:0] hub_identity_expected;
  logic hub_identity_programmed;
  logic [63:0] device_command_address[2];
  logic [31:0] device_enable_mask[2];
  logic [31:0] device_connect_mask[2];
  string recovery_register[logic [63:0]];

  // Recovery domain: never cleared by ocp_cancel_usb_epoch().
  logic [7:0] fifo_expected[$];
  logic [7:0] fifo_actual[$];
  int unsigned accepted_bytes;
  int unsigned returned_bytes;
  int unsigned compared_bytes;
  logic [31:0] image_words;
  logic [7:0] selected_cms;
  logic [23:0] recovery_ctrl;
  logic baseline_zero;
  logic activation_request;
  logic activation_status_acked;
  logic activation_observed;
  logic activation_cleared;
  logic recovery_mode_seen;
  logic pending_seen;
  logic final_status_seen;
  logic clear_seen;
  logic capabilities_seen;
  logic discovery_seen;
  logic fifo_discovered;
  logic [7:0] interface_number;
  int unsigned max_read;
  int unsigned max_write;
  int unsigned cms_count;
  int unsigned fifo_depth_words;
  int unsigned fifo_max_words;
  int unsigned image_size_reads;
  int unsigned control_reads;
  bit require_dev1_ep0_overlap;
  int unsigned dev1_ep0_read_overlap;
  int unsigned dev1_ep0_write_overlap;
  bit require_dev0_ep0_replacement;
  int unsigned dev0_ep0_read_replacements;
  int unsigned dev0_ep0_write_replacements;
  int unsigned replacement_crosschecks;
  bytes_t checked_replacement_bytes[3];
  longint unsigned checked_replacement_serial[3];
  bit checked_replacement_valid[3];
  bit reset_commit_at_status;
  usb_ocp_base_epn_model epn_models[2];
  usb_ocp_base_epn_profile epn_profiles[2];
  bit require_mixed_epn;
  bit full_speed;
  usb_ocp_protocol_stall_model stall_model;
  int unsigned mixed_generation[2];

  function new(string name = "usb_ocp_predictor");
    super.new(name);
    foreach (control[i])
      control[i] = usb_ocp_base_control::type_id::create($sformatf("control%0d", i));
    foreach (current_status[i]) begin
      current_status[i].valid = 0;
      current_status[i].value = 0;
      current_status[i].version = 0;
      current_status[i].order = 0;
      current_status[i].observed_at = 0;
    end
    default_device = 0;
    usb_completions = '{default:0};
    transfer_crosschecks = '{default:0};
    enumerated = '{default:0};
    device_descriptor_seen = '{default:0};
    config_descriptor_seen = '{default:0};
    device_prepared = '{default:0};
    hub_descriptor_seen = 0;
    hub_enabled = 0;
    hub_connected = 0;
    hub_identity_programmed = 0;
    accepted_bytes = 0;
    returned_bytes = 0;
    compared_bytes = 0;
    image_words = 0;
    selected_cms = 0;
    recovery_ctrl = 0;
    baseline_zero = 0;
    activation_request = 0;
    activation_status_acked = 0;
    activation_observed = 0;
    activation_cleared = 0;
    recovery_mode_seen = 0;
    pending_seen = 0;
    final_status_seen = 0;
    clear_seen = 0;
    capabilities_seen = 0;
    discovery_seen = 0;
    fifo_discovered = 0;
    max_read = 0;
    max_write = 0;
    cms_count = 0;
    fifo_depth_words = 0;
    fifo_max_words = 0;
    image_size_reads = 0;
    control_reads = 0;
    require_dev1_ep0_overlap = 0;
    dev1_ep0_read_overlap = 0;
    dev1_ep0_write_overlap = 0;
    require_dev0_ep0_replacement = 0;
    dev0_ep0_read_replacements = 0;
    dev0_ep0_write_replacements = 0;
    replacement_crosschecks = 0;
    checked_replacement_valid = '{default:0};
  endfunction

  function void ocp_configure_map(usb_reg_model ral);
    uvm_reg regs[$];
    ral.combo.recovery.get_registers(regs);
    foreach (regs[i])
      recovery_register[regs[i].get_address(ral.combo_map)] = regs[i].get_name();
    hub_control_address = ral.combo.hub.CONTROL.get_address(ral.combo_map);
    hub_identity_address = ral.combo.hub.DESCRIPTOR_LOW.m_mem.get_address(2,ral.combo_map);
    hub_enable_mask = 32'(1) << ral.combo.hub.CONTROL.ENABLE.get_lsb_pos();
    hub_connect_mask = 32'(1) << ral.combo.hub.CONTROL.DCON.get_lsb_pos();
    device_command_address[0] = ral.combo.dev0_csr.DEVCMDSTAT.get_address(ral.combo_map);
    device_command_address[1] = ral.dev1_csr.DEVCMDSTAT.get_address(ral.dev1_csr_map);
    device_enable_mask[0] = 32'(1) << ral.combo.dev0_csr.DEVCMDSTAT.DEV_EN.get_lsb_pos();
    device_enable_mask[1] = 32'(1) << ral.dev1_csr.DEVCMDSTAT.DEV_EN.get_lsb_pos();
    device_connect_mask[0] = 32'(1) << ral.combo.dev0_csr.DEVCMDSTAT.DCON.get_lsb_pos();
    device_connect_mask[1] = 32'(1) << ral.dev1_csr.DEVCMDSTAT.DCON.get_lsb_pos();
  endfunction

  static function logic [31:0] ocp_get_le32(bytes_t bytes, int offset);
    if (offset + 4 > bytes.size())
      `uvm_fatal("OCP_LENGTH", "DWORD beyond payload boundary")
    return {bytes[offset+3],bytes[offset+2],bytes[offset+1],bytes[offset]};
  endfunction

  // OCP 1.1 9.2: DEVICE_STATUS and RECOVERY_STATUS describe current status,
  // not any value previously programmed. AW/submitted intent is not evidence.
  function void ocp_record_status_programming(usb_ocp_event item);
    int status_index;
    logic [7:0] command;
    logic [31:0] word;
    usb_ocp_base_control c;
    if (item.manager != 0 || !item.write_access ||
        !recovery_register.exists(item.axi_address)) return;
    case (recovery_register[item.axi_address])
      "DEVICE_STATUS_0": begin status_index = 0; command = OCP_CMD_DEVICE_STATUS; end
      "RECOVERY_STATUS": begin status_index = 1; command = OCP_CMD_RECOVERY_STATUS; end
      default: return;
    endcase
    if (item.response_ok !== 1'b1 || item.bytes.size() != 4 ||
        item.strobes.size() != 4)
      `uvm_fatal("OCP_STATUS", "Status version requires a completed successful DWORD write")
    foreach (item.strobes[i])
      if (item.strobes[i] !== 8'h01)
        `uvm_fatal("OCP_STATUS", "Status programming requires all DWORD byte lanes")
    word = ocp_get_le32(item.bytes,0);
    if ($isunknown(word))
      `uvm_fatal("OCP_STATUS", "Unknown firmware status programming")
    if (current_status[status_index].valid &&
        item.order <= current_status[status_index].order)
      `uvm_fatal("OCP_STATUS", "Status programming is not in observer order")
    current_status[status_index].valid = 1;
    current_status[status_index].value = (status_index == 0) ? word : {16'b0,word[15:0]};
    current_status[status_index].version++;
    current_status[status_index].order = item.order;
    current_status[status_index].observed_at = item.observed_at;

    // Keep provisional versions across SETUP DATA/ACK, but do not supersede
    // the prior control until the new SETUP is accepted.
    if (token != null && token.pid == svt_usb_packet::SETUP && token_device == 1) begin
      if (setup_status_versions[status_index].size() >= STATUS_VERSION_LIMIT)
        `uvm_fatal("OCP_STATUS", "SETUP status-version window exceeded bound")
      setup_status_versions[status_index].push_back(current_status[status_index]);
    end
    c = control[1];
    if (c.active && c.status_read && !c.status_frozen && c.setup[2] === command) begin
      if (c.status_versions.size() >= STATUS_VERSION_LIMIT)
        `uvm_fatal("OCP_STATUS", "Read status-version window exceeded bound")
      c.status_versions.push_back(current_status[status_index]);
    end
  endfunction

  // USB 2.0 9.1.1.3: only USB transfer state belongs to this epoch.
  function void ocp_cancel_usb_epoch(int device);
    control[device].epoch++;
    control[device].active = 0;
    control[device].status_acked = 0;
    control[device].data.delete();
    control[device].expected.delete();
    control[device].status_versions.delete();
    control[device].status_read = 0;
    control[device].status_frozen = 0;
    if (token != null && token_device == device) begin
      foreach (setup_status_versions[i]) setup_status_versions[i].delete();
      token = null;
      candidate = null;
    end
  endfunction

  function usb_ocp_base_epn_model ocp_get_epn(int device);
    if (!(device inside {0,1,2}))
      `uvm_fatal("OCP_EPN_PROFILE", "Invalid passive endpoint slot")
    if (device == 0) return null;
    return epn_models[device-1];
  endfunction

  function void ocp_configure_epn_profile(usb_ocp_base_epn_profile profile,
      logic [31:0] list_base, logic [63:0] memory_base, bit negative_payload);
    usb_ocp_base_epn_model epn;
    if (profile == null)
      `uvm_fatal("OCP_EPN_PROFILE", "Missing passive endpoint profile")
    if (!(profile.device inside {1,2}) || ocp_get_epn(profile.device) != null)
      `uvm_fatal("OCP_EPN_PROFILE", "Invalid or duplicate passive endpoint ownership")
    epn = usb_ocp_base_epn_model::type_id::create("epn_model");
    epn.device = profile.device;
    epn.data_tag = profile.data_tag;
    for (int dir = 0; dir < 2; dir++)
      for (int phase = 0; phase < 2; phase++)
        epn.payload_lengths[dir][phase] = profile.ocp_get_payload_length(
          dir ? USB_DIRECTION_IN : USB_DIRECTION_OUT,phase);
    epn.full_speed = profile.full_speed;
    epn.discovery.full_speed = profile.full_speed;
    epn.list_base = list_base;
    epn.memory_base = memory_base;
    epn.negative_payload = negative_payload;
    epn_models[profile.device-1] = epn;
    epn_profiles[profile.device-1] = profile;
  endfunction

  function int ocp_find_device(logic [6:0] addr);
    if (addr === 0) return default_device;
    foreach (address[i]) if (address[i] === addr) return i;
    `uvm_fatal("OCP_CONTEXT", $sformatf("Unknown USB address %0d", addr))
    return 0;
  endfunction

  function void ocp_prepare_response(int device);
    usb_ocp_base_control c;
    usb_ocp_base_epn_model epn;
    c = control[device];
    epn = ocp_get_epn(device);
    c.expected.delete();
    if (c.setup[0] === 8'h80) begin
      case (c.setup[1])
        6: if (device != 0) begin
             if (epn_profiles[device-1] != null)
               c.expected = epn_profiles[device-1].ocp_prepare_descriptor(device,c.ocp_get_value());
             else
               c.expected = usb_ocp_base_descriptors::ocp_prepare_descriptor(device,c.ocp_get_value());
           end
        8: c.expected.push_back(c.configuration);
        0: if (device != 0) c.expected = '{0,0};
        default: begin end
      endcase
      while (c.expected.size() > c.ocp_get_length()) void'(c.expected.pop_back());
    end
    // USB 2.0 9.4.4/9.4.10: only configured, advertised interfaces/alternates.
    if (epn != null && device == epn.device && c.setup[0] inside {8'h81,8'h01}) begin
      if (!epn.configured || c.ocp_get_index() !== {8'b0,epn.discovery.interface_number})
        `uvm_fatal("OCP_EPN_INTERFACE", "Interface request before configuration or wrong identity")
      if (c.setup[0] === 8'h81) begin
        if (c.setup[1] !== svt_usb_types::GET_INTERFACE ||
            c.ocp_get_value() !== 0 || c.ocp_get_length() !== 1)
          `uvm_fatal("OCP_EPN_INTERFACE", "Malformed GET_INTERFACE")
        c.expected = '{epn.active_alternate};
      end else if (c.setup[1] !== svt_usb_types::SET_INTERFACE || c.ocp_get_length() !== 0 ||
                   !(c.ocp_get_value() inside {16'd0,{8'b0,epn.discovery.alternate}}))
        `uvm_fatal("OCP_EPN_INTERFACE", "SET_INTERFACE selected an unadvertised alternate")
    end
    // OCP requests must use only wire-discovered limits and interface.
    if (device == 1 && c.setup[0] inside {8'h21,8'ha1}) begin
      if (!discovery_seen || c.setup[1] !== OCP_BREQUEST_XFER ||
          c.setup[3] !== 0 || c.setup[4] !== interface_number || c.setup[5] !== 0 ||
          (c.setup[0][7] && c.ocp_get_length() != max_read) ||
          (!c.setup[0][7] && c.ocp_get_length() > max_write))
        `uvm_fatal("OCP_REQUEST", "OCP 8.5.1 request violates validated discovery")
      if (c.setup[2] === OCP_CMD_PROT_CAP && !recovery_mode_seen)
        `uvm_fatal("OCP_READY", "PROT_CAP before USB-observed Recovery Mode")
    end
  endfunction

  function void ocp_accept_setup(int device, usb_ocp_event data);
    usb_ocp_base_control c;
    usb_ocp_base_control fresh;
    c = control[device];
    if (data.bytes.size() != 8 || data.pid != svt_usb_packet::DATA0)
      `uvm_fatal("OCP_SETUP", "SETUP requires eight DATA0 bytes")
    if (require_dev0_ep0_replacement && device == 1 && c.active &&
        c.setup[0] inside {8'ha1,8'h21} && data.bytes[0][6:5] === 0) begin
      if (replaced_controls[device].size() >= 16384)
        `uvm_fatal("OCP_SUPERSESSION", "Uncrosschecked replaced-control queue exceeded bound")
      // Freeze the old ACK-qualified data only when the replacement SETUP
      // itself is ACKed. A native abort alone cannot retire DUT obligations.
      c.replaced_at = token.order;
      c.active = 0;
      replaced_controls[device].push_back(c);
      if (c.setup[0][7]) dev0_ep0_read_replacements++;
      else dev0_ep0_write_replacements++;
      fresh = usb_ocp_base_control::type_id::create("replacement_control");
      fresh.epoch = c.epoch;
      fresh.generation = c.generation;
      fresh.configuration = c.configuration;
      control[device] = fresh;
      c = fresh;
    end
    // USB 2.0 5.5.5 cancels the control operation on a new SETUP.
    // The recovery contract retains ACK/NYET-accepted FIFO bytes below.
    c.generation++;
    c.active = 1;
    c.status_acked = 0;
    c.data.delete();
    c.compared = 0;
    c.address = token.address;
    c.next_toggle = '{1'b1,1'b1};
    foreach (c.setup[i]) c.setup[i] = data.bytes[i];
    c.status_versions.delete();
    c.status_frozen = 0;
    c.status_setup_order = token.order;
    c.status_data_order = 0;
    c.status_read = (device == 1 && c.setup[0] === 8'ha1 &&
                    c.setup[2] inside {OCP_CMD_DEVICE_STATUS,OCP_CMD_RECOVERY_STATUS});
    if (c.status_read)
      c.status_versions = setup_status_versions[(c.setup[2] === OCP_CMD_RECOVERY_STATUS) ? 1 : 0];
    foreach (setup_status_versions[i]) setup_status_versions[i].delete();
    ocp_prepare_response(device);
    if (stall_model != null) stall_model.ocp_capture_setup(device,c);
  endfunction

  function void ocp_accept_out(int device, usb_ocp_event data);
    usb_ocp_base_control c;
    c = control[device];
    if (device == 1 && c.setup[0] === 8'h21) begin
      if (c.setup[2] === OCP_CMD_INDIRECT_FIFO_DATA) begin
        if (!fifo_discovered || image_words == 0 ||
            c.ocp_get_length() > fifo_max_words*4 ||
            accepted_bytes + data.bytes.size() > image_words*4)
          `uvm_fatal("OCP_FIFO", "FIFO write exceeds discovery/image bounds")
        foreach (data.bytes[i]) fifo_expected.push_back(data.bytes[i]);
        accepted_bytes += data.bytes.size();
      end
      if (c.data.size() == c.ocp_get_length() && !reset_commit_at_status) begin
        case (c.setup[2])
          OCP_CMD_INDIRECT_FIFO_CTRL: begin
            if (c.data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL ||
                c.data[1] !== 0 || accepted_bytes != 0)
              `uvm_fatal("OCP_FIFO", "Unsupported bringup FIFO control/reset")
            selected_cms = c.data[0];
            image_words = ocp_get_le32(c.data, 2);
          end
          OCP_CMD_RECOVERY_CTRL: begin
            if (c.data.size() != OCP_SPEC_LEN_RECOVERY_CTRL ||
                c.data[0] !== selected_cms || c.data[1] !== OCP_RC_IMAGE_SEL_CMS ||
                c.data[2] !== OCP_RC_ACTIVATE_CODE || !pending_seen || !baseline_zero)
              `uvm_fatal("OCP_ACTIVATION", "Activation lacks pending/zero baseline or legal payload")
            recovery_ctrl = {c.data[2],c.data[1],c.data[0]};
            activation_request = 1;
          end
          default: begin end
        endcase
      end
    end
  endfunction

  function void ocp_accept_status(int device);
    usb_ocp_base_control c;
    usb_ocp_base_epn_model epn;
    c = control[device];
    epn = ocp_get_epn(device);
    // Commit protocol completion here. USB 2.0 9.2.6 permits earlier device
    // processing; reset snapshots check those effects independently.
    if (reset_commit_at_status && device == 1 && c.setup[0] === 8'h21) begin
      case (c.setup[2])
        OCP_CMD_INDIRECT_FIFO_CTRL: begin
          if (c.data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL ||
              !(c.data[1] inside {8'h00,8'h01}))
            `uvm_fatal("OCP_FIFO", "Malformed FIFO control/reset at STATUS")
          if (c.data[1] === 1) begin
            // Only an observed explicit reset can retire old recovery bytes.
            if (fifo_actual.size() != 0 || fifo_expected.size() != 0 ||
                returned_bytes != accepted_bytes || compared_bytes != accepted_bytes)
              `uvm_fatal("OCP_RESET_AXI", "Explicit FIFO reset precedes complete accepted-old-byte reconciliation")
            fifo_expected.delete();
            accepted_bytes = 0;
            returned_bytes = 0;
            compared_bytes = 0;
            activation_request = 0;
            activation_status_acked = 0;
            activation_observed = 0;
            activation_cleared = 0;
            pending_seen = 0;
            final_status_seen = 0;
            clear_seen = 0;
            image_size_reads = 0;
            control_reads = 0;
            // OCP 8.2.5: fresh discovery may scan non-recovery CMS entries.
            fifo_discovered = 0;
          end else if (accepted_bytes != 0)
            `uvm_fatal("OCP_FIFO", "New image without observed explicit FIFO reset")
          selected_cms = c.data[0];
          image_words = ocp_get_le32(c.data,2);
        end
        OCP_CMD_RECOVERY_CTRL: begin
          if (c.data.size() != OCP_SPEC_LEN_RECOVERY_CTRL ||
              c.data[0] !== selected_cms || c.data[1] !== OCP_RC_IMAGE_SEL_CMS ||
              !(c.data[2] inside {OCP_RC_NO_ACTIVATE_CODE,OCP_RC_ACTIVATE_CODE}) ||
              !pending_seen || !baseline_zero)
            `uvm_fatal("OCP_ACTIVATION", "Activation lacks pending/baseline or legal payload")
          recovery_ctrl = {c.data[2],c.data[1],c.data[0]};
          activation_request = (c.data[2] === OCP_RC_ACTIVATE_CODE);
        end
        OCP_CMD_INDIRECT_FIFO_DATA: begin
          // Accepted FIFO bytes already belong to the packet-level ledger.
        end
        default: `uvm_fatal("OCP_RESET_COMMAND", "Unmodeled reset-row non-FIFO command")
      endcase
    end
    c.active = 0;
    c.status_acked = 1;
    usb_completions[device]++;
    ready_controls.push_back(device);
    if (c.setup[0] === 0 && c.setup[1] === 5) begin
      if (c.setup[2] == 0 || c.setup[2] > 127)
        `uvm_fatal("OCP_ADDRESS", "Invalid SET_ADDRESS")
      address[device] = c.setup[2][6:0];
    end
    if (c.setup[0] === 0 && c.setup[1] === 9) begin
      c.configuration = c.setup[2];
      enumerated[device] = (c.configuration === 1);
      if (epn != null && device == epn.device) begin
        if (c.ocp_get_value() !== {8'b0,epn.discovery.configuration})
          `uvm_fatal("OCP_EPN_CONFIGURATION", "Configuration differs from USB discovery")
        epn.configured = 1;
        epn.active_alternate = 0;
        epn.enabled = (epn.discovery.alternate === 0);
        epn.address = address[device];
        epn.control_address = address[1];
        epn.next_toggle = '{default:0};
      end
    end
    if (epn != null && device == epn.device && c.setup[0] === 8'h01 &&
        c.setup[1] === svt_usb_types::SET_INTERFACE) begin
      epn.active_alternate = c.setup[2];
      epn.enabled = (epn.active_alternate === epn.discovery.alternate);
      epn.next_toggle = '{default:0};
    end
    if (device == 0 && c.setup[0] === 8'h23 && c.setup[1] === 3 &&
        c.ocp_get_value() === 4) begin
      if (!(c.setup[4] inside {1,2}))
        `uvm_fatal("OCP_PORT", "Invalid downstream port")
      default_device = c.setup[4];
    end
    if (device == 1 && c.setup[0] === 8'h21 &&
        c.setup[2] === OCP_CMD_RECOVERY_CTRL &&
        c.data.size() == OCP_SPEC_LEN_RECOVERY_CTRL &&
        c.data[2] === OCP_RC_ACTIVATE_CODE)
      activation_status_acked = 1;
  endfunction

  function void ocp_observe_packet(usb_ocp_event item);
    usb_ocp_base_control c;
    usb_ocp_base_epn_model epn;
    logic incoming;
    logic status_stage;
    logic toggle;
    string setup_context;
    int unsigned setup_generation;
    if (full_speed && item.pid inside {svt_usb_packet::PING,svt_usb_packet::NYET} &&
        ((item.pid == svt_usb_packet::PING && item.endpoint == 0) ||
         (item.pid == svt_usb_packet::NYET && token != null && token.endpoint == 0))) begin
      `uvm_error("OCP_FS_HANDSHAKE", "FS control cannot use HS PING/NYET; no acceptance credit")
      candidate = null;
      token = null;
      return;
    end
    if (item.pid == svt_usb_packet::SOF) begin
      foreach (epn_models[i])
        if (epn_models[i] != null) epn_models[i].ocp_check_sof(item);
      return;
    end
    if (item.host_tx && item.pid inside {svt_usb_packet::SETUP,
        svt_usb_packet::IN,svt_usb_packet::OUT,svt_usb_packet::PING}) begin
      foreach (epn_models[i])
        if (epn_models[i] != null) epn_models[i].iso_no_handshake = 0;
      token = item;
      candidate = null;
      if (!item.packet_valid) begin token = null; return; end
      token_device = ocp_find_device(item.address);
      epn = ocp_get_epn(token_device);
      token_epoch = control[token_device].epoch;
      token_generation = control[token_device].generation;
      if (item.endpoint !== 0) begin
        if (epn == null || token_device != epn.device || item.pid == svt_usb_packet::SETUP)
          `uvm_fatal("OCP_CONTEXT", "Unexpected/unconfigured EPN token")
        // EPN identity is token_device; its overlap epoch/generation belongs
        // to the original device0 control, not device1's last standard EP0.
        token_epoch = control[1].epoch;
        token_generation = control[1].generation;
        epn.ocp_observe_packet(item,control[1]);
        token = epn.token;
        return;
      end
      // USB 2.0 5.5.4 permits transactions from independent control pipes
      // between an OCP control's accepted SETUP and completed STATUS.
      if (token_device == 2 && control[1].active) begin
        if (control[1].setup[0] === 8'ha1) dev1_ep0_read_overlap++;
        if (control[1].setup[0] === 8'h21) dev1_ep0_write_overlap++;
      end
      if (item.pid == svt_usb_packet::SETUP) begin
        foreach (setup_status_versions[i]) begin
          setup_status_versions[i].delete();
          if (current_status[i].valid)
            setup_status_versions[i].push_back(current_status[i]);
        end
      end
      return;
    end
    if (token == null) begin
      foreach (epn_models[i])
        if (epn_models[i] != null && epn_models[i].iso_no_handshake &&
            item.pid inside {svt_usb_packet::ACK,svt_usb_packet::NAK,
                             svt_usb_packet::NYET,svt_usb_packet::STALL})
          `uvm_fatal("OCP_EPN_ISO", "Handshake after ISO DATA is forbidden")
      return;
    end
    if (token.endpoint !== 0) begin
      epn = ocp_get_epn(token_device);
      if (epn == null)
        `uvm_fatal("OCP_EPN_CORRELATION", "EPN response lost its selected passive model")
      epn.ocp_observe_packet(item,control[1]);
      token = epn.token;
      candidate = null;
      return;
    end
    c = control[token_device];
    if (c.epoch != token_epoch || c.generation != token_generation)
      `uvm_fatal("OCP_CONTEXT", "Stale token epoch or SETUP generation")
    incoming = (token.pid == svt_usb_packet::IN);
    if (item.pid inside {svt_usb_packet::DATA0,svt_usb_packet::DATA1}) begin
      if (item.host_tx === incoming || !item.packet_valid)
        `uvm_fatal("OCP_PACKET", "Wrong DATA direction or invalid CRC")
      // These short OCP status replies fit one EP0 packet. Freeze before
      // inspecting its bytes, not at ACK or control-transfer completion:
      // subsequent programming cannot justify data already on the wire.
      if (incoming && c.active && c.status_read && !c.status_frozen &&
          item.pid == svt_usb_packet::DATA1) begin
        c.status_data_order = item.order;
        c.status_frozen = 1;
      end
      candidate = item;
      return;
    end
    if (item.pid inside {svt_usb_packet::NAK,svt_usb_packet::STALL}) begin
      if (item.pid == svt_usb_packet::STALL) begin
        setup_generation = c.generation;
        if (token.pid == svt_usb_packet::SETUP) begin
          setup_generation++;
          if (candidate != null && candidate.bytes.size() == 8)
            setup_context = $sformatf("pending SETUP=%p (not ACKed)",candidate.bytes);
          else setup_context = "pending SETUP unavailable (no complete SETUP DATA)";
        end else if (c.generation != 0)
          setup_context = $sformatf("accepted SETUP=%p",c.setup);
        else setup_context = "SETUP unavailable (no accepted generation)";
        if (stall_model == null ||
            !stall_model.ocp_check_stall(token_device,c,token,item,candidate))
          `uvm_fatal("OCP_STALL",$sformatf(
          "Unexpected STALL device=%s slot=%0d addr=%0d ep=%0d token=%s epoch=%0d setup_generation=%0d %s",
          (token_device == 0) ? "hub" : ((token_device == 1) ? "dev0" : "dev1"),
          token_device,token.address,token.endpoint,token.pid.name(),token_epoch,
          setup_generation,setup_context))
      end
      candidate = null;
      token = null;
      return;
    end
    if (item.pid == svt_usb_packet::ACK ||
        (item.pid == svt_usb_packet::NYET && !incoming)) begin
      if (candidate == null) begin token = null; return; end
      if (item.host_tx !== incoming)
        `uvm_fatal("OCP_ACK", "Handshake from wrong endpoint")
      if (token.pid == svt_usb_packet::SETUP) begin
        if (item.pid != svt_usb_packet::ACK)
          `uvm_fatal("OCP_SETUP", "SETUP requires ACK")
        ocp_accept_setup(token_device, candidate);
      end else begin
        if (!c.active) `uvm_fatal("OCP_STAGE", "DATA without active control transfer")
        status_stage = (c.ocp_get_length() == 0 || incoming != c.setup[0][7]);
        toggle = (candidate.pid == svt_usb_packet::DATA1);
        if (status_stage) begin
          if (c.ocp_get_length() == 0 && !incoming)
            `uvm_fatal("OCP_STATUS", "No-data control requires IN status")
          if (candidate.bytes.size() != 0 || !toggle)
            `uvm_fatal("OCP_STATUS", "Status stage must be DATA1 ZLP")
          if (!c.setup[0][7] && c.data.size() != c.ocp_get_length())
            `uvm_fatal("OCP_LENGTH", "OUT status before full data stage")
          // USB 2.0 8.5.1: HS control OUT Data/Status accept ACK or NYET.
          ocp_accept_status(token_device);
        end else if (toggle === c.next_toggle[incoming]) begin
          // USB 2.0 5.5.3/8.5.3.3: new DATA is not a last-packet retry.
          if (c.data.size() == c.ocp_get_length()) begin
            control_data_stage_errors++;
            `uvm_error("OCP_CONTROL_DATA_STAGE", $sformatf(
              "New accepted DATA after wLength device=%0d generation=%0d wLength=%0d pid=%s bytes=%0d order=%0d",
              token_device,c.generation,c.ocp_get_length(),candidate.pid.name(),
              candidate.bytes.size(),candidate.order))
          end
          c.next_toggle[incoming] = !toggle;
          foreach (candidate.bytes[i]) c.data.push_back(candidate.bytes[i]);
          if (c.data.size() > c.ocp_get_length())
            `uvm_fatal("OCP_LENGTH", "Control data exceeds wLength")
          if (!incoming) ocp_accept_out(token_device, candidate);
        end
        // A retry with the previous toggle has no second acceptance effect.
      end
      token = null;
      candidate = null;
    end
  endfunction
endclass
