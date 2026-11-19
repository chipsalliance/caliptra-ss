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

// OCP-only extension of the existing packet/transfer/completed-AXI ledger.
// USB 2.0 7.1.7.6/7, 9.1.1.6, 11.9: suspend retains device state; selective
// suspension leaves the upstream and the other downstream segment operational.
class usb_ocp_suspend_model extends uvm_object;
  `uvm_object_utils(usb_ocp_suspend_model)
  typedef enum int {GLOBAL, DEV0, DEV1} mode_e;
  mode_e mode;
  usb_ocp_predictor core;
  svt_usb_status native_status;
  typedef logic [7:0] bytes_t[$];
  bytes_t descriptor[3];
  logic [6:0] saved_address[3];
  logic [7:0] saved_configuration[3];
  int unsigned saved_epoch[3];
  int unsigned entry_generation[3];
  int unsigned exit_generation[3];
  logic [31:0] saved_words;
  logic [7:0] saved_cms;
  logic [23:0] saved_recovery;
  logic [31:0] saved_status[2];
  logic [31:0] dsus_mask[2];
  logic [31:0] address_mask[2];
  int unsigned address_shift[2];
  logic [31:0] live_command[2];
  int unsigned live_reads[2];
  int unsigned entry_reads[2];
  int unsigned exit_reads[2];
  int unsigned resume_reads[2];
  realtime live_at[2];
  int unsigned live_window_reads[2];
  int unsigned entry_accepted;
  int unsigned entry_returned;
  int unsigned exit_accepted;
  int unsigned exit_returned;
  int unsigned window_returned;
  int unsigned window_ocp_controls;
  int unsigned window_peer_configuration;
  int unsigned window_peer_descriptor;
  int unsigned window_soc_memory;
  int unsigned window_sofs;
  int unsigned resumed_peer_controls;
  int unsigned resumed_ocp_controls;
  bit resume_configuration_seen[3];
  bit resume_descriptor_seen[3];
  int unsigned port_suspend_checks;
  int unsigned port_resume_checks;
  bit port_resume_seen[2];
  int unsigned service_evidence[3];
  longint unsigned quiet_floor;
  realtime armed_at;
  realtime quiet_at;
  realtime quiet_end_at;
  realtime resumed_at;
  realtime recovery_guard_at;
  realtime recovery_guard_end_at;
  realtime native_microframe;
  realtime last_sof_at;
  realtime first_sof_on_at;
  bit armed;
  bit quiet_active;
  bit quiet_closed;
  bit resumed;
  bit peer_window_checked;
  bit progress_window_checked;
  bit finished;
  bit negative_retention;
  bit negative_peer;
  bit negative_progress;
  bit retention_applied;
  bit evidence_applied;
  int unsigned retention_errors;
  int unsigned evidence_errors;

  function new(string name = "usb_ocp_suspend_model");
    super.new(name);
  endfunction

  static function mode_e ocp_prepare_mode();
    string value;
    string values[$];
    uvm_cmdline_processor command_line;
    command_line = uvm_cmdline_processor::get_inst();
    if (command_line.get_arg_values("+usb_ocp_l2_mode=",values) != 1)
      `uvm_fatal("OCP_L2_MODE", "Require exactly one +usb_ocp_l2_mode=GLOBAL|DEV0|DEV1")
    value = values[0];
    case (value)
      "GLOBAL": return GLOBAL;
      "DEV0": return DEV0;
      "DEV1": return DEV1;
      default: `uvm_fatal("OCP_L2_MODE", "Invalid mode; use exactly GLOBAL, DEV0 or DEV1")
    endcase
    return GLOBAL;
  endfunction

  function void ocp_configure_geometry(usb_reg_model ral);
    uvm_reg r;
    uvm_reg_field f;
    for (int dev = 0; dev < 2; dev++) begin
      if (dev == 0) r = ral.combo.dev0_csr.DEVCMDSTAT;
      else r = ral.dev1_csr.DEVCMDSTAT;
      f = r.get_field_by_name("DSUS");
      if (f == null || f.get_n_bits() != 1)
        `uvm_fatal("OCP_L2_GEOMETRY", "Missing one-bit DSUS field geometry")
      dsus_mask[dev] = 32'(1) << f.get_lsb_pos();
      f = r.get_field_by_name("DEV_ADDR");
      if (f == null || f.get_n_bits() != 7)
        `uvm_fatal("OCP_L2_GEOMETRY", "Missing seven-bit live DEV_ADDR geometry")
      address_shift[dev] = f.get_lsb_pos();
      address_mask[dev] = 32'h7f << address_shift[dev];
    end
  endfunction

  function bit ocp_check_quiet_time(realtime observed_at);
    return armed && quiet_at != 0 && observed_at >= quiet_at &&
           (!quiet_closed || observed_at < quiet_end_at);
  endfunction

  function bit ocp_check_dsus(bit suspended);
    logic expected;
    foreach (live_command[dev]) begin
      if (live_reads[dev] <= (suspended ? entry_reads[dev] : exit_reads[dev])) return 0;
      expected = suspended && (mode == GLOBAL || (mode == DEV0 && dev == 0) ||
                                                 (mode == DEV1 && dev == 1));
      if ((live_command[dev] & dsus_mask[dev]) !==
          (expected ? dsus_mask[dev] : 32'b0)) return 0;
    end
    return 1;
  endfunction

  function void ocp_check_retained_core();
    if (!armed) return;
    foreach (saved_address[d])
      if (core.address[d] !== saved_address[d] ||
          core.control[d].configuration !== saved_configuration[d] ||
          core.control[d].epoch != saved_epoch[d]) begin
        retention_errors++;
        `uvm_error("OCP_L2_RETENTION", "USB address/configuration/epoch changed across L2")
      end
    if (core.image_words !== saved_words || core.selected_cms !== saved_cms ||
        core.recovery_ctrl !== saved_recovery || core.activation_request ||
        core.returned_bytes > core.accepted_bytes ||
        (mode != DEV1 && core.accepted_bytes != entry_accepted)) begin
      retention_errors++;
      `uvm_error("OCP_L2_RETENTION", "Pending image control or accepted/returned accounting changed illegally")
    end
    foreach (saved_status[i])
      if (core.current_status[i].value !== saved_status[i]) begin
        // Device0 may reach genuine Pending while port2 is suspended.
        if (mode == DEV1 && i == 0 &&
            core.current_status[i].value[7:0] === OCP_DEVICE_STATUS_RECOVERY_PENDING &&
            core.returned_bytes == saved_words*4) continue;
        retention_errors++;
        `uvm_error("OCP_L2_RETENTION", "Firmware-programmed recovery status changed without allowed progress")
      end
  endfunction

  function void ocp_check_entry(longint unsigned floor);
    if (armed || core == null || native_status == null || core.token != null ||
        core.accepted_bytes == 0 || core.accepted_bytes >= core.image_words*4)
      `uvm_fatal("OCP_L2_ENTRY", "Suspend requires a completed CONTROL and a partial accepted image")
    if (first_sof_on_at == 0 || last_sof_at < first_sof_on_at)
      `uvm_fatal("OCP_L2_NATIVE", "Initial SOF_ON lacks an independently observed actual SOF")
    foreach (core.control[d])
      if (core.control[d].active || core.transfer_crosschecks[d] != core.usb_completions[d])
        `uvm_fatal("OCP_L2_ENTRY", "Outstanding control/monitor obligation at suspend entry")
    foreach (saved_address[d]) begin
      saved_address[d] = core.address[d];
      saved_configuration[d] = core.control[d].configuration;
      saved_epoch[d] = core.control[d].epoch;
      entry_generation[d] = core.control[d].generation;
    end
    foreach (saved_status[i]) begin
      if (!core.current_status[i].valid)
        `uvm_fatal("OCP_L2_ENTRY", "Missing actual firmware status programming")
      saved_status[i] = core.current_status[i].value;
    end
    saved_words = core.image_words;
    saved_cms = core.selected_cms;
    saved_recovery = core.recovery_ctrl;
    entry_accepted = core.accepted_bytes;
    entry_returned = core.returned_bytes;
    entry_reads = live_reads;
    quiet_floor = floor;
    armed_at = $realtime;
    armed = 1;
    `uvm_info("OCP_L2_ENTRY", $sformatf(
      "mode=%s partial_bytes=%0d image_words=%0d SOF_ON_callback=%0t last_actual_SOF=%0t entry=%0t",
      mode.name(),entry_accepted,saved_words,first_sof_on_at,last_sof_at,armed_at), UVM_LOW)
  endfunction

  function void ocp_check_quiet_entry(longint unsigned floor);
    if (!armed || quiet_active || quiet_closed || !ocp_check_dsus(1))
      `uvm_fatal("OCP_L2_ENTRY", "Quiet interval lacks fresh owned DSUS entry evidence")
    quiet_floor = floor;
    quiet_at = $realtime;
    quiet_active = 1;
    ocp_check_retained_core();
  endfunction

  function bit ocp_check_upstream_active();
    // USB 2.0 Sections 11.5.1.6-11.5.1.7: packet forwarding enters
    // Transmit from Enabled without leaving normal powered operation.
    return (native_status.link_usb_20_state === svt_usb_types::ENABLED ||
            native_status.link_usb_20_state === svt_usb_types::TRANSMIT) &&
           native_status.link_usb_20_power_state === svt_usb_types::POWER_STATE_L0 &&
           native_status.physical_usb_20_working_speed === svt_usb_types::HS;
  endfunction

  function void ocp_check_native();
    if (!quiet_active) return;
    if (mode == GLOBAL) begin
      if (native_status.link_usb_20_state !== svt_usb_types::SUSPENDED ||
          native_status.link_usb_20_power_state !== svt_usb_types::POWER_STATE_L2)
        `uvm_fatal("OCP_L2_NATIVE", "Global quiet window left actual SUSPENDED/L2")
    end else begin
      if (!ocp_check_upstream_active())
        `uvm_fatal("OCP_L2_NATIVE", "Selective window lost actual upstream ENABLED/TRANSMIT/L0/HS")
    end
  endfunction

  function void ocp_check_recovery_guard();
    if (!resumed || native_microframe <= 0 || !ocp_check_upstream_active())
      `uvm_fatal("OCP_L2_NATIVE", $sformatf(
        "Recovery guard lost actual upstream ENABLED/TRANSMIT/L0/HS: resumed=%0b microframe=%0t link=%s power=%s speed=%0d required_speed=%0d last_SOF=%0t now=%0t",
        resumed,native_microframe,native_status.link_usb_20_state.name(),
        native_status.link_usb_20_power_state.name(),
        native_status.physical_usb_20_working_speed,svt_usb_types::HS,
        last_sof_at,$realtime))
    // Bound observation latency to two actual native microframes. The VIP's
    // own physical/link/protocol checks remain enabled independently.
    if (last_sof_at == 0 || $realtime - last_sof_at > 2*native_microframe)
      `uvm_fatal("OCP_L2_NATIVE", "Actual SOFs ceased during affected-segment resume recovery")
  endfunction

  // Called in observer order, BEFORE deferred recovery AXI accounting. The
  // event's original observation time scopes DSUS; a stale poll never rejects
  // a legitimately resumed SOF after quiet_end_at.
  function void ocp_capture_axi(usb_ocp_event item);
    logic [31:0] word;
    logic [6:0] expected_address;
    logic expected_dsus;
    int dev;
    if (item.manager inside {0,2} && !item.write_access) begin
      dev = (item.manager == 0) ? 0 : 1;
      if (item.axi_address == core.device_command_address[dev]) begin
        if (item.response_ok !== 1 || item.bytes.size() != 4)
          `uvm_fatal("OCP_L2_AXI", "DSUS evidence requires an actual successful owned DWORD read")
        word = core.ocp_get_le32(item.bytes,0);
        live_command[dev] = word;
        live_reads[dev]++;
        live_at[dev] = item.observed_at;
        if (armed && item.observed_at >= armed_at && !finished) begin
          expected_address = saved_address[dev+1];
          if (negative_retention && !retention_applied &&
              ocp_check_quiet_time(item.observed_at)) begin
            expected_address ^= 7'h01;
            retention_applied = 1;
          end
          if ((word & address_mask[dev]) !==
              (32'(expected_address) << address_shift[dev]) ||
              (word & (core.device_enable_mask[dev] | core.device_connect_mask[dev])) !==
                       (core.device_enable_mask[dev] | core.device_connect_mask[dev])) begin
            retention_errors++;
            `uvm_error("OCP_L2_RETENTION", "Actual owned DEVCMDSTAT lost live address/enable/connect")
          end
        end
        if (ocp_check_quiet_time(item.observed_at)) begin
          live_window_reads[dev]++;
          expected_dsus = mode == GLOBAL || (mode == DEV0 && dev == 0) ||
                                             (mode == DEV1 && dev == 1);
          if ((word & dsus_mask[dev]) !== (expected_dsus ? dsus_mask[dev] : 32'b0))
            `uvm_fatal("OCP_L2_DSUS", "Actual DSUS changed inside the stable pre-resume window")
        end
      end
    end
    if (!ocp_check_quiet_time(item.observed_at)) return;
    if (item.manager == 3) window_soc_memory++;
    if (item.manager == 0 && !item.write_access &&
        core.recovery_register.exists(item.axi_address) &&
        core.recovery_register[item.axi_address] == "INDIRECT_FIFO_DATA") begin
      if (item.response_ok !== 1 || item.axi_burst !== AAXI_BURST_FIXED)
        `uvm_fatal("OCP_L2_AXI", "Window progress lacks successful real FIXED DMA")
      window_returned += item.bytes.size();
    end
  endfunction

  function void ocp_capture_packet(usb_ocp_event item);
    if (item.host_tx && item.pid === svt_usb_packet::SOF && item.packet_valid)
      last_sof_at = item.observed_at;
    if (recovery_guard_at != 0 && item.observed_at >= recovery_guard_at &&
        (recovery_guard_end_at == 0 || item.observed_at < recovery_guard_end_at) &&
        item.host_tx && item.pid inside {svt_usb_packet::SETUP,svt_usb_packet::IN,
          svt_usb_packet::OUT,svt_usb_packet::PING} &&
        (mode == GLOBAL ||
         item.address === saved_address[(mode == DEV0) ? 1 : 2]))
      `uvm_fatal("OCP_L2_GUARD", "Addressed transaction on an affected segment during resume recovery")
    if (!ocp_check_quiet_time(item.observed_at)) return;
    if (mode == GLOBAL)
      `uvm_fatal("OCP_L2_QUIET", "USB packet/SOF observed in actual global L2 quiet interval")
    if (item.host_tx && item.pid === svt_usb_packet::SOF && item.packet_valid)
      window_sofs++;
    if (item.host_tx && item.pid inside {svt_usb_packet::SETUP,svt_usb_packet::IN,
        svt_usb_packet::OUT,svt_usb_packet::PING} &&
        item.address === saved_address[(mode == DEV0) ? 1 : 2])
      `uvm_fatal("OCP_L2_QUIET", "Token to suspended downstream device in stable selective window")
  endfunction

  function void ocp_capture_transfer(usb_ocp_event item);
    int dev;
    dev = core.ocp_find_device(item.address);
    if (!item.transfer_ok || item.transfer_type != svt_usb_transfer::CONTROL_TRANSFER) return;
    if (item.setup[0] === 8'h80 && item.setup[1] === svt_usb_types::GET_DESCRIPTOR &&
        {item.setup[3],item.setup[2]} === 16'h0100) begin
      if (!armed) descriptor[dev] = item.bytes;
      else begin
        if (item.bytes !== descriptor[dev]) begin
          retention_errors++;
          `uvm_error("OCP_L2_RETENTION", "Native-completed descriptor differs from runtime USB discovery")
        end
        if (resumed) resume_descriptor_seen[dev] = 1;
      end
    end
    if (armed && item.setup[0] === 8'h80 &&
        item.setup[1] === svt_usb_types::GET_CONFIGURATION) begin
      if (item.bytes.size() != 1 || item.bytes[0] !== saved_configuration[dev]) begin
        retention_errors++;
        `uvm_error("OCP_L2_RETENTION", "Actual USB configuration readback changed across L2")
      end
      if (resumed) resume_configuration_seen[dev] = 1;
    end
    if (ocp_check_quiet_time(item.observed_at) && item.transfer_start_order >= quiet_floor) begin
      if (dev == 2 && item.setup[0] === 8'h80) begin
        if (item.setup[1] === svt_usb_types::GET_CONFIGURATION) window_peer_configuration++;
        if (item.setup[1] === svt_usb_types::GET_DESCRIPTOR) window_peer_descriptor++;
      end
      if (dev == 1 && item.setup[0] === 8'h21 &&
          item.setup[2] === OCP_CMD_INDIRECT_FIFO_DATA) window_ocp_controls++;
    end
    if (resumed && !finished) begin
      if (dev == 2 && item.setup[0] === 8'h80) resumed_peer_controls++;
      if (dev == 1 && item.setup[0] === 8'h21 &&
          item.setup[2] === OCP_CMD_INDIRECT_FIFO_DATA) resumed_ocp_controls++;
    end
    // USB 2.0 11.24.2.7: four-byte little-endian GetPortStatus, not the
    // shipped example's inverted suspend-bit predicate.
    if (armed && dev == 0 && item.setup[0] === 8'ha3 &&
        item.setup[1] === svt_usb_types::HUB_CLASS_GET_STATUS &&
        item.setup[4] inside {1,2} && item.bytes.size() == 4) begin
      if (item.bytes[0][2] === 1 && !resumed) port_suspend_checks++;
      if (resumed && item.bytes[0][2] === 0 &&
          item.bytes[0][1:0] === 2'b11 && item.bytes[1][2] === 1) begin
        port_resume_checks++;
        port_resume_seen[item.setup[4]-1] = 1;
      end
    end
  endfunction

  function void ocp_check_resume();
    if (!quiet_closed || !ocp_check_dsus(0) || !ocp_check_upstream_active())
      `uvm_fatal("OCP_L2_RESUME", "Resume lacks actual DSUS clear and native ENABLED/TRANSMIT/L0/HS")
    if (!resumed) resumed_at = $realtime;
    resumed = 1;
    resume_reads = live_reads;
    ocp_check_retained_core();
  endfunction

  function void ocp_record_service(usb_ocp_suspend_service_record record);
    if (record == null || !record.ended)
      `uvm_fatal("OCP_L2_SERVICE", "Missing executed service coverage record")
    service_evidence[int'(record.operation)]++;
    if (record.operation == usb_ocp_suspend_service_record::SOF_ON && first_sof_on_at == 0)
      first_sof_on_at = record.ended_at;
  endfunction

  function void ocp_check_close_quiet();
    bit peer;
    bit progress;
    if (!quiet_active || quiet_closed)
      `uvm_fatal("OCP_L2_WINDOW", "Missing or duplicate quiet-window close")
    ocp_check_native();
    ocp_check_retained_core();
    quiet_end_at = $realtime;
    quiet_active = 0;
    quiet_closed = 1;
    exit_reads = live_reads;
    exit_accepted = core.accepted_bytes;
    exit_returned = core.returned_bytes;
    foreach (live_window_reads[d])
      if (live_window_reads[d] < 2)
        `uvm_fatal("OCP_L2_WINDOW", "Stable interval lacks repeated actual owned DSUS/address reads")
    peer = window_peer_configuration != 0 && window_peer_descriptor != 0 &&
           window_soc_memory != 0;
    progress = window_ocp_controls != 0 && exit_accepted > entry_accepted &&
               window_returned >= ((saved_words < 64) ? saved_words*4 : 256);
    if (mode == DEV0 && negative_peer) begin peer = 0; evidence_applied = 1; end
    if (mode == DEV1 && negative_progress) begin progress = 0; evidence_applied = 1; end
    peer_window_checked = peer;
    progress_window_checked = progress;
    if ((mode == DEV0 && !peer) || (mode == DEV1 && !progress)) begin
      evidence_errors++;
      `uvm_error("OCP_L2_PROGRESS", "Missing selected-mode native peer or accepted USB/returned AXI window proof")
    end
    if (mode != GLOBAL && window_sofs == 0)
      `uvm_fatal("OCP_L2_NATIVE", "No actual upstream SOF in selective quiet interval")
    `uvm_info("OCP_L2_WINDOW", $sformatf(
      "mode=%s start=%0t end=%0t reads=%p generations=%p accepted=%0d->%0d returned=%0d->%0d window_DMA=%0d peer=%0d/%0d OCP=%0d SoCmem=%0d SOF=%0d",
      mode.name(),quiet_at,quiet_end_at,live_window_reads,entry_generation,
      entry_accepted,exit_accepted,entry_returned,exit_returned,window_returned,
      window_peer_configuration,window_peer_descriptor,window_ocp_controls,
      window_soc_memory,window_sofs), UVM_LOW)
  endfunction

  function void ocp_check_complete();
    if (!finished || !armed || !quiet_closed || quiet_active || !resumed ||
        resumed_at == 0 || recovery_guard_at < resumed_at ||
        recovery_guard_end_at-recovery_guard_at < 10ms ||
        resume_reads[0] <= exit_reads[0] || resume_reads[1] <= exit_reads[1] ||
        resumed_peer_controls < 2 ||
        (mode != DEV1 && resumed_ocp_controls == 0) ||
        !port_resume_seen[0] || !port_resume_seen[1] ||
        (mode != GLOBAL && port_suspend_checks == 0) ||
        service_evidence[int'(usb_ocp_suspend_service_record::SOF_ON)] == 0 ||
        service_evidence[int'(usb_ocp_suspend_service_record::SOF_OFF)] == 0 ||
        (mode == GLOBAL && service_evidence[int'(usb_ocp_suspend_service_record::LINK_CLEAR)] != 1) ||
        (mode != GLOBAL && service_evidence[int'(usb_ocp_suspend_service_record::LINK_CLEAR)] != 0))
      `uvm_fatal("OCP_L2_INCOMPLETE", "Missing selected L2 entry/exit/retained-identity/progress obligations")
    foreach (entry_generation[d])
      if (exit_generation[d] <= entry_generation[d] ||
          !resume_configuration_seen[d] || !resume_descriptor_seen[d])
        `uvm_fatal("OCP_L2_INCOMPLETE", "Missing post-resume native configuration/descriptor generation proof")
    if ((mode == DEV0 && !peer_window_checked) ||
        (mode == DEV1 && !progress_window_checked))
      `uvm_error("OCP_L2_INCOMPLETE", "Selected-mode positive window evidence is incomplete")
    if (negative_retention && (!retention_applied || retention_errors == 0))
      `uvm_fatal("OCP_L2_NEGATIVE", "Retention checker control did not produce its required actual error")
    if ((negative_peer || negative_progress) && (!evidence_applied || evidence_errors == 0))
      `uvm_fatal("OCP_L2_NEGATIVE", "Evidence checker control did not produce its required actual error")
    `uvm_info("OCP_L2_EVIDENCE", $sformatf(
      "mode=%s entry_generations=%p exit_generations=%p live_reads=%p entry=%p exit=%p retention_errors=%0d evidence_errors=%0d",
      mode.name(),entry_generation,exit_generation,live_reads,entry_reads,exit_reads,
      retention_errors,evidence_errors), UVM_LOW)
  endfunction
endclass
