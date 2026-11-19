// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_model extends uvm_object;
  `uvm_object_utils(usb_ocp_reset_model)
  typedef logic [7:0] bytes_t[$];
  usb_ocp_reset_control cfg;
  usb_ocp_predictor core;
  logic [31:0] dres_mask[2];
  logic [31:0] saved_register[string];
  bit post_register[string];
  int unsigned sampling; // 0: ordinary, 1: initial, 2: after reset, 3: command effects.
  bit snapshot_ready;
  bit command_checkpoint_requested;
  bit command_checkpoint_ready;
  bit command_register[string];
  bytes_t command_data;
  logic [31:0] command_initial_ctrl;
  logic [31:0] command_checkpoint_ctrl;
  logic [31:0] command_snapshot_reads[longint unsigned];
  longint unsigned command_read_floor;
  int unsigned command_reads;
  bit partial_ready;
  bit reset_seen[2];
  bit epoch_changed;
  int unsigned recovery_epoch;
  int unsigned saved_epoch[3];
  int unsigned peer_controls;
  int unsigned peer_axi;
  int unsigned peer_dma_bytes;
  bit window_open;
  bit window_seen;
  int unsigned old_accepted;
  int unsigned old_returned;
  int unsigned old_compared;
  int unsigned old_entry_returned;
  int unsigned old_entry_compared;
  bytes_t old_fifo_expected;
  bytes_t old_fifo_actual;
  int unsigned old_post_compared;
  int unsigned old_post_bursts;
  int unsigned old_post_instances[$];
  int unsigned old_byte_errors;
  bit byte_negative_applied;
  bit old_batch_active;
  bit old_batch_complete;
  longint unsigned retention_end_order;
  longint unsigned old_first_axi_order;
  longint unsigned old_last_axi_order;
  int unsigned old_control_crosschecks;
  int unsigned old_control_invalidations;
  int unsigned native_reset_crosschecks;
  int unsigned host_cleanup_crosschecks;
  bit cleanup_requested[3];
  longint unsigned cleanup_floor[3];
  int unsigned cleanup_tokens[3];
  int unsigned reinit_writes;
  int unsigned retained_reads;
  int unsigned explicit_resets;
  int unsigned fresh_mode_reads;
  int unsigned fresh_caps_reads;
  int unsigned fresh_fifo_reads;
  longint unsigned event_order;
  int unsigned stage_device;
  int unsigned stage_generation;
  int unsigned stage_data_tokens;
  int unsigned stage_status_tokens;
  bit stage_data_payload_seen;
  bit stage_tracking;
  bit status_processing_paused;
  realtime status_processing_paused_at;
  usb_ocp_base_control interrupted[3];
  bit interrupt_checked[3];
  longint unsigned interrupt_serial[3];
  bit finished;

  function new(string name = "usb_ocp_reset_model");
    super.new(name);
  endfunction

  function void ocp_configure_geometry(usb_reg_model ral);
    dres_mask[0] = 32'(1) << ral.combo.dev0_csr.DEVCMDSTAT.DRES_C.get_lsb_pos();
    dres_mask[1] = 32'(1) << ral.dev1_csr.DEVCMDSTAT.DRES_C.get_lsb_pos();
  endfunction

  function void ocp_check_entry();
    if (cfg == null || core == null || cfg.armed || !snapshot_ready ||
        !core.discovery_seen || !core.capabilities_seen || !core.fifo_discovered)
      `uvm_fatal("OCP_RESET_ENTRY", "Reset lacks initial discovery and owned pre-event snapshot")
    if (cfg.stage == usb_ocp_reset_control::PARTIAL) begin
      if (core.accepted_bytes == 0 || core.accepted_bytes >= core.image_words*4)
        `uvm_fatal("OCP_RESET_ENTRY", "PARTIAL requires a genuinely accepted incomplete image")
      if (cfg.ocp_check_recovery_affected() &&
          (core.accepted_bytes != 64*4 || core.returned_bytes != 0 ||
           core.compared_bytes != 0 || core.fifo_expected.size() != 64*4))
        `uvm_fatal("OCP_RESET_PUBLICATION", "PARTIAL lacks one complete unread normal publication batch")
    end else if (core.accepted_bytes != core.image_words*4 ||
                 core.compared_bytes != core.accepted_bytes ||
                 !core.pending_seen)
      `uvm_fatal("OCP_RESET_ENTRY", "Control/activation boundary lacks initial exact image and Pending")
    saved_epoch = '{core.control[0].epoch,core.control[1].epoch,core.control[2].epoch};
    old_accepted = core.accepted_bytes;
    old_returned = core.returned_bytes;
    old_compared = core.compared_bytes;
    old_entry_returned = old_returned;
    old_entry_compared = old_compared;
    // Copy only the passive ACK-qualified expected stream, never DUT FIFO.
    old_fifo_expected = core.fifo_expected;
    cfg.armed = 1;
  endfunction

  function bit ocp_check_command_idle();
    usb_ocp_base_control c;
    if (core.token == null) return 1;
    c = core.control[stage_device];
    // USB 8.5.3.1/9.2.6: STATUS may remain unacknowledged while the
    // accepted command is processed. Preserve the paused token/candidate.
    return cfg.stage == usb_ocp_reset_control::STATUS &&
           status_processing_paused && c != null &&
           core.token_device == stage_device &&
           core.token_epoch == c.epoch && core.token_generation == c.generation &&
           core.token.packet_valid === 1'b1 && core.token.host_tx === 1'b1 &&
           core.token.pid == svt_usb_packet::IN &&
           core.token.endpoint === 0 && core.token.address === c.address &&
           core.candidate != null && core.candidate.packet_valid === 1'b1 &&
           core.candidate.host_tx === 1'b0 &&
           core.candidate.pid == svt_usb_packet::DATA1 &&
           core.candidate.bytes.size() == 0 &&
           core.token.observed_at <= core.candidate.observed_at &&
           core.candidate.observed_at <= status_processing_paused_at;
  endfunction

  function bit ocp_check_command_service();
    usb_ocp_base_control c;
    c = core.control[1];
    return command_checkpoint_requested && !epoch_changed &&
           cfg.ocp_check_recovery_affected() && cfg.armed &&
           cfg.attempt == 0 && !cfg.abort_requested &&
           !cfg.caliptra_quiescent && !cfg.mcu_reinitialized &&
           stage_tracking && stage_device == 1 && c != null &&
           c.active === 1'b1 && c.status_acked === 1'b0 &&
           c.generation == stage_generation && c.epoch == saved_epoch[1] &&
           c.setup[0] === 8'h21 && c.setup[2] === OCP_CMD_RECOVERY_CTRL &&
           c.ocp_get_length() == OCP_SPEC_LEN_RECOVERY_CTRL &&
           c.data.size() == OCP_SPEC_LEN_RECOVERY_CTRL &&
           cfg.stage inside {usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS} &&
           ((cfg.stage == usb_ocp_reset_control::DATA && stage_status_tokens == 0) ||
            (cfg.stage == usb_ocp_reset_control::STATUS && stage_status_tokens != 0)) &&
           ocp_check_command_idle();
  endfunction

  function void ocp_configure_command_checkpoint();
    usb_ocp_base_control c;
    if (command_checkpoint_requested || !saved_register.exists("RECOVERY_CTRL"))
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Command checkpoint lacks a unique initial frontdoor baseline")
    command_checkpoint_requested = 1;
    if (!ocp_check_command_service())
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Command checkpoint lacks full accepted original DATA/idle transaction/held writer")
    c = core.control[1];
    command_data = c.data;
    command_initial_ctrl = saved_register["RECOVERY_CTRL"];
    command_checkpoint_ctrl = command_initial_ctrl;
    // Select the discovered CMS image without activating it (OCP 9.2).
    // This changes image selection, not a NOOP or a device-cleared field.
    if (command_data[0] !== core.selected_cms ||
        command_initial_ctrl[7:0] !== core.selected_cms ||
        command_data[1] !== OCP_RC_IMAGE_SEL_CMS ||
        command_data[2] !== usb_ocp_predictor::OCP_RC_NO_ACTIVATE_CODE ||
        command_initial_ctrl[15:8] !== usb_ocp_predictor::OCP_RC_IMAGE_SEL_NONE ||
        command_initial_ctrl[23:16] !== usb_ocp_predictor::OCP_RC_NO_ACTIVATE_CODE)
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Interrupted selection is malformed, idempotent or activates the old image")
  endfunction

  function bit ocp_check_command_fields(logic [31:0] value,
      logic [31:0] baseline, string report_id);
    bit valid = 1;
    if (command_data.size() != OCP_SPEC_LEN_RECOVERY_CTRL)
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Command comparison lacks the accepted three-byte payload")
    // USB 9.2.6/OCP 9.2 do not prescribe atomic field-update ordering.
    // A processed field cannot regress; an unprocessed one may reach its
    // accepted requested value. Unrelated/reserved bits remain exact.
    for (int i = 0; i < OCP_SPEC_LEN_RECOVERY_CTRL; i++)
      if (value[i*8 +: 8] !== baseline[i*8 +: 8] &&
          !(baseline[i*8 +: 8] === command_initial_ctrl[i*8 +: 8] &&
            value[i*8 +: 8] === command_data[i])) begin
        valid = 0;
        `uvm_error(report_id, $sformatf(
          "RECOVERY_CTRL byte=%0d actual=%02h checkpoint=%02h initial=%02h requested=%02h",
          i,value[i*8 +: 8],baseline[i*8 +: 8],
          command_initial_ctrl[i*8 +: 8],command_data[i]))
      end
    if (value[31:24] !== baseline[31:24]) begin
      valid = 0;
      `uvm_error(report_id, $sformatf(
        "RECOVERY_CTRL unrelated byte actual=%02h expected=%02h",
        value[31:24],baseline[31:24]))
    end
    return valid;
  endfunction

  function void ocp_check_command_checkpoint_complete();
    if (!ocp_check_command_service() || sampling != 0 ||
        command_reads != saved_register.num() || command_snapshot_reads.num() != 0)
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Command checkpoint lacks all actual completed/consumed pre-event reads")
    foreach (saved_register[name])
      if (!command_register.exists(name))
        `uvm_fatal("OCP_RESET_COMMAND_EFFECT", $sformatf("Missing command checkpoint read %s",name))
    command_checkpoint_ready = 1;
    `uvm_info("OCP_RESET_COMMAND_EFFECT", $sformatf(
      "scope=%s stage=%s original_epoch=%0d generation=%0d accepted=%p initial=%08h checkpoint=%08h reads=%0d floor=%0d; no STATUS completion or activation credit",
      cfg.scope.name(),cfg.stage.name(),saved_epoch[1],stage_generation,
      command_data,command_initial_ctrl,command_checkpoint_ctrl,command_reads,
      command_read_floor), UVM_LOW)
  endfunction

  function bit ocp_check_command_snapshot_read(usb_ocp_event item);
    if (!command_snapshot_reads.exists(item.order)) return 0;
    if (item.manager != 0 || item.write_access ||
        !core.recovery_register.exists(item.axi_address) ||
        core.recovery_register[item.axi_address] != "RECOVERY_CTRL" ||
        item.axi_beats != 1 || item.bytes.size() != 4 ||
        core.ocp_get_le32(item.bytes,0) !== command_snapshot_reads[item.order])
      `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Deferred command comparison lost its exact completed-read identity/value")
    // Capture already checked this immutable value against its owned phase.
    // Consume only this expectation, never discard the accepted AXI actual.
    command_snapshot_reads.delete(item.order);
    return 1;
  endfunction

  function void ocp_check_begin_old_batch(logic payload_available);
    if (!cfg.ocp_check_recovery_affected() ||
        cfg.stage != usb_ocp_reset_control::PARTIAL || !cfg.abort_requested ||
        !epoch_changed || !cfg.retention_complete || sampling != 0 ||
        cfg.caliptra_quiescent || cfg.mcu_reinitialized || reinit_writes != 0 ||
        recovery_epoch != 0 || old_batch_active || old_batch_complete ||
        payload_available !== 1'b1 || old_fifo_expected.size() != 64*4 ||
        core.accepted_bytes != old_accepted || core.returned_bytes != 0 ||
        core.compared_bytes != 0)
      `uvm_fatal("OCP_RESET_PUBLICATION", "Old batch lacks real readiness/reset/all-register snapshot/ownership evidence")
    old_batch_active = 1;
  endfunction

  function void ocp_check_old_fifo_bytes(usb_ocp_event item);
    logic [7:0] expected;
    int unsigned index;
    if (!old_batch_active || !cfg.retention_complete || sampling != 0 ||
        !epoch_changed || item.order <= event_order ||
        item.order <= retention_end_order || cfg.caliptra_quiescent ||
        cfg.mcu_reinitialized || reinit_writes != 0 ||
        item.axi_beats == 0 || item.axi_beats > 16 ||
        item.bytes.size() != item.axi_beats*4 ||
        old_fifo_actual.size()+item.bytes.size() > old_fifo_expected.size())
      `uvm_fatal("OCP_RESET_BYTE_RETENTION", "Old FIFO actual lacks POST-reset/pre-writer normal-burst evidence")
    if (old_post_bursts == 0) old_first_axi_order = item.order;
    old_last_axi_order = item.order;
    old_post_bursts++;
    old_post_instances.push_back(item.axi_instance);
    foreach (item.bytes[i]) begin
      index = old_fifo_actual.size();
      expected = old_fifo_expected[index];
      // Only this private comparison operand changes. Canonical OCP_IMAGE
      // comparison still sees the original accepted and returned byte streams.
      if (cfg.negative == usb_ocp_reset_control::BYTE_RETENTION &&
          !byte_negative_applied) begin
        expected ^= 8'h01;
        byte_negative_applied = 1;
      end
      if (item.bytes[i] !== expected) begin
        old_byte_errors++;
        `uvm_error("OCP_RESET_BYTE_RETENTION", $sformatf(
          "POST-reset old byte=%0d order=%0d actual=%02h accepted=%02h",
          index,item.order,item.bytes[i],expected))
      end
      old_fifo_actual.push_back(item.bytes[i]);
      old_post_compared++;
    end
  endfunction

  function void ocp_check_old_batch_complete(logic payload_available);
    if (!old_batch_active || payload_available !== 1'b0 ||
        old_fifo_actual.size() != old_accepted || old_post_compared != old_accepted ||
        old_post_bursts != 4 || core.accepted_bytes != old_accepted ||
        core.returned_bytes != old_accepted || core.compared_bytes != old_accepted ||
        core.fifo_expected.size() != 0 || core.fifo_actual.size() != 0 ||
        (cfg.negative != usb_ocp_reset_control::BYTE_RETENTION && old_byte_errors != 0) ||
        (cfg.negative == usb_ocp_reset_control::BYTE_RETENTION && !byte_negative_applied))
      `uvm_fatal("OCP_RESET_QUIESCENCE", "Old published batch lacks readiness fall/exact returned-byte reconciliation")
    old_batch_active = 0;
    old_batch_complete = 1;
  endfunction

  function void ocp_check_usb_reset(usb_ocp_event item, int dev);
    usb_ocp_base_control fresh;
    if (!cfg.armed || reset_seen[dev]) return;
    if (!cfg.ocp_check_device_affected(dev+1))
      `uvm_fatal("OCP_RESET_SCOPE", "Selective reset reached the unaffected device")
    reset_seen[dev] = 1;
    `uvm_info("OCP_RESET_HW", $sformatf(
      "scope=%s stage=%s slot=%0d manager=%0d DRES_C_order=%0d epoch_changed=%0b",
      cfg.scope.name(),cfg.stage.name(),dev+1,item.manager,item.order,
      epoch_changed), UVM_LOW)
    if (epoch_changed) return;
    epoch_changed = 1;
    event_order = item.order;
    foreach (core.control[d]) begin
      if (!cfg.ocp_check_device_affected(d)) continue;
      if (stage_tracking && d == stage_device) begin
        ocp_check_stage_cut(core.control[d]);
        old_control_invalidations++;
        stage_tracking = 0;
        `uvm_info("OCP_RESET_CONTROL_INVALIDATION", $sformatf(
          "actual DRES_C order=%0d slot=%0d old_epoch=%0d generation=%0d accepted_prefix=%0d STATUS_ACK=%0b",
          item.order,d,core.control[d].epoch,core.control[d].generation,
          core.control[d].data.size(),core.control[d].status_acked), UVM_LOW)
      end
      // Preserve the old control for the independent native abort crosscheck.
      if (core.control[d].active) interrupted[d] = core.control[d];
      fresh = usb_ocp_base_control::type_id::create("reset_control");
      fresh.epoch = core.control[d].epoch;
      fresh.generation = core.control[d].generation;
      core.control[d] = fresh;
      core.ocp_cancel_usb_epoch(d);
      core.enumerated[d] = 0;
      core.address[d] = (d == 0) ? 0 : ((d == 1) ? 126 : 127);
    end
    core.default_device = (cfg.scope == usb_ocp_reset_control::BUS) ? 0 :
                          ((cfg.scope == usb_ocp_reset_control::DEV0) ? 1 : 2);
    if (cfg.ocp_check_recovery_affected()) begin
      if (core.accepted_bytes != old_accepted ||
          core.returned_bytes < old_returned ||
          core.compared_bytes < old_compared)
        `uvm_fatal("OCP_RESET_LEDGER", "USB reset discarded a recovery or accepted-AXI obligation")
      // Mandatory discovery is fresh; recovery bytes and activation persist.
      core.recovery_mode_seen = 0;
      core.capabilities_seen = 0;
      core.discovery_seen = 0;
    end
  endfunction

  function void ocp_check_stage_cut(usb_ocp_base_control c);
    if (c == null)
      `uvm_fatal("OCP_RESET_STAGE", "Selected control boundary has no passive context")
    if (c.active !== 1'b1 || c.status_acked !== 1'b0 ||
        c.generation != stage_generation ||
        (cfg.stage == usb_ocp_reset_control::SETUP &&
         (c.data.size() != 0 || stage_data_tokens != 0 || stage_status_tokens != 0)) ||
        (cfg.stage == usb_ocp_reset_control::DATA &&
         (c.ocp_get_length() == 0 || c.data.size() != c.ocp_get_length() ||
          stage_status_tokens != 0)) ||
        (cfg.stage == usb_ocp_reset_control::STATUS &&
         (c.data.size() != c.ocp_get_length() || stage_status_tokens == 0)))
      `uvm_fatal("OCP_RESET_STAGE", $sformatf(
        "Passive stream missed cut: scope=%s stage=%s slot=%0d epoch=%0d generation=%0d required_generation=%0d active=%0b DATA=%0d/%0d DATA_tokens=%0d STATUS_tokens=%0d STATUS_ACK=%0b",
        cfg.scope.name(),cfg.stage.name(),stage_device,c.epoch,c.generation,
        stage_generation,c.active,c.data.size(),c.ocp_get_length(),
        stage_data_tokens,stage_status_tokens,c.status_acked))
    `uvm_info("OCP_RESET_CUT", $sformatf(
      "scope=%s stage=%s slot=%0d epoch=%0d generation=%0d active=%0b DATA=%0d/%0d DATA_tokens=%0d STATUS_tokens=%0d STATUS_ACK=%0b",
      cfg.scope.name(),cfg.stage.name(),stage_device,c.epoch,c.generation,
      c.active,c.data.size(),c.ocp_get_length(),stage_data_tokens,
      stage_status_tokens,c.status_acked), UVM_LOW)
  endfunction

  function void ocp_check_host_cleanup(int device, longint unsigned floor);
    if (device < 1 || device > 2)
      `uvm_fatal("OCP_RESET_HOST_CLEANUP", "Invalid selected host cleanup slot")
    if (cfg.scope == usb_ocp_reset_control::BUS || !epoch_changed ||
        !reset_seen[device-1] || interrupted[device] == null ||
        interrupted[device].status_acked !== 1'b0 ||
        core.control[device].active !== 1'b0 ||
        core.control[device].epoch <= interrupted[device].epoch ||
        cleanup_requested[device])
      `uvm_fatal("OCP_RESET_HOST_CLEANUP", "HOST cleanup lacks independently observed selected hardware reset/old epoch invalidation")
    cleanup_requested[device] = 1;
    cleanup_floor[device] = floor;
    `uvm_info("OCP_RESET_HOST_CLEANUP", $sformatf(
      "Native cancellation after DRES_C order=%0d slot=%0d completion_floor=%0d; command bit1 is NOT reset attribution",
      event_order,device,floor), UVM_LOW)
  endfunction

  function void ocp_check_native_result(usb_ocp_event item, int device);
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed;
    if (device < 1 || device > 2 || !epoch_changed ||
        interrupted[device] == null || !reset_seen[device-1])
      `uvm_fatal("OCP_RESET_EPOCH", "Interrupted result lacks actual selected reset/old context")
    allowed = 0;
    allowed[0] = 1; // Documented native protocol reset, not CMD abort.
    if (cfg.scope != usb_ocp_reset_control::BUS && cleanup_requested[device])
      allowed[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] = 1;
    if (!item.setup[0][7]) allowed[5] = 1;
    if (item.transfer_ok !== 1'b0 || !item.native_aborted ||
        (item.results & ~allowed) !== 0 ||
        !((item.results[0] === 1'b1 &&
           item.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1'b0) ||
          (item.results[0] === 1'b0 &&
           item.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1'b1)) ||
        (item.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1'b1 &&
         (!cleanup_requested[device] || item.order < cleanup_floor[device])))
      `uvm_fatal("OCP_RESET_NATIVE_ATTRIBUTION", "Old completion is not reset-bit0 or separately accounted POST-reset HOST-bit1 cleanup")
  endfunction

  function bit ocp_check_interrupted_transfer(usb_ocp_event item);
    usb_ocp_base_control c;
    int unsigned expected_epoch;
    foreach (interrupted[d]) begin
      c = interrupted[d];
      if (c == null || interrupt_checked[d] || item.address !== c.address ||
          item.setup !== c.setup || item.transfer_start_order >= event_order) continue;
      if (d == 0) continue;
      if (!reset_seen[d-1]) continue;
      ocp_check_native_result(item,d);
      if (c.status_acked || item.bytes.size() < c.data.size())
        `uvm_fatal("OCP_RESET_EPOCH", "Interrupted epoch completed or has an unexplained native failure")
      foreach (c.data[i])
        if (item.bytes[i] !== c.data[i])
          `uvm_fatal("OCP_RESET_PREFIX", "Native completion differs from ACK-accepted old prefix")
      expected_epoch = core.control[d].epoch;
      if (cfg.negative == usb_ocp_reset_control::EPOCH) expected_epoch = c.epoch;
      if (expected_epoch <= c.epoch)
        `uvm_error("OCP_RESET_EPOCH", "Interrupted completion cannot acquire an old epoch as its successor")
      interrupt_checked[d] = 1;
      interrupt_serial[d] = item.transfer_serial;
      old_control_crosschecks++;
      if (item.results[0] === 1'b1) native_reset_crosschecks++;
      else host_cleanup_crosschecks++;
      `uvm_info("OCP_RESET_NATIVE_ATTRIBUTION", $sformatf(
        "slot=%0d old_epoch=%0d DRES_C_order=%0d monitor_order=%0d results=%h evidence=%s",
        d,c.epoch,event_order,item.order,item.results,
        item.results[0] === 1'b1 ? "NATIVE_PROTOCOL_RESET_BIT0" : "HOST_CLEANUP_BIT1_NOT_RESET"), UVM_LOW)
      return 1;
    end
    return 0;
  endfunction

  function void ocp_capture_axi(usb_ocp_event item);
    logic [31:0] value;
    logic [31:0] expected;
    string name;
    int dev;
    if (!item.response_ok || item.bytes.size() < 4)
      `uvm_fatal("OCP_RESET_AXI", "Reset observer received an unsuccessful AXI actual")
    value = core.ocp_get_le32(item.bytes,0);
    if (item.manager inside {0,2} && !item.write_access) begin
      dev = (item.manager == 0) ? 0 : 1;
      if (item.axi_address == core.device_command_address[dev] &&
          (value & dres_mask[dev]) === dres_mask[dev])
        ocp_check_usb_reset(item,dev);
    end
    if (window_open &&
        ((cfg.scope == usb_ocp_reset_control::DEV0 && item.manager inside {2,3}) ||
         (cfg.scope == usb_ocp_reset_control::DEV1 && item.manager == 0)))
      peer_axi++;
    if (window_open && cfg.scope == usb_ocp_reset_control::DEV1 &&
        item.manager == 0 && !item.write_access &&
        core.recovery_register.exists(item.axi_address) &&
        core.recovery_register[item.axi_address] == "INDIRECT_FIFO_DATA")
      peer_dma_bytes += item.bytes.size();
    if (item.manager != 0 || !core.recovery_register.exists(item.axi_address)) return;
    name = core.recovery_register[item.axi_address];
    if (item.write_access) begin
      if (cfg.armed && cfg.ocp_check_recovery_affected() &&
          (!cfg.retention_complete || !cfg.caliptra_quiescent))
        `uvm_fatal("OCP_RESET_OWNERSHIP", "Recovery writer preceded retention/old-byte quiescence")
      if (cfg.caliptra_quiescent && !cfg.mcu_reinitialized) begin
        if (!cfg.retention_complete || !(name inside {"DEVICE_STATUS_0","DEVICE_STATUS_1"}))
          `uvm_fatal("OCP_RESET_OWNERSHIP", "MCU exception exceeded DEVICE_STATUS ownership")
        if ((name == "DEVICE_STATUS_0" && value !==
             ((32'(OCP_REC_REASON_FORCED_RECOVERY)<<16) | OCP_DEVICE_STATUS_RECOVERY_MODE)) ||
            (name == "DEVICE_STATUS_1" && value !== 0))
          `uvm_fatal("OCP_RESET_REINIT", "MCU restored incorrect starting DEVICE_STATUS")
        reinit_writes++;
      end
      return;
    end
    // OCP 8.2.5 forbids random FIFO access. Only the ordinary already-
    // published old batch may complete after all retained-register reads.
    if (name == "INDIRECT_FIFO_DATA") begin
      if (cfg.armed && cfg.ocp_check_recovery_affected() && !cfg.fifo_reset_observed)
        ocp_check_old_fifo_bytes(item);
      return;
    end
    if (sampling == 0) return;
    if (item.axi_beats != 1 || $isunknown(value))
      `uvm_fatal("OCP_RESET_RETENTION", "Retention snapshot is not a known owned DWORD")
    if (sampling == 1) begin
      saved_register[name] = value;
      // OCP 9.2 defines clear-on-read at the recovery interface. Legal
      // stimulus keeps it zero; do not infer undocumented AXI read effects.
      if (name == "DEVICE_STATUS_0" && value[15:8] !== 0)
        `uvm_fatal("OCP_RESET_PRECONDITION", "Pre-event protocol error lacks a documented AXI clear-on-read baseline")
    end else if (sampling == 3) begin
      if (!ocp_check_command_service() || command_checkpoint_ready ||
          item.order < command_read_floor || !saved_register.exists(name) ||
          command_register.exists(name))
        `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Command snapshot read lacks its owned pre-reset phase/order")
      if (name == "RECOVERY_CTRL") begin
        if (ocp_check_command_fields(value,command_initial_ctrl,"OCP_RESET_COMMAND_EFFECT"))
          command_checkpoint_ctrl = value;
      end else if (value !== saved_register[name])
        `uvm_error("OCP_RESET_COMMAND_EFFECT", $sformatf(
          "Unrelated %s changed before reset: actual=%08h initial=%08h",
          name,value,saved_register[name]))
      command_register[name] = 1;
      command_reads++;
    end else begin
      if (!epoch_changed || !saved_register.exists(name))
        `uvm_fatal("OCP_RESET_RETENTION", "Post-reset read lacks a pre-event frontdoor value")
      expected = saved_register[name];
      if (name == "RECOVERY_CTRL" && cfg.stage == usb_ocp_reset_control::ACTIVATE)
        expected[23:0] = core.recovery_ctrl;
      if (cfg.negative == usb_ocp_reset_control::RETENTION &&
          !command_checkpoint_ready && retained_reads == 0)
        expected ^= 1;
      if (name == "RECOVERY_CTRL" && command_checkpoint_ready) begin
        bit valid;
        expected = command_checkpoint_ctrl;
        if (cfg.negative == usb_ocp_reset_control::RETENTION)
          expected[31:24] ^= 8'h01;
        valid = ocp_check_command_fields(value,expected,"OCP_RESET_RETENTION");
      end else if (value !== expected)
        `uvm_error("OCP_RESET_RETENTION", $sformatf(
          "%s pre-firmware read actual=%08h expected=%08h",name,value,expected))
      post_register[name] = 1;
      retained_reads++;
      retention_end_order = item.order;
    end
    if (name == "RECOVERY_CTRL" &&
        (sampling == 3 || (sampling == 2 && command_checkpoint_ready))) begin
      if (command_snapshot_reads.exists(item.order) || command_snapshot_reads.num() >= 2)
        `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Duplicate/unconsumed owned command-read expectation")
      command_snapshot_reads[item.order] = value;
    end
  endfunction

  function void ocp_capture_packet(usb_ocp_event item);
    usb_ocp_base_control c;
    bit incoming;
    // No new selected control is queued until old-native cleanup and drain.
    if (item.host_tx === 1'b1 && item.packet_valid === 1'b1 &&
        item.endpoint === 0 &&
        item.pid inside {svt_usb_packet::SETUP,svt_usb_packet::IN,svt_usb_packet::OUT}) begin
      foreach (interrupted[d]) begin
        c = interrupted[d];
        if (d != 0 && c != null && cleanup_requested[d] &&
            !cfg.event_complete && item.order >= cleanup_floor[d] &&
            item.address === c.address) begin
          cleanup_tokens[d]++;
          `uvm_error("OCP_RESET_HOST_REPLAY", $sformatf(
            "Post-DRES native cleanup replayed slot=%0d address=%0d PID=%s order=%0d cleanup_floor=%0d",
            d,item.address,item.pid.name(),item.order,cleanup_floor[d]))
        end
      end
    end
    if (!stage_tracking) return;
    c = core.control[stage_device];
    if (!c.active || c.generation != stage_generation) return;
    incoming = c.setup[0][7];
    // USB 2.0 8.5.3: a DATA-stage IN may NAK. Observe actual payload,
    // not its poll; the later ACK-qualified cut remains independently checked.
    if (cfg.stage == usb_ocp_reset_control::DATA && !stage_data_payload_seen &&
        c.active === 1'b1 && c.data.size() == 0 &&
        item.packet_valid === 1'b1 &&
        item.pid inside {svt_usb_packet::DATA0,svt_usb_packet::DATA1} &&
        (item.pid == svt_usb_packet::DATA1) === c.next_toggle[incoming] &&
        item.host_tx === !incoming && item.bytes.size() == c.ocp_get_length() &&
        core.token != null && core.token.packet_valid === 1'b1 &&
        core.token_device == stage_device &&
        core.token_epoch == c.epoch && core.token_generation == stage_generation &&
        core.token.endpoint === 0 && core.token.address === c.address &&
        core.token.pid == (incoming ? svt_usb_packet::IN : svt_usb_packet::OUT)) begin
      stage_data_payload_seen = 1;
      `uvm_info("OCP_RESET_DATA_TRIGGER", $sformatf(
        "slot=%0d generation=%0d bytes=%0d packet_order=%0d; received DATA is not ACK acceptance",
        stage_device,stage_generation,item.bytes.size(),item.order), UVM_LOW)
    end
    if (!item.host_tx || !item.packet_valid ||
        item.endpoint !== 0 || item.address !== core.address[stage_device] ||
        !(item.pid inside {svt_usb_packet::IN,svt_usb_packet::OUT})) return;
    incoming = (item.pid == svt_usb_packet::IN);
    if (c.ocp_get_length() == 0 || incoming != c.setup[0][7])
      stage_status_tokens++;
    else stage_data_tokens++;
  endfunction

  function void ocp_capture_control(int device);
    usb_ocp_base_control c;
    c = core.control[device];
    if (!cfg.armed) return;
    if (device == 0 && cfg.scope != usb_ocp_reset_control::BUS &&
        c.setup[4] == ((cfg.scope == usb_ocp_reset_control::DEV0) ? 1 : 2)) begin
      if (c.setup[0] === 8'h23 && c.setup[1] === 3 && c.ocp_get_value() === 4) begin
        if (window_seen)
          `uvm_fatal("OCP_RESET_SCOPE", "Duplicate selective reset command")
        window_open = 1;
        window_seen = 1;
        `uvm_info("OCP_RESET_WINDOW", $sformatf(
          "open scope=%s stage=%s port=%0d accepted=%0d returned=%0d",
          cfg.scope.name(),cfg.stage.name(),c.setup[4],core.accepted_bytes,
          core.returned_bytes), UVM_LOW)
      end
      if (window_open && c.setup[0] === 8'ha3 && c.setup[1] === 0 &&
          c.data.size() == 4 && c.data[0][4] === 0 &&
          c.data[0][1] === 1 && c.data[2][4] === 1) begin
        window_open = 0;
        `uvm_info("OCP_RESET_WINDOW", $sformatf(
          "close scope=%s stage=%s port=%0d status=%08h peer_USB=%0d peer_AXI=%0d peer_DMA_bytes=%0d",
          cfg.scope.name(),cfg.stage.name(),c.setup[4],core.ocp_get_le32(c.data,0),
          peer_controls,peer_axi,peer_dma_bytes), UVM_LOW)
      end
    end
    if (window_open &&
        ((cfg.scope == usb_ocp_reset_control::DEV0 && device == 2) ||
         (cfg.scope == usb_ocp_reset_control::DEV1 && device == 1)))
      peer_controls++;
    if (!cfg.ocp_check_recovery_affected() || !epoch_changed || device != 1) return;
    if (c.epoch <= saved_epoch[1])
      `uvm_fatal("OCP_RESET_EPOCH", "Post-reset command belongs to an old USB epoch")
    if (c.setup[0] === 8'ha1) begin
      case (c.setup[2])
        OCP_CMD_DEVICE_STATUS:
          if (c.data[0] === OCP_DEVICE_STATUS_RECOVERY_MODE) fresh_mode_reads++;
        OCP_CMD_PROT_CAP: begin
          if (fresh_mode_reads == 0 || !cfg.mcu_reinitialized)
            `uvm_fatal("OCP_RESET_DISCOVERY", "Capabilities precede fresh observed Recovery Mode")
          fresh_caps_reads++;
        end
        OCP_CMD_INDIRECT_FIFO_STATUS: fresh_fifo_reads++;
        default: begin end
      endcase
    end
    if (c.setup[0] === 8'h21 && c.setup[2] === OCP_CMD_INDIRECT_FIFO_CTRL &&
        c.data[1] === 1) begin
      if (!cfg.caliptra_quiescent || !cfg.mcu_reinitialized ||
          fresh_mode_reads == 0 || fresh_caps_reads == 0 || fresh_fifo_reads == 0 ||
          explicit_resets != 0 || old_returned != old_accepted ||
          old_compared != old_accepted ||
          (cfg.stage == usb_ocp_reset_control::PARTIAL && !old_batch_complete))
        `uvm_fatal("OCP_RESET_FIFO", "Explicit FIFO reset lacks quiescence/reinit/fresh discovery")
      explicit_resets++;
      cfg.fifo_reset_observed = 1;
    end
  endfunction

  function void ocp_check_retention_complete();
    if (retained_reads == 0 || !reset_seen[0] ||
        (cfg.scope == usb_ocp_reset_control::BUS && !reset_seen[1]))
      `uvm_fatal("OCP_RESET_RETENTION", "Missing actual affected reset or pre-firmware reads")
    foreach (saved_register[name])
      if (!post_register.exists(name))
        `uvm_fatal("OCP_RESET_RETENTION", $sformatf("Missing retained read %s",name))
    cfg.retention_complete = 1;
  endfunction

  function void ocp_check_abort_ack();
    if (!cfg.abort_requested || !epoch_changed || recovery_epoch != 0 ||
        !cfg.retention_complete || old_batch_active ||
        core.accepted_bytes != old_accepted || core.returned_bytes != old_accepted ||
        core.compared_bytes != old_accepted ||
        core.fifo_expected.size() != 0 || core.fifo_actual.size() != 0 ||
        (cfg.stage == usb_ocp_reset_control::PARTIAL && !old_batch_complete))
      `uvm_fatal("OCP_RESET_QUIESCENCE", "Abort acknowledgement lacks actual reset/accounted returned bytes")
    // Keep the completed old ledger independently of the later canonical
    // explicit FIFO reset and fresh image counters.
    old_returned = core.returned_bytes;
    old_compared = core.compared_bytes;
    `uvm_info("OCP_RESET_OLD_ACCOUNTING", $sformatf(
      "scope=%s stage=%s accepted=%0d entry_returned=%0d entry_compared=%0d returned=%0d compared=%0d POST_bytes=%0d POST_compared=%0d POST_bursts=%0d POST_AXI_instances=%p retention_end_order=%0d POST_orders=%0d..%0d byte_errors=%0d",
      cfg.scope.name(),cfg.stage.name(),old_accepted,old_entry_returned,
      old_entry_compared,old_returned,old_compared,old_fifo_actual.size(),
      old_post_compared,old_post_bursts,old_post_instances,retention_end_order,
      old_first_axi_order,old_last_axi_order,old_byte_errors), UVM_LOW)
    // USB invalidation does not change this epoch. The old recovery attempt
    // retires only at its accounted firmware acknowledgement, retaining FIFO.
    recovery_epoch++;
  endfunction

  function void ocp_check_complete();
    int expected_interrupts;
    bit peer_ok;
    int unsigned final_epoch[3];
    if (finished) return;
    expected_interrupts = (cfg.stage inside {usb_ocp_reset_control::SETUP,
      usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS}) ? 1 : 0;
    peer_ok = peer_controls != 0 && peer_axi != 0;
    if (cfg.negative == usb_ocp_reset_control::PEER) peer_ok = 0;
    if (!cfg.event_complete || !epoch_changed || command_snapshot_reads.num() != 0 ||
        old_control_crosschecks != expected_interrupts ||
        old_control_invalidations != expected_interrupts ||
        native_reset_crosschecks+host_cleanup_crosschecks != expected_interrupts ||
        (cfg.scope == usb_ocp_reset_control::BUS &&
         (native_reset_crosschecks != expected_interrupts || host_cleanup_crosschecks != 0)))
      `uvm_fatal("OCP_RESET_INCOMPLETE", "Missing actual reset or interrupted crosscheck")
    if (cfg.scope != usb_ocp_reset_control::BUS && !peer_ok)
      `uvm_error("OCP_RESET_PEER", "Missing during-event unaffected USB/AXI progress")
    if (cfg.scope == usb_ocp_reset_control::DEV1 &&
        cfg.stage == usb_ocp_reset_control::PARTIAL && peer_dma_bytes == 0)
      `uvm_fatal("OCP_RESET_PEER", "Partial DEV1 reset lacks actual concurrent recovery DMA")
    foreach (saved_epoch[d])
      if (core.control[d].epoch != saved_epoch[d]+int'(cfg.ocp_check_device_affected(d)))
        `uvm_fatal("OCP_RESET_SCOPE", "Affected/unaffected USB epoch changed incorrectly")
    if (cfg.ocp_check_recovery_affected()) begin
      if (cfg.stage inside {usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS} &&
          !command_checkpoint_ready)
        `uvm_fatal("OCP_RESET_INCOMPLETE", "Missing validated pre-event command-effects checkpoint")
      if (!cfg.retention_complete || !cfg.caliptra_quiescent ||
          !cfg.mcu_reinitialized || reinit_writes != 2 || explicit_resets != 1 ||
          fresh_mode_reads == 0 || fresh_caps_reads == 0 || fresh_fifo_reads == 0 ||
          recovery_epoch != 1)
        `uvm_fatal("OCP_RESET_INCOMPLETE", "Missing retention/quiescence/ownership/discovery/FIFO-reset proof")
      if (old_returned != old_accepted || old_compared != old_accepted ||
          old_batch_active ||
          (cfg.stage == usb_ocp_reset_control::PARTIAL &&
           (!old_batch_complete || old_fifo_actual.size() != old_accepted ||
            old_post_compared != old_accepted || old_post_bursts != 4 ||
            old_first_axi_order <= retention_end_order)))
        `uvm_fatal("OCP_RESET_BYTE_RETENTION", "Missing preserved completed old accounting/POST-reset content witness")
    end else if (cfg.abort_requested || explicit_resets != 0 || recovery_epoch != 0)
      `uvm_fatal("OCP_RESET_SCOPE", "DEV1 reset disturbed unaffected OCP recovery")
    final_epoch = '{core.control[0].epoch,core.control[1].epoch,core.control[2].epoch};
    finished = 1;
    `uvm_info("OCP_RESET_EVIDENCE", $sformatf(
      "scope=%s stage=%s USB_epochs=%p final_USB_epochs=%p recovery_epoch=%0d old_accepted=%0d old_entry_returned=%0d old_entry_compared=%0d old_returned=%0d old_compared=%0d old_POST_bytes=%0d old_POST_compared=%0d old_POST_bursts=%0d old_POST_orders=%0d..%0d old_byte_errors=%0d retention=%0d old_invalidations=%0d old_crosschecks=%0d native_reset_bit0=%0d HOST_cleanup_bit1=%0d peer_USB=%0d peer_AXI=%0d peer_DMA_bytes=%0d",
      cfg.scope.name(),cfg.stage.name(),saved_epoch,final_epoch,recovery_epoch,
      old_accepted,old_entry_returned,old_entry_compared,old_returned,old_compared,
      old_fifo_actual.size(),old_post_compared,old_post_bursts,old_first_axi_order,
      old_last_axi_order,old_byte_errors,retained_reads,old_control_invalidations,
      old_control_crosschecks,native_reset_crosschecks,host_cleanup_crosschecks,
      peer_controls,peer_axi,peer_dma_bytes), UVM_LOW)
  endfunction
endclass
