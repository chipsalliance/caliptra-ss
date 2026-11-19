// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_reset_reinit_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_reset_reinit_host_seq)
  // USB 2.0 9.4.7: zero configuration returns a configured device to Address.
  localparam bit [15:0] OCP_USB_UNCONFIGURED = 16'h0000;
  usb_ocp_reset_model reset_model;
  usb_ocp_scoreboard scoreboard;
  usb_ocp_reset_reinit_host_seq port_host;
  usb_ocp_reset_reinit_host_seq parent_host;
  usb_ocp_reset_service_seq reset_service;
  usb_ocp_reset_link_callback reset_callback;
  usb_ocp_reset_start_callback start_callback;
  usb_ocp_reset_protocol_seq protocol_services[$];
  int unsigned protocol_launch_requests;
  bit reset_launch_requested;
  bit service_dispatch_stop;
  bit service_dispatch_finished;
  process service_dispatch_process;
  svt_usb_endpoint_status interrupted_endpoint;
  bit native_release_requested;
  bit port_actor;
  bit cancelling;
  bit interrupted_started;
  bit fresh;
  bit event_started;
  bit reconfigure_pending;
  int unsigned submission_inflight;
  svt_usb_transfer interrupted_request;
  int unsigned interrupted_device;
  time native_reset_timeout = 5ms;

  function new(string name = "usb_ocp_reset_reinit_host_seq");
    super.new(name);
    protocol_launch_requests = 0;
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    // Cross a publication batch and finish with a two-DWORD remainder.
    // Firmware still learns all geometry and length from its frontdoors.
    words = 130;
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    int remaining;
    int wrap_remaining;
    if (fresh ||
        reset_model.cfg.stage != usb_ocp_reset_control::PARTIAL) return;
    if (!reset_model.cfg.ocp_check_recovery_affected()) begin
      if (offset != 0) return;
      chunk_words = (chunk_limit < 16) ? chunk_limit : 16;
      if (chunk_words == 0 || chunk_words >= words)
        `uvm_fatal("OCP_RESET_IMAGE", "No legal initial partial image chunk")
      return;
    end
    // The verification charter permits full advertised FIFO occupancy,
    // including equal indices. Keep discovered CMS/USB command limits and
    // require publication of a normal 64-DWORD firmware batch.
    if (fifo_depth < 64 || words <= 64 || chunk_limit == 0)
      `uvm_fatal("OCP_RESET_PUBLICATION",
        "Discovered FIFO depth must hold the normal 64-DWORD published batch")
    if (offset >= 64) return;
    remaining = 64-offset;
    wrap_remaining = fifo_depth-(offset%fifo_depth);
    chunk_words = (chunk_limit < 16) ? chunk_limit : 16;
    if (chunk_words > remaining) chunk_words = remaining;
    if (chunk_words > wrap_remaining) chunk_words = wrap_remaining;
    if (chunk_words == 0 || chunk_words > max_write/4 ||
        chunk_words > fifo_max || chunk_words > fifo_depth)
      `uvm_fatal("OCP_RESET_IMAGE", "No legal published-partial image chunk")
  endfunction

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    svt_usb_device_status native_device;
    svt_usb_endpoint_status native_endpoint;
    if (!port_actor && device == 2 && reset_model.epoch_changed &&
        port_host != null && port_host.completed) begin
      native_device = shared_status.get_device_status(tr.device_address);
      if (native_device == null)
        `uvm_fatal("OCP_RESET_ROUTING", "Post-enumeration request lacks native device status")
      native_endpoint = native_device.get_endpoint_status(
        0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
      if (native_endpoint == null)
        `uvm_fatal("OCP_RESET_ROUTING", "Post-enumeration request lacks native endpoint status")
      `uvm_info("OCP_RESET_ROUTING", $sformatf(
        "post-enumeration parent request sequence=%0d transaction=%0d address=%0d paused=%s old_endpoint_same=%0b port_completed=%0b port_sequence_state=%0d native_release_requested=%0b dispatch_finished=%0b",
        tr.get_sequence_id(),tr.get_transaction_id(),tr.device_address,
        native_endpoint.processing_paused.name(),
        native_endpoint == port_host.interrupted_endpoint,port_host.completed,
        port_host.get_sequence_state(),port_host.native_release_requested,
        port_host.service_dispatch_finished), UVM_LOW)
      foreach (port_host.protocol_services[i])
        `uvm_info("OCP_RESET_ROUTING", $sformatf(
          "selected issuer index=%0d operation=%s executed=%0b responses=%0d release=%0b finished=%0b sequence_state=%0d",
          i,port_host.protocol_services[i].operation.name(),
          port_host.protocol_services[i].executed,
          port_host.protocol_services[i].responses,
          port_host.protocol_services[i].release_requested,
          port_host.protocol_services[i].finished,
          port_host.protocol_services[i].get_sequence_state()), UVM_LOW)
    end
    if (cancelling && device == interrupted_device && !reset_model.epoch_changed) begin
      if (tr == null || start_callback == null || start_callback.original != null)
        `uvm_fatal("OCP_RESET_START", "Missing or already armed original start callback")
      if (!port_actor && reset_model.cfg.stage == usb_ocp_reset_control::STATUS &&
          (tr.setup_data_bmrequesttype_dir !== 1'b0 ||
           tr.setup_data_w_length != OCP_SPEC_LEN_RECOVERY_CTRL ||
           tr.setup_data_w_value != OCP_CMD_RECOVERY_CTRL))
        `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Timeout response requires the original OCP CONTROL write")
      start_callback.original = tr;
      start_callback.status_timeout_requested = !port_actor &&
        reset_model.cfg.ocp_check_recovery_affected() &&
        reset_model.cfg.stage == usb_ocp_reset_control::STATUS;
      reset_model.stage_tracking = 1;
      reset_model.stage_device = device;
      reset_model.stage_generation = scoreboard.model.control[device].generation+1;
    end
  endfunction

  virtual function int ocp_configure_control_priority(int device);
    // Native priority is randomized within the documented <100 constraint:
    // hub 99, either selected child 0; no post-randomization bypass.
    return device == 0 ? 99 : 0;
  endfunction

  virtual function void ocp_check_interrupted_result(usb_ocp_event observed);
    reset_model.ocp_check_native_result(observed,interrupted_device);
  endfunction

  task ocp_poll_check_observation(bit usb_idle = 1, bit axi_retired = 1);
    while ((usb_idle && !observer.ocp_check_usb_idle()) || scoreboard.busy ||
           !observer.ocp_check_snapshots_consumed() ||
           (axi_retired && scoreboard.deferred_axi.size() != 0) ||
           scoreboard.model.ready_controls.size() != 0) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_OBSERVER", "Completed-request observation did not retire")
      #1us;
    end
  endtask

  task ocp_poll_check_snapshot();
    while (!reset_model.snapshot_ready) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_BOUNDARY", "Owned initial snapshot checkpoint deadline")
      #1us;
    end
  endtask

  task ocp_do_check_service_dispatch();
    int unsigned next_protocol = 0;
    bit reset_started = 0;
    // Per-control timeout forks cancel descendants. Keep held native issuers
    // under the host's outer lifetime, not inside a cancellable control fork.
    service_dispatch_process = process::self();
    while (!service_dispatch_stop) begin
      wait (service_dispatch_stop ||
            (!reset_started && reset_launch_requested) ||
            next_protocol < protocol_launch_requests);
      if (!reset_started && reset_launch_requested) begin
        if (reset_service == null)
          `uvm_fatal("OCP_RESET_NATIVE", "Native launch lacks its owned reset issuer")
        `uvm_info("OCP_RESET_DISPATCH", "Launching owned native reset issuer", UVM_LOW)
        reset_started = 1;
        fork
          reset_service.start(p_sequencer.link_service_sequencer,this);
        join_none
      end
      if (next_protocol < protocol_launch_requests) begin
        if (next_protocol >= protocol_services.size() ||
            protocol_launch_requests != protocol_services.size())
          `uvm_fatal("OCP_RESET_PROTOCOL", "Native launch queue lost an owned scoped issuer")
        begin
          automatic usb_ocp_reset_protocol_seq service = protocol_services[next_protocol];
          if (service == null)
            `uvm_fatal("OCP_RESET_PROTOCOL", "Native launch queue contains a null issuer")
          `uvm_info("OCP_RESET_DISPATCH", $sformatf(
            "Launching scoped issuer index=%0d cmd=%s target=%0d",
            next_protocol,service.operation.name(),service.target_address), UVM_LOW)
          next_protocol++;
          fork
            service.start(p_sequencer,this);
          join_none
        end
      end
    end
    wait fork;
    service_dispatch_finished = 1;
  endtask

  task ocp_do_check_port_reset(int port);
    bytes_t empty;
    bytes_t data;
    // USB 2.0 11.24.2.13: reset only the selected downstream port.
    ocp_do_check_control(0,8'h23,3,4,16'(port),0,empty,data);
    do begin
      #(usb_cfg.tdrst * 1ps);
      ocp_do_check_control(0,8'ha3,0,0,16'(port),4,empty,data);
      if (data.size() != 4 || $isunknown({data[3],data[2],data[1],data[0]}))
        `uvm_fatal("OCP_RESET_PORT", "Unknown/short reset port status")
      if (data[0][4] === 0 && data[0][1] === 1 && data[2][4] === 1) break;
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_PORT", "Selected port reset/enable/change deadline")
    end while (1);
    if (data[0][0] !== 1 || data[1][0] !== 1 || data[1][2:1] !== 2'b10)
      `uvm_fatal("OCP_RESET_PORT", "Selected port lost connection/power/HS")
    ocp_do_check_control(0,8'h23,1,20,16'(port),0,empty,data);
    #(usb_cfg.trstrcy * 1ps);
  endtask

  task ocp_do_check_bus_reset();
    time native_deadline;
    if (host_agent.link == null)
      `uvm_fatal("OCP_RESET_NATIVE", "Missing native host link")
    if (reset_launch_requested)
      `uvm_fatal("OCP_RESET_NATIVE", "Duplicate native reset launch")
    native_deadline = $time + native_reset_timeout;
    reset_service = usb_ocp_reset_service_seq::type_id::create("reset_service");
    reset_callback = usb_ocp_reset_link_callback::type_id::create("reset_callback");
    reset_callback.issuer = reset_service;
    uvm_callbacks#(svt_usb_link)::add(host_agent.link,reset_callback);
    reset_launch_requested = 1;
    while (!reset_service.ocp_check_executed() || !reset_model.reset_seen[0] ||
           !reset_model.reset_seen[1] ||
           shared_status.link_usb_20_state !== svt_usb_types::ENABLED ||
           shared_status.link_usb_20_power_state !== svt_usb_types::POWER_STATE_L0 ||
           shared_status.physical_usb_20_working_speed !== svt_usb_types::HS) begin
      if ($time >= native_deadline || $time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE", $sformatf(
          "Native BUS reset deadline: issued=%0d ingress=%0d executed=%0b finished=%0b reset_seen=%p retention=%0b quiescent=%0b mcu_reinitialized=%0b link=%s power=%s speed=%0d required_speed=%0d",
          reset_service.issued.size(),reset_service.ingress,
          reset_service.ocp_check_executed(),reset_service.finished,
          reset_model.reset_seen,reset_model.cfg.retention_complete,
          reset_model.cfg.caliptra_quiescent,reset_model.cfg.mcu_reinitialized,
          shared_status.link_usb_20_state.name(),
          shared_status.link_usb_20_power_state.name(),
          shared_status.physical_usb_20_working_speed,svt_usb_types::HS))
      #1us;
    end
    #(usb_cfg.trstrcy * 1ps);
  endtask

  task ocp_do_check_peer_window();
    usb_ocp_base_ep0_peer_seq peer;
    if (reset_model.cfg.scope != usb_ocp_reset_control::DEV0) return;
    while (!reset_model.window_open) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_PEER", "Selected reset never opened a real hub status window")
      #1us;
    end
    peer = usb_ocp_base_ep0_peer_seq::type_id::create("unaffected_dev1");
    peer.peer_device = 2;
    peer.peer_schedule_priority = 98;
    peer.expected_configuration = configuration_value[2];
    peer.expected_descriptor = device_descriptor_bytes[2];
    peer.ocp_cfg = ocp_cfg;
    peer.observer = observer;
    peer.start(p_sequencer,this);
    if (!peer.completed)
      `uvm_fatal("OCP_RESET_PEER", "Unaffected-device in-event peer did not finish")
  endtask

  task ocp_do_check_reset_event();
    reset_model.cfg.event_dispatched = 1;
    if (reset_model.cfg.scope == usb_ocp_reset_control::BUS) begin
      ocp_do_check_bus_reset();
    end else begin
      fork
        ocp_do_check_port_reset(
          reset_model.cfg.scope == usb_ocp_reset_control::DEV0 ? 1 : 2);
        ocp_do_check_peer_window();
      join
    end
    while (!reset_model.epoch_changed ||
           (reset_model.cfg.scope == usb_ocp_reset_control::DEV0 && !reset_model.reset_seen[0]) ||
           (reset_model.cfg.scope == usb_ocp_reset_control::DEV1 && !reset_model.reset_seen[1])) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_SCOPE", "Selected event lacks actual owned hardware reset indication")
      #1us;
    end
    if (reset_model.cfg.ocp_check_recovery_affected()) begin
      while (!reset_model.cfg.mcu_reinitialized) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_REINIT", "Retention/abort/MCU reinitialization deadline")
        #1us;
      end
    end
    if (interrupted_request != null) ocp_do_check_old_native_cleanup();
    // End the during-event progress window BEFORE reenumbering its target.
    if (reset_model.cfg.scope == usb_ocp_reset_control::DEV1) begin
      if (parent_host == null || parent_host.port_host != this)
        `uvm_fatal("OCP_RESET_ROUTING", "Selected-port actor lacks its live parent owner")
      parent_host.reconfigure_pending = 1;
      `uvm_info("OCP_RESET_ROUTING", $sformatf(
        "freeze time=%0t slot=1 submission_inflight=%0d reconfigure_pending=%0b monitor_starts_global=%0d monitor_ends_global=%0d",
        $time,parent_host.submission_inflight,parent_host.reconfigure_pending,
        observer.transfer_starts,observer.transfer_count), UVM_LOW)
    end
    reset_model.cfg.event_complete = 1;
    if (reset_model.cfg.scope == usb_ocp_reset_control::DEV1) begin
      // Reconfiguration has no documented unaffected-pipe cancellation
      // guarantee. Retire its current native CONTROL before updating routing.
      while (parent_host.submission_inflight != 0 ||
             scoreboard.model.control[1].active ||
             scoreboard.model.transfer_crosschecks[1] != scoreboard.model.usb_completions[1] ||
             scoreboard.model.ready_controls.size() != 0 || scoreboard.busy ||
             !observer.ocp_check_snapshots_consumed()) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_ROUTING", "Unaffected control did not retire before target enumeration")
        #1us;
      end
      `uvm_info("OCP_RESET_ROUTING", $sformatf(
        "reconfigure time=%0t slot=1 submission_inflight=%0d reconfigure_pending=%0b monitor_starts_global=%0d monitor_ends_global=%0d",
        $time,parent_host.submission_inflight,parent_host.reconfigure_pending,
        observer.transfer_starts,observer.transfer_count), UVM_LOW)
      ocp_do_check_enumeration(2);
      parent_host.reconfigure_pending = 0;
    end
  endtask

  task ocp_do_check_protocol(svt_usb_protocol_service::protocol_command_type_enum operation);
    usb_ocp_reset_protocol_seq service;
    time command_deadline;
    if (interrupted_request == null || interrupted_endpoint == null)
      `uvm_fatal("OCP_RESET_PROTOCOL", "Scoped command lacks the original live endpoint")
    if (operation != svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING &&
        (!reset_model.epoch_changed || !reset_model.reset_seen[interrupted_device-1] ||
         reset_model.interrupted[interrupted_device] == null ||
         scoreboard.model.control[interrupted_device].active !== 1'b0))
      `uvm_fatal("OCP_RESET_HOST_CLEANUP", "Cancellation/RESUME attempted before actual hardware reset/old-control invalidation")
    if (operation == svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER &&
        (reset_model.cfg.scope == usb_ocp_reset_control::BUS ||
         !reset_model.cleanup_requested[interrupted_device] ||
         (reset_model.cfg.ocp_check_recovery_affected() &&
          (!reset_model.cfg.retention_complete || !reset_model.cfg.mcu_reinitialized))))
      `uvm_fatal("OCP_RESET_HOST_CLEANUP", "Immediate native abort lacks accounted selective reset/retention/MCU reinitialization")
    if (service_dispatch_process == null ||
        service_dispatch_process.status() inside {process::KILLED,process::FINISHED})
      `uvm_fatal("OCP_RESET_DISPATCH", "Scoped request lacks its live native dispatcher")
    command_deadline = $time + native_reset_timeout;
    `uvm_info("OCP_RESET_DISPATCH", $sformatf(
      "Request cmd=%s target=%0d dispatcher_state=%0d",
      operation.name(),interrupted_request.device_address,
      service_dispatch_process.status()), UVM_LOW)
    service = usb_ocp_reset_protocol_seq::type_id::create("scoped_protocol_service");
    service.operation = operation;
    service.target_address = interrupted_request.device_address;
    service.ocp_cfg = ocp_cfg;
    service.observer = observer;
    protocol_services.push_back(service);
    protocol_launch_requests = protocol_services.size();
    while (!service.executed) begin
      if ($time >= command_deadline || $time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_PROTOCOL", "Scoped native command end/correlation deadline")
      #1us;
    end
  endtask

  task ocp_do_check_old_native_cleanup();
    usb_ocp_event native_end;
    usb_ocp_base_service_callback actual;
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed;
    time original_deadline;
    actual = observer.service_callback;
    // BUS must end the held original with native reset bit0; never introduce
    // an abort command to manufacture that result. Selective host bookkeeping
    // is allowed only after independently observed selected DRES_C/epoch.
    if (reset_model.cfg.scope != usb_ocp_reset_control::BUS &&
        actual.mixed_native_abort == null) begin
      if (interrupted_endpoint.processing_paused !== svt_usb_endpoint_status::IS_PAUSED ||
          interrupted_request.status === svt_sequence_item::ABORTED)
        `uvm_fatal("OCP_RESET_HOST_CLEANUP", "Original is not a live paused host-cache entry after selected reset")
      reset_model.ocp_check_host_cleanup(interrupted_device,observer.next_order);
      ocp_do_check_protocol(svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER);
    end
    original_deadline = $time + native_reset_timeout;
    while (actual.mixed_native_abort == null) begin
      if ($time >= original_deadline || $time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE_GAP", $sformatf(
          "Original native end deadline after actual DRES_C=%0d: sequence=%0d transaction=%0d status=%s results=%h paused=%0d command=%0d command_return_status=%0d immediate_abort=%0b; no speculative RESUME or fabricated end",
          reset_model.event_order,interrupted_request.get_sequence_id(),
          interrupted_request.get_transaction_id(),interrupted_request.status.name(),
          interrupted_request.results_status,interrupted_endpoint.processing_paused,
          actual.command,actual.return_status,actual.force_immediate_abort))
      #1us;
    end
    if (actual.native_end_sequence_id != interrupted_request.get_sequence_id() ||
        actual.native_end_transaction_id != interrupted_request.get_transaction_id())
      `uvm_fatal("OCP_RESET_NATIVE", "Original end callback has a different native issuer identity")
    actual.ocp_wait_native_abort(native_end);
    allowed = 0;
    allowed[0] = 1;
    if (!native_end.setup[0][7]) allowed[5] = 1;
    if (reset_model.cfg.scope != usb_ocp_reset_control::BUS &&
        reset_model.cleanup_requested[interrupted_device])
      allowed[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] = 1;
    if (!native_end.native_aborted || (native_end.results & ~allowed) !== 0 ||
        !((native_end.results[0] === 1'b1 &&
           native_end.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1'b0) ||
          (native_end.results[0] === 1'b0 &&
           native_end.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] === 1'b1)))
      `uvm_fatal("OCP_RESET_NATIVE_ATTRIBUTION", "Original did not end with real native ABORTED/reset attribution")
    `uvm_info("OCP_RESET_NATIVE_END", $sformatf(
      "original sequence=%0d transaction=%0d after DRES_C=%0d native_results=%h; bit1 is HOST cleanup, not hardware reset",
      interrupted_request.get_sequence_id(),interrupted_request.get_transaction_id(),
      reset_model.event_order,native_end.results), UVM_LOW)
    if (interrupted_endpoint.processing_paused === svt_usb_endpoint_status::IS_PAUSED) begin
      // The old transfer already ENDED/ABORTED and no future selected-child
      // control is queued. RESUME only unlocks host cache; it cannot replay
      // the original or supply evidence that the DUT cleared its old control.
      `uvm_info("OCP_RESET_HOST_CLEANUP", "POST-reset RESUME of ended original endpoint; HOST bookkeeping only", UVM_LOW)
      ocp_do_check_protocol(svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING);
    end
    while (interrupted_endpoint.processing_paused !== svt_usb_endpoint_status::NOT_PAUSED) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE_GAP", "Old endpoint pause cache did not clear before fresh routing")
      #1us;
    end
    ocp_poll_check_observation(0,0);
    if (reset_model.cleanup_requested[interrupted_device])
      `uvm_info("OCP_RESET_HOST_CLEANUP", $sformatf(
        "slot=%0d post-DRES old_tokens=%0d; original native end and observation drain precede fresh routing",
        interrupted_device,reset_model.cleanup_tokens[interrupted_device]), UVM_LOW)
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    svt_usb_device_status native_device;
    usb_ocp_base_control c;
    time boundary_deadline;
    bit stage_ready = 0;
    if (!cancelling || device != interrupted_device || reset_model.epoch_changed) return;
    if (start_callback == null || start_callback.original != tr)
      `uvm_fatal("OCP_RESET_START", "Original was not armed before native submission")
    if (reset_model.cfg.stage == usb_ocp_reset_control::DATA &&
        (tr.setup_data_w_length == 0 || tr.setup_data_w_length >
         usb_cfg.remote_device_cfg[device].endpoint_cfg[0].max_packet_size))
      `uvm_fatal("OCP_RESET_STAGE", "DATA pause requires one discovered-size data transaction")
    interrupted_request = tr;
    native_device = shared_status.get_device_status(tr.device_address);
    if (native_device == null)
      `uvm_fatal("OCP_RESET_PAUSE", "Original lacks native device shared status")
    interrupted_endpoint = native_device.get_endpoint_status(0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
    if (interrupted_endpoint == null ||
        interrupted_endpoint.processing_paused !== svt_usb_endpoint_status::NOT_PAUSED)
      `uvm_fatal("OCP_RESET_PAUSE", "Original endpoint was not initially unpaused")
    observer.service_callback.ocp_configure_abort_capture(tr.device_address,
      '{ {1'(tr.setup_data_bmrequesttype_dir),2'(tr.setup_data_bmrequesttype_type),
          5'(tr.setup_data_bmrequesttype_recipient)},tr.setup_data_brequest,
         tr.setup_data_w_value[7:0],tr.setup_data_w_value[15:8],
         tr.setup_data_w_index[7:0],tr.setup_data_w_index[15:8],
         tr.setup_data_w_length[7:0],tr.setup_data_w_length[15:8] });
    // USB 2.0 8.5.3.1 permits busy STATUS NAKs. A STATUS poll only triggers
    // PAUSE; the cut rejects any completed STATUS or ended original.
    fork
      begin
        fork
          begin
            wait (start_callback.started);
            case (reset_model.cfg.stage)
              usb_ocp_reset_control::SETUP: begin end
              usb_ocp_reset_control::DATA:
                wait (reset_model.stage_data_payload_seen);
              usb_ocp_reset_control::STATUS:
                wait (reset_model.stage_status_tokens > 0);
              default: `uvm_fatal("OCP_RESET_STAGE", "Unexpected interrupted control boundary")
            endcase
            stage_ready = 1;
          end
          begin #(native_reset_timeout); end
        join_any
        disable fork;
      end
    join
    if (!stage_ready)
      `uvm_fatal("OCP_RESET_STAGE", "Original native start/complete DATA packet/STATUS poll deadline")
    ocp_do_check_protocol(svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING);
    while (interrupted_endpoint.processing_paused !== svt_usb_endpoint_status::IS_PAUSED) begin
      if (observer.service_callback.mixed_native_abort != null ||
          tr.status === svt_sequence_item::ABORTED)
        `uvm_fatal("OCP_RESET_STAGE", "Original ended before transaction-boundary PAUSE caught the selected stage")
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_PAUSE", "Actual native transaction-boundary pause deadline")
      #1us;
    end
    if (start_callback.status_timeout_requested) begin
      `uvm_info("OCP_RESET_STATUS_RESPONSE", $sformatf(
        "original_type=%s native_response_updates=%0d native_end_seen=%0b transfer_status=%0d; no omission or survival credit",
        tr.get_type_name(),start_callback.status_timeout_responses,
        observer.service_callback.mixed_native_abort != null,tr.status), UVM_NONE)
      if (start_callback.status_timeout_responses == 0)
        `uvm_fatal("OCP_RESET_STATUS_RESPONSE", "Original native STATUS response callback was not applied")
      reset_model.status_processing_paused = 1;
      reset_model.status_processing_paused_at = $realtime;
      `uvm_info("OCP_RESET_STATUS_PAUSE", $sformatf(
        "original_sequence=%0d original_transaction=%0d implementation_index=%0d processing_paused=%s; no transaction or STATUS completion credit",
        tr.get_sequence_id(),tr.get_transaction_id(),
        start_callback.status_timeout_index,
        interrupted_endpoint.processing_paused.name()), UVM_NONE)
    end
    if (observer.service_callback.mixed_native_abort != null ||
        tr.status === svt_sequence_item::ABORTED)
      `uvm_fatal("OCP_RESET_STAGE", "PAUSE did not retain the original incomplete transfer")
    if (reset_model.cfg.stage inside {usb_ocp_reset_control::SETUP,
        usb_ocp_reset_control::DATA}) begin
      // PAUSE0 completes admitted transactions, not an entire DATA stage.
      // Native PAUSE acceptance is not passive ACK-qualified cut evidence.
      boundary_deadline = $time + native_reset_timeout;
      forever begin
        c = scoreboard.model.control[device];
        if (c == null || observer.service_callback.mixed_native_abort != null ||
            tr.status === svt_sequence_item::ABORTED)
          `uvm_fatal("OCP_RESET_STAGE", "Original ended before its accepted boundary")
        if (c.generation > reset_model.stage_generation ||
            (c.generation == reset_model.stage_generation &&
             (c.status_acked !== 1'b0 || reset_model.stage_status_tokens != 0)))
          reset_model.ocp_check_stage_cut(c);
        if (c.active === 1'b1 && c.generation == reset_model.stage_generation &&
            (reset_model.cfg.stage == usb_ocp_reset_control::SETUP ||
             c.data.size() == c.ocp_get_length())) break;
        if ($time >= boundary_deadline || $time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_STAGE", $sformatf(
            "Accepted boundary deadline: stage=%s active=%0b generation=%0d required_generation=%0d DATA=%0d/%0d DATA_tokens=%0d STATUS_tokens=%0d STATUS_ACK=%0b",
            reset_model.cfg.stage.name(),c.active,c.generation,
            reset_model.stage_generation,c.data.size(),c.ocp_get_length(),
            reset_model.stage_data_tokens,reset_model.stage_status_tokens,
            c.status_acked))
        #1us;
      end
    end
    ocp_poll_check_observation(0,0);
    if (reset_model.cfg.ocp_check_recovery_affected() &&
        reset_model.cfg.stage inside {usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS}) begin
      reset_model.ocp_configure_command_checkpoint();
      boundary_deadline = $time + native_reset_timeout;
      while (!reset_model.command_checkpoint_ready) begin
        if ($time >= boundary_deadline || $time >= reset_model.cfg.deadline ||
            observer.service_callback.mixed_native_abort != null ||
            tr.status === svt_sequence_item::ABORTED ||
            interrupted_endpoint.processing_paused !== svt_usb_endpoint_status::IS_PAUSED)
          `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Original/checkpoint did not survive until pre-reset read retirement")
        #1us;
      end
      ocp_poll_check_observation(0,0);
    end
    reset_model.ocp_check_stage_cut(scoreboard.model.control[device]);
    // Tracking remains armed through actual DRES_C, where the same passive
    // guard is repeated. PAUSE/end responses alone establish no DUT reset.
    ocp_do_check_reset_event();
  endtask

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    if (tr != interrupted_request) return;
    while (!reset_model.cfg.event_complete) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE", "Reset event did not finish before old issuer retirement")
      #1us;
    end
  endtask

  virtual task ocp_wait_replaced_prefix(usb_ocp_event observed, output bytes_t prefix);
    while (!reset_model.interrupt_checked[interrupted_device]) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_PREFIX", "Old epoch lacks passive native-prefix crosscheck")
      #1us;
    end
    if (reset_model.interrupt_serial[interrupted_device] != observed.transfer_serial)
      `uvm_fatal("OCP_RESET_PREFIX", "Old native completion belongs to another issuer")
    prefix = reset_model.interrupted[interrupted_device].data;
  endtask

  task ocp_do_start_port_actor();
    if (port_host != null)
      `uvm_fatal("OCP_RESET_ACTORS", "Duplicate reset port actor")
    port_host = usb_ocp_reset_reinit_host_seq::type_id::create("port_host");
    port_host.parent_host = this;
    port_host.port_actor = 1;
    port_host.reset_model = reset_model;
    port_host.scoreboard = scoreboard;
    port_host.ocp_cfg = ocp_cfg;
    port_host.observer = observer;
    port_host.configuration_value = configuration_value;
    foreach (device_descriptor_bytes[d])
      port_host.device_descriptor_bytes[d] = device_descriptor_bytes[d];
    fork
      port_host.start(p_sequencer,this);
    join_none
  endtask

  virtual task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
      logic [15:0] value, logic [15:0] index, logic [15:0] length,
      bytes_t write_data, output bytes_t read_data, input bit expect_replacement = 0);
    bit selected;
    bit track_submission;
    if (expect_replacement)
      `uvm_fatal("OCP_RESET_NATIVE", "Nested abort/replacement is not a reset variant")
    track_submission = !port_actor && device == 1 &&
                       reset_model.cfg.scope == usb_ocp_reset_control::DEV1;
    if (track_submission) begin
      // Admission and lifetime registration have no intervening blocking work.
      while (reconfigure_pending) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_ROUTING", "Selected target reconfiguration did not release submissions")
        #1us;
      end
      submission_inflight++;
    end
    selected = !fresh && !interrupted_started &&
      ((port_actor && device == 2 &&
        ((request == 6 && reset_model.cfg.stage inside {
            usb_ocp_reset_control::SETUP,usb_ocp_reset_control::DATA}) ||
         (reset_model.cfg.stage == usb_ocp_reset_control::STATUS &&
          bm === 8'h00 && request == svt_usb_types::SET_CONFIGURATION &&
          value === OCP_USB_UNCONFIGURED))) ||
       (!port_actor && device == 1 && bm === 8'h21 && value === OCP_CMD_RECOVERY_CTRL));
    if (!selected) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      if (track_submission) submission_inflight--;
      return;
    end
    if (!port_actor && !event_started) begin
      ocp_poll_check_snapshot();
      ocp_poll_check_observation();
      reset_model.ocp_check_entry();
      event_started = 1;
      if (reset_model.cfg.scope == usb_ocp_reset_control::DEV1 &&
          reset_model.cfg.stage != usb_ocp_reset_control::ACTIVATE) begin
        ocp_do_start_port_actor();
        while (!reset_model.window_open) begin
          if ($time >= reset_model.cfg.deadline)
            `uvm_fatal("OCP_RESET_PEER", "Unaffected activation lacks real selective reset window")
          #1us;
        end
      end
    end
    interrupted_started = 1;
    if (reset_model.cfg.stage inside {usb_ocp_reset_control::SETUP,
        usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS} &&
        (port_actor || reset_model.cfg.ocp_check_recovery_affected())) begin
      interrupted_device = device;
      cancelling = 1;
      if (!port_actor && reset_model.cfg.stage inside {
          usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS}) begin
        // OCP 9.2: selecting the uploaded CMS image is a real state change.
        // Completed ACTIVATE variants separately retain the device-cleared
        // activation request; this incomplete request does not activate.
        if (write_data.size() != OCP_SPEC_LEN_RECOVERY_CTRL ||
            write_data[0] !== scoreboard.model.selected_cms ||
            write_data[1] !== OCP_RC_IMAGE_SEL_CMS ||
            write_data[2] !== OCP_RC_ACTIVATE_CODE)
          `uvm_fatal("OCP_RESET_COMMAND_EFFECT", "Interrupted selection lacks the legal original CMS payload")
        write_data[2] = usb_ocp_predictor::OCP_RC_NO_ACTIVATE_CODE;
      end
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data,1);
      cancelling = 0;
    end else begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,read_data);
      if (reset_model.cfg.stage == usb_ocp_reset_control::ACTIVATE) begin
        ocp_poll_check_observation();
        if (!scoreboard.model.activation_request || scoreboard.model.activation_cleared)
          `uvm_fatal("OCP_RESET_STAGE", "Committed activation boundary was not retained")
        if (reset_model.cfg.scope == usb_ocp_reset_control::DEV1) begin
          ocp_do_start_port_actor();
          while (!reset_model.window_open) begin
            if ($time >= reset_model.cfg.deadline)
              `uvm_fatal("OCP_RESET_PEER", "Unaffected image lacks real selective reset window")
            #1us;
          end
        end else ocp_do_check_reset_event();
      end
    end
    if (track_submission) submission_inflight--;
  endtask

  virtual function bit ocp_check_recovery_restart();
    return !fresh && reset_model.cfg.event_complete &&
           reset_model.cfg.ocp_check_recovery_affected();
  endfunction

  virtual task ocp_do_check_image_progress(int offset, int words);
    if (fresh || event_started ||
        reset_model.cfg.stage != usb_ocp_reset_control::PARTIAL) return;
    if (reset_model.cfg.ocp_check_recovery_affected()) begin
      if (offset < 64) return;
      if (offset != 64 || offset >= words)
        `uvm_fatal("OCP_RESET_PUBLICATION", "Reset missed the normal published incomplete-image boundary")
    end
    reset_model.partial_ready = 1;
    ocp_poll_check_snapshot();
    ocp_poll_check_observation();
    reset_model.ocp_check_entry();
    event_started = 1;
    if (reset_model.cfg.scope == usb_ocp_reset_control::DEV1) begin
      ocp_do_start_port_actor();
      while (!reset_model.window_open) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_PEER", "Unaffected image lacks real selective reset window")
        #1us;
      end
    end else ocp_do_check_reset_event();
  endtask

  // OCP 9.2: byte 1 == 1 explicitly resets both FIFO indices. Discovery does
  // not itself authorize deletion of old accepted bytes.
  task ocp_do_check_fresh_fifo_reset();
    bytes_t data;
    int unsigned spaces;
    ocp_do_check_read(OCP_CMD_PROT_CAP,data);
    if (data.size() != OCP_SPEC_LEN_PROT_CAP || data[12] == 0)
      `uvm_fatal("OCP_RESET_DISCOVERY", "Fresh capabilities did not advertise CMS")
    spaces = data[12];
    // Rediscover the retained selected CMS through USB, rather than supplying
    // its previous test-side selection to firmware or silently emptying it.
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_CTRL,data);
    if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_CTRL || data[0] >= spaces ||
        data[1] !== 0)
      `uvm_fatal("OCP_RESET_DISCOVERY", "Fresh selected FIFO CMS/control is unusable")
    cms = data[0];
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
    if (data.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS ||
        data[1] !== OCP_REGION_RECOVERY_CODE_WO ||
        {data[15],data[14],data[13],data[12]} === 0 ||
        {data[19],data[18],data[17],data[16]} === 0)
      `uvm_fatal("OCP_RESET_DISCOVERY", "Fresh selected CMS is not usable recovery FIFO storage")
    data = '{cms,1,0,0,0,0};
    ocp_do_check_write(OCP_CMD_INDIRECT_FIFO_CTRL,data);
    while (!reset_model.cfg.fresh_zero_observed) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_FIFO", "Fresh firmware did not discover reset FIFO zero size")
      #1us;
    end
  endtask

  virtual task ocp_do_sof(bit on);
    if (!on) begin
      while (port_host != null && !port_host.completed) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_ACTORS", "Selective reset actor did not finish")
        #1us;
      end
    end
    super.ocp_do_sof(on);
  endtask

  task ocp_do_check_retire_services();
    time retire_deadline;
    retire_deadline = $time + native_reset_timeout;
    `uvm_info("OCP_RESET_RETIRE", $sformatf(
      "release owned native issuers: scoped=%0d reset=%0b",
      protocol_services.size(),reset_service != null), UVM_LOW)
    foreach (protocol_services[i]) protocol_services[i].release_requested = 1;
    if (reset_service != null) reset_service.release_requested = 1;
    foreach (protocol_services[i]) begin
      while (!protocol_services[i].finished ||
             protocol_services[i].get_sequence_state() != UVM_FINISHED) begin
        if ($time >= retire_deadline || $time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_PROTOCOL", "Scoped native issuer response/finish retirement deadline")
        #1us;
      end
    end
    while (reset_service != null &&
           (!reset_service.finished || reset_service.get_sequence_state() != UVM_FINISHED)) begin
      if ($time >= retire_deadline || $time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE", "Native issuer response/finish retirement deadline")
      #1us;
    end
    service_dispatch_stop = 1;
    while (!service_dispatch_finished) begin
      if ($time >= retire_deadline || $time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_NATIVE", "Native dispatch processes did not retire with their issuers")
      #1us;
    end
    `uvm_info("OCP_RESET_RETIRE", "All owned native issuers and dispatch processes retired", UVM_LOW)
    if (reset_callback != null)
      uvm_callbacks#(svt_usb_link)::delete(host_agent.link,reset_callback);
    if (start_callback != null)
      uvm_callbacks#(svt_usb_protocol)::delete(host_agent.prot,start_callback);
  endtask

  task ocp_do_check_host_traffic();
    bytes_t data;
    bytes_t empty;
    if (port_actor) begin
      if (reset_model.cfg.stage == usb_ocp_reset_control::STATUS) begin
        if (scoreboard.model.enumerated[2] !== 1'b1)
          `uvm_fatal("OCP_RESET_STAGE", "STATUS unconfiguration lacks an observed Configured device")
        ocp_do_check_control(2,8'h00,svt_usb_types::SET_CONFIGURATION,
          OCP_USB_UNCONFIGURED,0,0,empty,data);
      end else if (reset_model.cfg.stage inside {usb_ocp_reset_control::SETUP,
          usb_ocp_reset_control::DATA})
        ocp_do_check_control(2,8'h80,6,16'h0100,0,18,empty,data);
      else ocp_do_check_reset_event();
      completed = 1;
      // Work completion is distinct from UVM issuer retirement. Retain the
      // old selected-child issuer and scoped services through parent traffic.
      while (!native_release_requested) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_NATIVE", "Parent did not reach native issuer release barrier")
        #1us;
      end
      ocp_do_check_retire_services();
      return;
    end
    `uvm_info("OCP_TIMING", $sformatf(
      "Scaled USB timers: reset=%0t debounce=%0t reset/address_recovery=%0t",
      usb_cfg.tdrst * 1ps, usb_cfg.tattdb * 1ps, usb_cfg.trstrcy * 1ps), UVM_LOW)
    wait_for_link_enabled(ocp_cfg.link_timeout);
    ocp_do_sof(1);
    #(usb_cfg.trstrcy * 1ps);
    ocp_do_check_enumeration(0);
    for (int d = 1; d < 3; d++) begin
      ocp_do_check_port(d);
      ocp_do_check_enumeration(d);
    end
    ocp_do_check_recovery();
    if (reset_model.cfg.ocp_check_recovery_affected()) begin
      if (!ocp_check_recovery_restart())
        `uvm_fatal("OCP_RESET_HOST", "Initial attempt escaped mandatory reset/reinitialization")
      fresh = 1;
      // Reconfigure only affected routing slots; unrelated devices keep their
      // actual assigned identities. BUS reenumerates hub before either port.
      if (reset_model.cfg.scope == usb_ocp_reset_control::BUS) begin
        usb_cfg.remote_device_cfg[0].device_address = 0;
        usb_cfg.remote_device_cfg[1].device_address = 126;
        usb_cfg.remote_device_cfg[2].device_address = 127;
        host_agent.reconfigure(usb_cfg);
        ocp_do_check_enumeration(0);
        for (int d = 1; d < 3; d++) begin
          ocp_do_check_port(d);
          ocp_do_check_enumeration(d);
        end
      end else ocp_do_check_enumeration(1);
      // OCP 8.5.5: mandatory access after reset, before any FIFO reset.
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
      if (data.size() != OCP_SPEC_MIN_LEN_DEVICE_STATUS ||
          data[0] !== OCP_DEVICE_STATUS_RECOVERY_MODE)
        `uvm_fatal("OCP_RESET_DISCOVERY", "Fresh USB Recovery Mode response missing")
      ocp_do_check_read(OCP_CMD_PROT_CAP,data);
      ocp_do_check_fresh_fifo_reset();
      ocp_do_check_recovery();
    end
    while (port_host != null && !port_host.completed) begin
      if ($time >= reset_model.cfg.deadline)
        `uvm_fatal("OCP_RESET_ACTORS", "Mandatory reset port actor incomplete")
      #1us;
    end
    // Operational checks are in addition to the during-event passive proof.
    ocp_do_check_standard_controls(1,configuration_value[1],device_descriptor_bytes[1]);
    ocp_do_check_standard_controls(2,configuration_value[2],device_descriptor_bytes[2]);
    ocp_do_sof(0);
    ocp_poll_check_observation();
    if (port_host != null) begin
      port_host.native_release_requested = 1;
      while (port_host.get_sequence_state() != UVM_FINISHED) begin
        if ($time >= reset_model.cfg.deadline)
          `uvm_fatal("OCP_RESET_NATIVE", "Selected-child issuer did not retire after parent observation barrier")
        #1us;
      end
    end
    ocp_do_check_retire_services();
    completed = 1;
    ocp_cfg.actor_finished[0] = 1;
  endtask

  task body();
    if (reset_model == null || scoreboard == null || ocp_cfg == null || observer == null)
      `uvm_fatal("OCP_RESET_HOST", "Missing reset actors/checker context")
    resolve_host_context(1);
    if (reset_model.cfg.stage inside {usb_ocp_reset_control::SETUP,
        usb_ocp_reset_control::DATA,usb_ocp_reset_control::STATUS} &&
        (port_actor || reset_model.cfg.ocp_check_recovery_affected())) begin
      if (host_agent.prot == null)
        `uvm_fatal("OCP_RESET_START", "Original lacks the native host protocol")
      start_callback = usb_ocp_reset_start_callback::type_id::create("start_callback");
      uvm_callbacks#(svt_usb_protocol)::add(host_agent.prot,start_callback);
    end
    // Caller-level cancellation in traffic helpers cannot kill this sibling.
    fork
      ocp_do_check_service_dispatch();
      ocp_do_check_host_traffic();
    join
  endtask
endclass
