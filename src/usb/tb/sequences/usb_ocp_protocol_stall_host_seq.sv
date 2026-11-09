// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_stall_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_protocol_stall_host_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_protocol_stall_model stall_model;
  usb_ocp_reset_start_callback start_callback;
  usb_ocp_dev1_ep0_service_seq peer;
  svt_usb_transfer invalid_request;
  svt_usb_transfer probe_request;
  bit probing;
  bit injecting;
  bit recovery_checked;
  time window_deadline;

  function new(string name = "usb_ocp_protocol_stall_host_seq");
    super.new(name);
  endfunction

  function string ocp_check_probe_progress();
    int p;
    p = stall_model.active_probe;
    if (p < 0) return $sformatf(
      "no active probe; attempted=%0d native_success=%0d native_STALL=%0d",
      stall_model.probe_attempts,stall_model.probe_successes,stall_model.probe_stalls);
    return $sformatf(
      "probe=%0d attempted_SETUP=%0b STALL=%0b native=%0b CLEAR=%0b/%0b firmware=%0d RTC=%0d/%0d",
      p,stall_model.probes[p].setup_seen,stall_model.probes[p].stall_seen,
      stall_model.probes[p].native_checked,stall_model.probes[p].clear_seen,
      stall_model.probes[p].clear_native_checked,stall_model.probes[p].firmware_clears,
      stall_model.probes[p].status_reads,stall_model.probes[p].status_crosschecks);
  endfunction

  function void ocp_check_deadline(string obligation);
    if ($time >= window_deadline)
      `uvm_fatal("OCP_STALL_DEADLOCK", $sformatf(
        "Unreached %s: main SETUP=%0b STALL=%0b native=%0b peer=%0d/%0d CLEAR=%0b/%0b RTC=%0d; %s; mandatory rediscovery/image/FIXED DMA/activation/drain remain required; no reset or synthetic retirement",
        obligation,stall_model.setup_seen,stall_model.stall_seen,
        stall_model.native_checked,stall_model.peer_controls,
        stall_model.peer_crosschecks,stall_model.clear_seen,
        stall_model.clear_native_checked,stall_model.status_reads,
        ocp_check_probe_progress()))
  endfunction

  task ocp_poll_check_observation();
    while (scoreboard.busy || !observer.ocp_check_snapshots_consumed() ||
            scoreboard.model.ready_controls.size() != 0 ||
            scoreboard.deferred_axi.size() != 0) begin
      ocp_check_deadline("ordered observer retirement");
      #1us;
    end
  endtask

  virtual function int ocp_configure_control_priority(int device);
    // Avoid an unconstrained scheduler draw only for this owning row.
    return device == 1 ? 0 : 99;
  endfunction

  virtual task ocp_do_check_control(int device, logic [7:0] bm, logic [7:0] request,
      logic [15:0] value, logic [15:0] index, logic [15:0] length,
      bytes_t write_data, output bytes_t read_data,
      input bit expect_replacement = 0, input bit expect_protocol_stall = 0);
    bit done;
    process request_process;
    process watchdog_process;
    done = 0;
    if ((!stall_model.armed && stall_model.active_probe < 0) || recovery_checked) begin
      super.ocp_do_check_control(device,bm,request,value,index,length,write_data,
        read_data,expect_replacement,expect_protocol_stall);
      return;
    end
    fork
      begin
        fork
          begin
            request_process = process::self();
            super.ocp_do_check_control(device,bm,request,value,index,length,write_data,
              read_data,expect_replacement,expect_protocol_stall);
            done = 1;
          end
          begin
            watchdog_process = process::self();
            #(ocp_cfg.control_transfer_timeout-1us);
            `uvm_fatal("OCP_STALL_DEADLOCK", $sformatf(
              "Owned request deadline slot=%0d bm=%02h request=%02h value=%04h: main SETUP=%0b STALL=%0b native=%0b peer=%0d/%0d CLEAR=%0b/%0b RTC=%0d rediscovery=%0b; %s; outstanding clear/RTC/image/FIXED DMA/activation/drain required",
              device,bm,request,value,stall_model.setup_seen,stall_model.stall_seen,
              stall_model.native_checked,stall_model.peer_controls,
              stall_model.peer_crosschecks,stall_model.clear_seen,
              stall_model.clear_native_checked,stall_model.status_reads,recovery_checked,
              ocp_check_probe_progress()))
          end
        join_any
        // Successful native services may spawn persistent workers. Preserve
        // the completed request tree; cancel only the independent watchdog.
        if (!done && request_process != null &&
            request_process.status() != process::FINISHED) request_process.kill();
        if (watchdog_process != null &&
            watchdog_process.status() != process::FINISHED) watchdog_process.kill();
      end
    join
    if (!done)
      `uvm_fatal("OCP_STALL_DEADLOCK", "Owned request returned without its native completion")
  endtask

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    if (probing && device == 1) begin
      if (probe_request != null || stall_model.active_probe < 0 ||
          tr.setup_data_w_value != OCP_CMD_INDIRECT_CTRL ||
          tr.setup_data_bmrequesttype_dir !== 1)
        `uvm_fatal("OCP_STALL_PROBE_OWNER", "Probe hook must own one registered legal INDIRECT_CTRL read")
      probe_request = tr;
      return;
    end
    if (!injecting || device != 1) return;
    if (invalid_request != null || start_callback == null ||
        tr.setup_data_w_value != OCP_CMD_PROT_CAP ||
        tr.setup_data_bmrequesttype_dir !== 0)
      `uvm_fatal("OCP_STALL_GUARD", "Injection hook must own exactly one write-RO request")
    invalid_request = tr;
    start_callback.original = tr;
  endfunction

  task ocp_do_check_protocol(svt_usb_protocol_service::protocol_command_type_enum operation);
    usb_ocp_reset_protocol_seq service;
    if (invalid_request == null ||
        !(operation inside {svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING,
          svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING}))
      `uvm_fatal("OCP_STALL_GUARD", "Only native scheduling PAUSE/RESUME is allowed; no abort command")
    // Reuse the typed scoped CMD issuer, including actual callback and routed
    // response checks. Its abort option is never selected in this row.
    service = usb_ocp_reset_protocol_seq::type_id::create("stall_schedule_service");
    service.operation = operation;
    service.target_address = invalid_request.device_address;
    service.ocp_cfg = ocp_cfg;
    service.observer = observer;
    fork
      service.start(p_sequencer,this);
      begin
        while (!service.executed) begin
          ocp_check_deadline("native scheduling command");
          #1us;
        end
        service.release_requested = 1;
      end
    join
    if (!service.finished || service.responses == 0)
      `uvm_fatal("OCP_STALL_SCHEDULE", "Native scheduling command did not retire its live issuer")
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    svt_usb_device_status native_device;
    svt_usb_endpoint_status native_endpoint;
    usb_ocp_base_control c;
    if (!injecting || tr != invalid_request || device != 1) return;
    native_device = shared_status.get_device_status(tr.device_address);
    if (native_device == null)
      `uvm_fatal("OCP_STALL_SCHEDULE", "Original lacks native device status")
    native_endpoint = native_device.get_endpoint_status(
      0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
    if (native_endpoint == null ||
        native_endpoint.processing_paused !== svt_usb_endpoint_status::NOT_PAUSED)
      `uvm_fatal("OCP_STALL_SCHEDULE", "Original must start on an unpaused control pipe")
    // Launch PAUSE at native transfer_started, while SETUP is admitted.
    // PAUSE0 waits for that transaction (including retries), not STATUS.
    while (!start_callback.started) begin
      ocp_check_deadline("native original start");
      #1ns;
    end
    ocp_do_check_protocol(svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING);
    while (native_endpoint.processing_paused !== svt_usb_endpoint_status::IS_PAUSED ||
            !stall_model.setup_seen || scoreboard.busy ||
            !observer.ocp_check_snapshots_consumed()) begin
      if (stall_model.stall_seen || tr.status === svt_sequence_item::ABORTED)
        `uvm_fatal("OCP_STALL_WINDOW", "Scheduling PAUSE missed the accepted SETUP boundary; no overlap credit")
      ocp_check_deadline("accepted SETUP and transaction-boundary PAUSE");
      #1us;
    end
    c = scoreboard.model.control[1];
    if (!stall_model.ocp_check_owner(1,c) || c.active !== 1 ||
        c.status_acked !== 0 || c.data.size() != 0 || stall_model.stall_seen)
      `uvm_fatal("OCP_STALL_WINDOW", "PAUSE must hold this accepted SETUP before any DATA/STALL/STATUS completion")
    peer = usb_ocp_dev1_ep0_service_seq::type_id::create("independent_dev1");
    peer.ocp_cfg = ocp_cfg;
    peer.observer = observer;
    peer.expected_configuration = configuration_value[2];
    peer.expected_descriptor = device_descriptor_bytes[2];
    peer.start(p_sequencer,this);
    ocp_poll_check_observation();
    if (!peer.completed || stall_model.peer_controls != 2 ||
        stall_model.peer_crosschecks != 2 || !c.active || stall_model.stall_seen)
      `uvm_fatal("OCP_STALL_WINDOW", "Device1 did not complete two checked native controls during the original live error generation")
    `uvm_info("OCP_STALL_INTERLEAVE", $sformatf(
      "Two independent device1 controls checked before RESUME of dev0 generation=%0d",
      stall_model.generation), UVM_LOW)
    ocp_do_check_protocol(svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING);
    while (native_endpoint.processing_paused !== svt_usb_endpoint_status::NOT_PAUSED) begin
      ocp_check_deadline("native RESUME");
      #1us;
    end
  endtask

  virtual function void ocp_check_stall_result(usb_ocp_event observed);
    stall_model.ocp_check_host_result(observed);
  endfunction

  virtual task ocp_wait_peer_completion(svt_usb_transfer tr, int device);
    if (probing && tr == probe_request) begin
      while (!stall_model.probes[stall_model.active_probe].native_checked) begin
        ocp_check_deadline("mandatory probe actual native/packet reconciliation");
        #1us;
      end
      return;
    end
    if (tr != invalid_request) return;
    // Observe the terminal packet/native ledger before consuming the routed
    // result. This does not modify or manufacture DUT/native completion.
    while (!stall_model.native_checked) begin
      ocp_check_deadline("terminal STALL packet/native reconciliation");
      #1us;
    end
  endtask

  task ocp_do_check_indirect_probe(int index, output bytes_t data);
    bytes_t empty;
    bytes_t response;
    if (max_read == 0 || stall_model.active_probe != -1 || injecting)
      `uvm_fatal("OCP_STALL_PROBE_OWNER", "Mandatory probe requires discovered limits and exclusive owned lifetime")
    ocp_poll_check_observation();
    stall_model.ocp_configure_probe(index,usb_cfg.remote_device_cfg[1].device_address,
      interface_number,max_read,usb_cfg.remote_device_cfg[1].endpoint_cfg[0].max_packet_size,
      scoreboard.model.control[1].epoch,scoreboard.model.control[1].generation+1,
      observer.next_order);
    probe_request = null;
    probing = 1;
    // The existing owned result hook checks success OR precise native STALL.
    // The ordinary successful path still owns STATUS, payload and native checks.
    ocp_do_check_control(1,8'ha1,OCP_BREQUEST_XFER,16'(OCP_CMD_INDIRECT_CTRL),
      {8'b0,interface_number},16'(max_read),empty,data,0,1);
    probing = 0;
    ocp_poll_check_observation();
    if (stall_model.probes[index].stall_seen) begin
      // This recovery was planned with the negative probe, not improvised.
      // OCP 8.5.5 first uses actual CLEAR_FEATURE; OCP 9.1/9.2 then clears
      // unsupported-command error by two checked DEVICE_STATUS reads (1,0).
      ocp_do_check_control(1,8'h02,svt_usb_types::CLEAR_FEATURE,0,0,0,empty,response);
      ocp_poll_check_observation();
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
      ocp_poll_check_observation();
      ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
      ocp_poll_check_observation();
    end
    stall_model.ocp_check_probe_retirement(index);
    probe_request = null;
  endtask

  virtual task ocp_do_check_post_capabilities(bytes_t data);
    bytes_t payload;
    bytes_t response;
    bytes_t empty;
    bytes_t baseline_caps;
    bytes_t baseline_id;
    bytes_t baseline_indirect;
    bytes_t baseline_status;
    bytes_t baseline_recovery_ctrl;
    bytes_t baseline_recovery_status;
    logic [15:0] caps;
    bit check_indirect;
    baseline_caps = data;
    caps = {data[11],data[10]};
    check_indirect = caps[OCP_CAP_INDIRECT_CTRL] || caps[OCP_CAP_PUSH_C_IMAGE];
    window_deadline = $time + ocp_cfg.control_transfer_timeout*8;
    ocp_poll_check_observation();
    ocp_do_check_read(OCP_CMD_DEVICE_ID,baseline_id);
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,baseline_status);
    ocp_do_check_read(OCP_CMD_RECOVERY_CTRL,baseline_recovery_ctrl);
    ocp_do_check_read(OCP_CMD_RECOVERY_STATUS,baseline_recovery_status);
    if (caps[OCP_CAP_PUSH_C_IMAGE] && !caps[OCP_CAP_INDIRECT_CTRL])
      `uvm_error("OCP_STALL_MANDATORY",
        "OCP 1.1 9.2 INDIRECT_CTRL is mandatory for Push C-image but unadvertised; exercising required access despite inconsistent capabilities.")
    if (check_indirect)
      ocp_do_check_indirect_probe(0,baseline_indirect);
    ocp_poll_check_observation();
    payload = '{8'hd1,8'h72,8'hb3,8'h54,8'h95,8'h36,8'hf7,8'h18,
                8'hc9,8'h6a,8'hab,8'h4c,8'h8d,8'h2e,8'hef};
    // USB2 9.2.7 Request Error: incompatible H2D request for an explicitly
    // read-only command. OCP 8.5.5 MAY alone is not a blanket STALL mandate.
    stall_model.ocp_configure_request(usb_cfg.remote_device_cfg[1].device_address,
      interface_number,scoreboard.model.control[1].epoch,
      scoreboard.model.control[1].generation+1,observer.next_order,payload);
    injecting = 1;
    ocp_do_check_control(1,8'h21,OCP_BREQUEST_XFER,16'(OCP_CMD_PROT_CAP),
      {8'b0,interface_number},16'(payload.size()),payload,response,0,1);
    injecting = 0;
    ocp_poll_check_observation();
    // This next SETUP itself ends protocol STALL (USB2 8.5.3.4), and is the
    // least-disruptive OCP 8.5.5 recovery step. Never fall back to reset.
    ocp_do_check_control(1,8'h02,svt_usb_types::CLEAR_FEATURE,0,0,0,empty,response);
    ocp_poll_check_observation();
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
    if (response.size() != baseline_status.size() ||
        response[0] !== baseline_status[0] || response[2] !== baseline_status[2] ||
        response[3] !== baseline_status[3] || response[6] !== baseline_status[6])
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Rejected write changed device state/recovery reason/vendor length")
    ocp_poll_check_observation();
    stall_model.finished = 1;
    ocp_do_check_read(OCP_CMD_RECOVERY_CTRL,response);
    if (response !== baseline_recovery_ctrl)
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Rejected write changed RECOVERY_CTRL")
    ocp_do_check_read(OCP_CMD_RECOVERY_STATUS,response);
    if (response !== baseline_recovery_status)
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Rejected write changed RECOVERY_STATUS")
    ocp_do_check_read(OCP_CMD_PROT_CAP,response);
    if (response !== baseline_caps)
      `uvm_error("OCP_STALL_SIDE_EFFECT", "PROT_CAP bytes changed after rejected write and CLEAR_FEATURE")
    ocp_do_check_read(OCP_CMD_DEVICE_ID,response);
    if (response !== baseline_id)
      `uvm_error("OCP_STALL_SIDE_EFFECT", "DEVICE_ID changed after protocol STALL recovery")
    if (check_indirect) begin
      ocp_do_check_indirect_probe(1,response);
      if (stall_model.probes[0].payload_valid && stall_model.probes[1].payload_valid &&
          response !== baseline_indirect)
        `uvm_error("OCP_STALL_SIDE_EFFECT", "INDIRECT_CTRL changed without accepted programming")
    end
    ocp_do_check_standard_controls(1,configuration_value[1],device_descriptor_bytes[1]);
    ocp_do_check_standard_controls(2,configuration_value[2],device_descriptor_bytes[2]);
    ocp_poll_check_observation();
    if (scoreboard.model.accepted_bytes != 0 || scoreboard.model.returned_bytes != 0 ||
        scoreboard.model.image_words != 0 || scoreboard.model.activation_request)
      `uvm_error("OCP_STALL_SIDE_EFFECT", "Rejected write unexpectedly changed image/FIFO/activation ledger")
    recovery_checked = 1;
    // The inherited recovery body now performs live CMS/FIFO discovery and
    // the complete random image, FIXED DMA, activation and final drain checks.
  endtask

  virtual task ocp_do_check_host_completion();
    if (!recovery_checked || peer == null || !peer.completed)
      `uvm_fatal("OCP_STALL_INCOMPLETE", "Owned error/recovery/peer stimulus is unreached")
    stall_model.ocp_check_complete();
  endtask

  task body();
    if (scoreboard == null || stall_model == null ||
        scoreboard.model.stall_model != stall_model)
      `uvm_fatal("OCP_STALL_GUARD", "Host must share its owned passive model")
    resolve_host_context(1);
    ocp_cfg.control_transfer_timeout = 5ms;
    start_callback = usb_ocp_reset_start_callback::type_id::create("stall_start_callback");
    if (host_agent.prot == null)
      `uvm_fatal("OCP_STALL_SCHEDULE", "Missing native host protocol component")
    uvm_callbacks#(svt_usb_protocol)::add(host_agent.prot,start_callback);
    super.body();
    uvm_callbacks#(svt_usb_protocol)::delete(host_agent.prot,start_callback);
  endtask
endclass
