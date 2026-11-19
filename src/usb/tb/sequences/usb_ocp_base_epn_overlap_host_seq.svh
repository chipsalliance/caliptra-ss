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

class usb_ocp_base_epn_overlap_host_seq extends usb_ocp_base_replacement_host_seq;
  `uvm_object_utils(usb_ocp_base_epn_overlap_host_seq)
  usb_ocp_base_epn_descriptor discoveries[2];
  // EPN slot is independent of the original OCP control slot (always 1).
  int unsigned epn_device = 1;
  bit both_epn_devices;
  bit read_started;
  bit write_started;
  longint unsigned capture_floor;

  function new(string name = "usb_ocp_base_epn_overlap_host_seq");
    super.new(name);
    foreach (discoveries[i])
      discoveries[i] = usb_ocp_base_epn_descriptor::type_id::create("host_discovery");
  endfunction

  function bit ocp_check_selected_device(int device);
    return both_epn_devices ? (device inside {1,2}) : device == epn_device;
  endfunction

  virtual function void ocp_check_configuration_discovery(int device, bytes_t data);
    if (ocp_check_selected_device(device)) discoveries[device-1].ocp_check_parse(data);
  endfunction

  virtual task ocp_do_check_post_enumeration(int device);
    bytes_t empty;
    bytes_t data;
    usb_ocp_base_endpoint_cfg native_ep;
    usb_endpoint_cfg ep;
    usb_ocp_base_epn_descriptor discovery;
    if (!ocp_check_selected_device(device)) return;
    discovery = discoveries[device-1];
    if (configuration_value[device] !== discovery.configuration)
      `uvm_fatal("OCP_EPN_DISCOVERY", "GET_CONFIGURATION differs from actual descriptor")
    // USB 2.0 9.4.4/9.4.10. The host learns both interface and alternate
    // from actual descriptors; ISO bandwidth is never enabled by a shadow.
    ocp_do_check_control(device,8'h81,svt_usb_types::GET_INTERFACE,0,{8'b0,discovery.interface_number},
                         1,empty,data);
    if (data.size() != 1 || data[0] !== 0)
      `uvm_fatal("OCP_EPN_INTERFACE", "Default GET_INTERFACE is not alternate zero")
    if (discovery.alternate != 0)
      ocp_do_check_control(device,8'h01,svt_usb_types::SET_INTERFACE,{8'b0,discovery.alternate},
                           {8'b0,discovery.interface_number},0,empty,data);
    ocp_do_check_control(device,8'h81,svt_usb_types::GET_INTERFACE,0,{8'b0,discovery.interface_number},
                         1,empty,data);
    if (data.size() != 1 || data[0] !== discovery.alternate)
      `uvm_fatal("OCP_EPN_INTERFACE", "GET_INTERFACE does not confirm advertised alternate")
    // Work is quiescent here. Preserve EP0 and add only the selected pair,
    // with anchor positions from the actual native queue.
    for (int dir = 0; dir < 2; dir++) begin
      ep = discovery.endpoints[dir];
      native_ep = usb_ocp_base_endpoint_cfg::type_id::create("discovered_native_ep");
      native_ep.ep_number = ep.ep_number;
      native_ep.direction = dir ? svt_usb_types::IN : svt_usb_types::OUT;
      native_ep.speed = svt_usb_types::HS;
      native_ep.max_packet_size = ep.max_packet_size;
      native_ep.interval = ep.interval;
      native_ep.isoc_mult = svt_usb_endpoint_configuration::ISOC_MULT_ZERO;
      native_ep.usb_20_isoc_without_first_last_transaction = 0;
      case (ep.transfer_type)
        USB_TRANSFER_TYPE_BULK: native_ep.ep_type = svt_usb_types::BULK;
        USB_TRANSFER_TYPE_INTERRUPT: native_ep.ep_type = svt_usb_types::INTERRUPT;
        USB_TRANSFER_TYPE_ISOCHRONOUS: native_ep.ep_type = svt_usb_types::ISOCHRONOUS;
        default: `uvm_fatal("OCP_EPN_DISCOVERY", "Unsupported native endpoint type")
      endcase
      if (ep.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS) begin
        native_ep.max_retry_due_to_nak = 100000;
        native_ep.max_retry_due_to_nak_before_moving_to_next_ep = 1;
      end
      ep.anchor_index = usb_cfg.remote_device_cfg[device].endpoint_cfg.size();
      ep.anchor_index_valid = 1;
      usb_cfg.remote_device_cfg[device].add_endpoint_configuration(native_ep);
    end
    usb_cfg.remote_device_cfg[device].num_endpoints =
      usb_cfg.remote_device_cfg[device].endpoint_cfg.size();
    host_agent.reconfigure(usb_cfg);
  endtask

  virtual function void ocp_configure_control_request(svt_usb_transfer tr, int device);
    if (device == 1) tr.schedule_priority = 0;
    capture_floor = observer.next_order;
  endfunction

  task ocp_do_check_native_processing(svt_usb_transfer tr, bit pause_processing);
    svt_usb_protocol_service service;
    svt_usb_device_status device_status;
    svt_usb_endpoint_status endpoint_status;
    usb_ocp_base_service_callback actual;
    longint unsigned command_floor;
    int paused_before;
    int expected_command;
    actual = observer.service_callback;
    if (actual == null) `uvm_fatal("OCP_EPN_COMMAND", "Missing native completion callback")
    device_status = shared_status.get_device_status(tr.device_address);
    if (device_status == null) `uvm_fatal("OCP_EPN_PAUSE", "No native device shared status")
    endpoint_status = device_status.get_endpoint_status(0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
    if (endpoint_status == null) `uvm_fatal("OCP_EPN_PAUSE", "No native EP0 shared status")
    paused_before = endpoint_status.processing_paused;
    if (paused_before !== (pause_processing ? svt_usb_endpoint_status::NOT_PAUSED :
                                           svt_usb_endpoint_status::IS_PAUSED))
      `uvm_fatal("OCP_EPN_PAUSE", "Native command lost its required initial processing state")
    command_floor = actual.completed_commands;
    expected_command = pause_processing ?
      svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING :
      svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING;
    service = svt_usb_protocol_service::type_id::create("ep0_processing_command");
    start_item(service,-1,p_sequencer.prot_service_sequencer);
    service.cfg = usb_cfg;
    if (!service.randomize() with {
          service_type == svt_usb_protocol_service::CMD;
          protocol_command_type == (local::pause_processing ?
            svt_usb_protocol_service::USB_PAUSE_TRANSFER_PROCESSING :
            svt_usb_protocol_service::USB_RESUME_TRANSFER_PROCESSING);
          device_address == local::tr.device_address;
          endpoint_number == 0;
          direction == svt_usb_types::OUT;
          pause_at_transfer_boundary == 0;
        }) `uvm_fatal("OCP_EPN_PAUSE", "Native processing command randomization failed")
    finish_item(service);
    service.end_event.wait_on();
    // Submitted completion does not establish executed result copy-back.
    wait (actual.completed_commands > command_floor);
    if (actual.completed_commands != command_floor+1 ||
        actual.command !== expected_command || actual.address !== tr.device_address ||
        actual.endpoint !== 0 || actual.pause_at_transfer_boundary !== 0)
      `uvm_fatal("OCP_EPN_COMMAND", "Native completion does not match the sole submitted command")
    `uvm_info("OCP_EPN_COMMAND",$sformatf(
      "pause=%0b state_before=%0d state_after=%s submitted_return=%0d actual_return=%0d",
      pause_processing,paused_before,endpoint_status.processing_paused.name(),
      service.return_status,actual.return_status),UVM_LOW)
    if (!actual.accepted || !(actual.return_status inside {0,1}))
      `uvm_fatal("OCP_EPN_PAUSE",$sformatf(
        "Completed native command rejected pause=%0b return_status=%0d state_before=%0d state_after=%s",
        pause_processing,actual.return_status,paused_before,endpoint_status.processing_paused.name()))
    // CMD acceptance may precede the transaction boundary. Only the caller's
    // IS_PAUSED plus ACK-qualified active SETUP can authorize EPN traffic.
    if (pause_processing) begin
      if (!(endpoint_status.processing_paused inside {
          svt_usb_endpoint_status::PENDING_PAUSED_AT_TRANSACTION,
          svt_usb_endpoint_status::IS_PAUSED}))
        `uvm_fatal("OCP_EPN_PAUSE", "Accepted mode0 request did not establish transaction-boundary pause")
    end else begin
      if ((epn_device == 2 || both_epn_devices) && actual.return_status !== 1)
        `uvm_fatal("OCP_EPN_PAUSE", "Peer overlap RESUME did not change original EP0 processing state")
      wait (endpoint_status.processing_paused === svt_usb_endpoint_status::NOT_PAUSED);
    end
  endtask

  virtual task ocp_do_check_paused_continuation(svt_usb_transfer tr,
      int phase, int generation, output bit resumed_original);
    ocp_do_check_native_processing(tr,0);
    resumed_original = 1;
  endtask

  virtual task ocp_do_control_interleave(svt_usb_transfer tr, int device);
    bit done;
    done = 0;
    // This watchdog expires before the enclosing 5 ms control budget.
    // API/admission/capture uncertainty is a stimulus failure, not a DUT hang.
    fork
      begin
        fork
          begin ocp_do_check_overlap_window(tr,device); done = 1; end
          begin #4ms; end
        join_any
        disable fork;
      end
    join
    if (!done)
      `uvm_fatal("OCP_EPN_STIMULUS_TIMEOUT",$sformatf(
        "Bounded pause/EPN/SRAM/resume candidate failed cmd=%02h; no overlap or DUT-hang claim",
        tr.setup_data_w_value))
  endtask

  task ocp_do_check_overlap_window(svt_usb_transfer tr, int device);
    usb_ocp_base_epn_host_seq peers[2][2];
    usb_ocp_base_epn_model epn_model;
    usb_ocp_base_epn_profile profile;
    svt_usb_device_status device_status;
    svt_usb_endpoint_status endpoint_status;
    usb_ocp_base_control c;
    int phase;
    int generation;
    int period;
    int microframe;
    logic [7:0] expected_setup[8];
    longint unsigned setup_order;
    bit resumed_original;
    phase = -1;
    if (device == 1 && tr.setup_data_w_value == OCP_CMD_PROT_CAP && !read_started)
      phase = 0;
    if (device == 1 && tr.setup_data_w_value == OCP_CMD_INDIRECT_FIFO_DATA && !write_started)
      phase = 1;
    if (phase < 0) return;
    if (phase == 0) read_started = 1;
    else write_started = 1;
    generation = scoreboard.model.control[1].generation + 1;
    expected_setup = '{phase ? 8'h21 : 8'ha1,tr.setup_data_brequest,
      tr.setup_data_w_value[7:0],tr.setup_data_w_value[15:8],
      tr.setup_data_w_index[7:0],tr.setup_data_w_index[15:8],
      tr.setup_data_w_length[7:0],tr.setup_data_w_length[15:8]};
    // Request mode0 while the observed SETUP transaction is underway, not
    // after SETUP_STAGE end. This address/EP0 has only this submitted control;
    // the subsequent ACK-qualified SETUP must still match all eight bytes.
    while (!(scoreboard.model.token != null &&
          scoreboard.model.token.pid === svt_usb_packet::SETUP &&
          scoreboard.model.token.address === tr.device_address &&
          scoreboard.model.token.endpoint === 0 &&
          scoreboard.model.token.order >= capture_floor)) begin
      if (scoreboard.model.control[1].generation >= generation &&
          (!scoreboard.model.control[1].active || scoreboard.model.control[1].status_acked))
        `uvm_fatal("OCP_EPN_CAPTURE_LATE", "Matching SETUP already ended before pause submission")
      #5ns;
    end
    setup_order = scoreboard.model.token.order;
    `uvm_info("OCP_EPN_PAUSE",$sformatf(
      "Requesting mode0 during SETUP phase=%0d cmd=%02h token_order=%0d generation=%0d",
      phase,tr.setup_data_w_value,setup_order,generation),UVM_LOW)
    ocp_do_check_native_processing(tr,1);
    device_status = shared_status.get_device_status(tr.device_address);
    if (device_status == null) `uvm_fatal("OCP_EPN_PAUSE", "No native device shared status")
    endpoint_status = device_status.get_endpoint_status(0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
    if (endpoint_status == null) `uvm_fatal("OCP_EPN_PAUSE", "No native EP0 shared status")
    forever begin
      c = scoreboard.model.control[1];
      if (c.generation >= generation && (!c.active || c.status_acked))
        `uvm_fatal("OCP_EPN_CAPTURE_LATE", "STATUS won the pause race; no overlap credit is allowed")
      if (endpoint_status.processing_paused === svt_usb_endpoint_status::IS_PAUSED &&
          c.generation == generation && c.active && !c.status_acked) break;
      #10ns;
    end
    if (c.setup !== expected_setup || c.address !== tr.device_address)
      `uvm_fatal("OCP_EPN_CAPTURE_LATE", "Paused ACK-qualified control does not match submitted SETUP")
    `uvm_info("OCP_EPN_PAUSED",$sformatf(
      "IS_PAUSED with matching accepted SETUP phase=%0d generation=%0d setup_order=%0d",
      phase,generation,setup_order),UVM_LOW)
    period = 1;
    for (int port = 0; port < 2; port++) begin
      if (!ocp_check_selected_device(port+1)) continue;
      wait (ocp_cfg.epn_ready[port][phase][0] && ocp_cfg.epn_ready[port][phase][1]);
      for (int dir = 0; dir < 2; dir++)
        if (discoveries[port].endpoints[dir].transfer_type != USB_TRANSFER_TYPE_BULK &&
            period < (1 << (discoveries[port].endpoints[dir].interval-1)))
          period = 1 << (discoveries[port].endpoints[dir].interval-1);
    end
    microframe = shared_status.local_host_status.micro_frame_count + 2;
    microframe = (((microframe+period-1)/period)*period) & 'h3fff;
    for (int port = 0; port < 2; port++) begin
      if (!ocp_check_selected_device(port+1)) continue;
      profile = ocp_cfg.ocp_get_epn_profile(port+1);
      if (profile == null)
        `uvm_fatal("OCP_EPN_HOST", "Missing owned test-data profile")
      for (int dir = 0; dir < 2; dir++) begin
        peers[port][dir] = usb_ocp_base_epn_host_seq::type_id::create(
          both_epn_devices ? $sformatf("epn_peer%0d_%0d",port,dir) :
                             $sformatf("epn_peer%0d",dir));
        peers[port][dir].endpoint = discoveries[port].endpoints[dir];
        peers[port][dir].device = port+1;
        peers[port][dir].address = (port == 0) ? tr.device_address :
          usb_cfg.remote_device_cfg[port+1].device_address;
        peers[port][dir].observer = observer;
        peers[port][dir].ocp_cfg = ocp_cfg;
        peers[port][dir].phase = phase;
        peers[port][dir].data_tag = profile.data_tag;
        peers[port][dir].scheduled_microframe = microframe;
      end
    end
    fork
      begin if (ocp_check_selected_device(1)) peers[0][0].start(p_sequencer); end
      begin if (ocp_check_selected_device(1)) peers[0][1].start(p_sequencer); end
      begin if (ocp_check_selected_device(2)) peers[1][0].start(p_sequencer); end
      begin if (ocp_check_selected_device(2)) peers[1][1].start(p_sequencer); end
    join
    for (int port = 0; port < 2; port++) begin
      if (!ocp_check_selected_device(port+1)) continue;
      epn_model = scoreboard.model.ocp_get_epn(port+1);
      if (epn_model == null)
        `uvm_fatal("OCP_EPN_HOST", "Missing selected passive endpoint ledger")
      wait (epn_model.crosschecked[0] > phase && epn_model.crosschecked[1] > phase &&
            epn_model.memory_checked[0] > phase && epn_model.memory_checked[1] > phase);
      if (!peers[port][0].completed || !peers[port][1].completed)
        `uvm_fatal("OCP_EPN_CAPTURE_LATE", "Native endpoint pair returned incomplete")
    end
    if (!c.active || c.status_acked || c.generation != generation ||
        endpoint_status.processing_paused !== svt_usb_endpoint_status::IS_PAUSED)
      `uvm_fatal("OCP_EPN_CAPTURE_LATE", "Lost matching paused control before accepted EPN/SRAM proof")
    ocp_do_check_paused_continuation(tr,phase,generation,resumed_original);
    if (resumed_original)
      `uvm_info("OCP_EPN_RESUMED",$sformatf(
        "Resumed exact original OCP phase=%0d generation=%0d; STATUS and recovery remain required",
        phase,generation),UVM_LOW)
  endtask

  task body();
    resolve_host_context(1);
    if (ocp_cfg == null || observer == null || scoreboard == null ||
        shared_status.local_host_status == null)
      `uvm_fatal("OCP_EPN_HOST", "Missing native overlap context")
    if (!(epn_device inside {1,2}))
      `uvm_fatal("OCP_EPN_HOST", "EPN slot differs from the selected passive ledger")
    for (int port = 0; port < 2; port++) begin
      if (!ocp_check_selected_device(port+1)) continue;
      if (scoreboard.model.ocp_get_epn(port+1) == null ||
          scoreboard.model.ocp_get_epn(port+1).device != port+1)
        `uvm_fatal("OCP_EPN_HOST", "EPN slot differs from the selected passive ledger")
    end
    ocp_cfg.control_transfer_timeout = 5ms;
    usb_cfg.remote_device_cfg[1].endpoint_cfg[0].
      max_retry_due_to_nak_before_moving_to_next_ep = 1;
    host_agent.reconfigure(usb_cfg);
    super.body();
    if (!read_started || !write_started)
      `uvm_fatal("OCP_EPN_HOST", "Both OCP overlap phases were not submitted")
  endtask
endclass
