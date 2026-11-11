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

class usb_ocp_suspend_resume_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_suspend_resume_host_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_suspend_model l2;
  usb_ocp_suspend_service_record live_services[$];
  usb_ocp_suspend_response_catcher response_catcher;
  bit cycle_started;
  bit cycle_finished;
  bit native_watch_finished;
  bit timers_reported;
  time case_timeout = 100ms;
  // Bound native dispatch separately from physical recovery and issuer lifetime.
  time native_command_timeout = 5ms;
  time quiet_interval = 3ms;
  // USB 2.0 7.1.7.7: affected-segment resume recovery. DUT scaling is
  // unverified, so nominal recovery follows real readiness, with SOF running.
  time recovery_guard = 10ms;
  localparam logic [15:0] PORT_SUSPEND = 16'd2;
  localparam logic [15:0] C_PORT_SUSPEND = 16'd18;
  localparam logic [15:0] PORT_CONNECTION_MASK = 16'h0001;
  localparam logic [15:0] PORT_ENABLE_MASK = 16'h0002;
  localparam logic [15:0] PORT_SUSPEND_MASK = 16'h0004;
  localparam logic [15:0] PORT_POWER_MASK = 16'h0100;
  localparam logic [15:0] PORT_HIGH_SPEED_MASK = 16'h0400;
  localparam logic [15:0] PORT_RETAIN_MASK =
    PORT_CONNECTION_MASK | PORT_ENABLE_MASK | PORT_POWER_MASK | PORT_HIGH_SPEED_MASK;

  function new(string name = "usb_ocp_suspend_resume_host_seq");
    super.new(name);
  endfunction

  virtual function void ocp_configure_image_words(ref int words);
    int explicit_words;
    // Keep the explicit ordinary image override, but select a stable fixture
    // when none was supplied. Firmware still learns size solely through AXI.
    if (!$test$plusargs("usb_ocp_image_words=")) words = 130;
    else begin
      if (!$value$plusargs("usb_ocp_image_words=%d",explicit_words))
        `uvm_fatal("OCP_L2_IMAGE", "Malformed explicit image DWORD count")
      words = explicit_words;
    end
    if (words < 2 || words > 1024)
      `uvm_fatal("OCP_L2_IMAGE", "Pending-image L2 requires 2..1024 DWORDs")
  endfunction

  virtual function void ocp_configure_chunk_words(int offset, int words,
      int chunk_limit, ref int chunk_words);
    if (offset != 0) return;
    // Stay below a published 64-DWORD batch and the total image. All ordinary
    // descriptor/FIFO/chunk/wrap constraints remain in force.
    chunk_words = (chunk_limit < 16) ? chunk_limit : 16;
    if (chunk_words >= words) chunk_words = words-1;
    if (chunk_words == 0 || chunk_words > chunk_limit || chunk_words >= words)
      `uvm_fatal("OCP_L2_IMAGE", "No legal partial first chunk")
  endfunction

  task ocp_poll_observation();
    time deadline;
    deadline = $time + case_timeout;
    while (!observer.ocp_check_usb_idle() || scoreboard.busy ||
           scoreboard.deferred_axi.size() != 0 ||
           scoreboard.model.ready_controls.size() != 0) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_OBSERVER", "Completed-request observation barrier timed out")
      #1us;
    end
  endtask

  task ocp_do_check_native_service(usb_ocp_suspend_service_record::operation_e operation);
    usb_ocp_suspend_service_seq service_seq;
    usb_ocp_suspend_clear_seq clear_seq;
    usb_ocp_suspend_service_record record;
    uvm_sequence_state_enum sequence_state;
    time deadline;
    if (observer.service_callback == null || observer.l2_link_callback == null)
      `uvm_fatal("OCP_L2_SERVICE", "Missing existing native callback plumbing")
    if (operation == usb_ocp_suspend_service_record::LINK_CLEAR &&
        (shared_status.link_usb_20_state !== svt_usb_types::SUSPENDED ||
         shared_status.link_usb_20_power_state !== svt_usb_types::POWER_STATE_L2))
      `uvm_fatal("OCP_L2_SERVICE", "Upstream CLEAR requires actual SUSPENDED/L2")
    record = usb_ocp_suspend_service_record::type_id::create("native_record");
    record.operation = operation;
    if (operation == usb_ocp_suspend_service_record::LINK_CLEAR) begin
      clear_seq = usb_ocp_suspend_clear_seq::type_id::create("native_clear");
      clear_seq.record = record;
      clear_seq.native_status = shared_status;
      clear_seq.timeout = ocp_cfg.actor_timeout;
      record.issuer = clear_seq;
      observer.l2_link_callback.active_record = record;
      observer.l2_link_callback.native_status = shared_status;
    end else begin
      service_seq = usb_ocp_suspend_service_seq::type_id::create("native_service");
      service_seq.cfg = usb_cfg;
      service_seq.native_status = shared_status;
      service_seq.record = record;
      service_seq.timeout = ocp_cfg.actor_timeout;
      record.issuer = service_seq;
      observer.service_callback.l2_record = record;
    end
    live_services.push_back(record);
    deadline = $time + native_command_timeout;
    // Automatic fork copies keep each issuing sequence alive independently
    // when this task returns. No response is redirected to the virtual host.
    fork
      begin
        automatic uvm_sequence_base issuing = record.issuer;
        automatic usb_ocp_suspend_service_record::operation_e op = operation;
        `uvm_info("OCP_L2_DISPATCH", $sformatf(
          "op=%s stage=child_start link=%s power=%s time=%0t",op.name(),
          shared_status.link_usb_20_state.name(),shared_status.link_usb_20_power_state.name(),
          $realtime), UVM_LOW)
        if (op == usb_ocp_suspend_service_record::LINK_CLEAR)
          issuing.start(p_sequencer.link_service_sequencer,this);
        else issuing.start(p_sequencer.prot_service_sequencer,this);
      end
    join_none
    while (!record.submitted || !record.ended) begin
      if ($time >= deadline) begin
        sequence_state = record.issuer.get_sequence_state();
        `uvm_fatal("OCP_L2_SERVICE_API", $sformatf(
          "Native service submission/executed-callback deadline op=%s stage=%s submitted=%0b ended=%0b ingress=%0d responses=%0d sequence_state=%s link=%s power=%s bound=%0t",
          operation.name(),record.dispatch_stage,record.submitted,record.ended,
          record.ingress_count,record.responses,sequence_state.name(),
          shared_status.link_usb_20_state.name(),shared_status.link_usb_20_power_state.name(),
          native_command_timeout))
      end
      #1us;
    end
    l2.ocp_record_service(record);
  endtask

  virtual task ocp_do_sof(bit on);
    svt_usb_agent_configuration actual_cfg;
    if (l2 == null || scoreboard == null)
      `uvm_fatal("OCP_L2_HOST", "Missing selected L2 checker")
    l2.native_status = shared_status;
    if (!timers_reported) begin
      response_catcher = usb_ocp_suspend_response_catcher::type_id::create("response_catcher");
      uvm_report_cb::add(p_sequencer.prot_service_sequencer,response_catcher);
      uvm_report_cb::add(p_sequencer.link_service_sequencer,response_catcher);
      if (!$cast(actual_cfg,usb_cfg) || actual_cfg.local_host_cfg == null)
        `uvm_fatal("OCP_L2_TIMING", "Missing actual native host timer configuration")
      `uvm_info("OCP_L2_TIMING", $sformatf(
        "actual tinactivity=%0t tdrsmdn=%0t trsmrcy=%0t microframe=%0t max_empty_sof=%0d; DUT scale unverified; quiet=%0t nominal guard=%0t case=%0t actor=%0t",
        usb_cfg.tinactivity*1ps,usb_cfg.tdrsmdn*1ps,usb_cfg.trsmrcy*1ps,
        actual_cfg.local_host_cfg.micro_frame_period*1ps,actual_cfg.local_host_cfg.max_empty_sof,
        quiet_interval,recovery_guard,case_timeout,ocp_cfg.actor_timeout), UVM_LOW)
      timers_reported = 1;
      l2.native_microframe = actual_cfg.local_host_cfg.micro_frame_period*1ps;
    end
    ocp_do_check_native_service(on ? usb_ocp_suspend_service_record::SOF_ON :
                                    usb_ocp_suspend_service_record::SOF_OFF);
  endtask

  task ocp_poll_link(bit suspended);
    time deadline;
    deadline = $time + case_timeout;
    forever begin
      if (suspended) begin
        if (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED &&
            shared_status.link_usb_20_power_state === svt_usb_types::POWER_STATE_L2) return;
      end else begin
        if (shared_status.link_usb_20_state === svt_usb_types::ENABLED &&
            shared_status.link_usb_20_power_state === svt_usb_types::POWER_STATE_L0 &&
            shared_status.physical_usb_20_working_speed === svt_usb_types::HS) return;
      end
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_NATIVE", $sformatf(
          "Actual link/HS readiness deadline suspended=%0b link=%s power=%s speed=%s",
          suspended,shared_status.link_usb_20_state.name(),
          shared_status.link_usb_20_power_state.name(),
          shared_status.physical_usb_20_working_speed.name()))
      #1us;
    end
  endtask

  task ocp_poll_dsus(bit suspended);
    time deadline;
    deadline = $time + case_timeout;
    while (!l2.ocp_check_dsus(suspended)) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_DSUS", $sformatf(
          "Fresh MCU/SoC DSUS deadline suspended=%0b actual=%p reads=%p",
          suspended,l2.live_command,l2.live_reads))
      #10us;
    end
  endtask

  task ocp_do_check_port_feature(int port, bit suspend_port);
    bytes_t empty;
    bytes_t data;
    // USB 2.0 11.24.2.2/13, Table 11-17: real hub EP0 request, not PAUSE.
    ocp_do_check_control(0,8'h23,
      suspend_port ? svt_usb_types::HUB_CLASS_SET_FEATURE :
                     svt_usb_types::HUB_CLASS_CLEAR_FEATURE,
      PORT_SUSPEND,16'(port),0,empty,data);
  endtask

  task ocp_do_poll_port_status(int port, bit suspended);
    bytes_t empty;
    bytes_t data;
    logic [15:0] status;
    logic [15:0] change;
    time deadline;
    deadline = $time + case_timeout;
    forever begin
      ocp_do_check_control(0,8'ha3,svt_usb_types::HUB_CLASS_GET_STATUS,0,16'(port),4,empty,data);
      if (data.size() != 4)
        `uvm_fatal("OCP_L2_PORT", "GetPortStatus must return four actual little-endian bytes")
      status = {data[1],data[0]};
      change = {data[3],data[2]};
      if ($isunknown({status,change}) ||
          (status & (PORT_CONNECTION_MASK | PORT_ENABLE_MASK | PORT_POWER_MASK)) !==
                    (PORT_CONNECTION_MASK | PORT_ENABLE_MASK | PORT_POWER_MASK))
        `uvm_fatal("OCP_L2_PORT", "Unsafe port disconnect/disable/power loss across suspend")
      if ((status & PORT_RETAIN_MASK) === PORT_RETAIN_MASK &&
          (status & PORT_SUSPEND_MASK) === (suspended ? PORT_SUSPEND_MASK : 16'b0) &&
          (suspended || l2.mode == usb_ocp_suspend_model::GLOBAL ||
           port != ((l2.mode == usb_ocp_suspend_model::DEV0) ? 1 : 2) ||
           (change & PORT_SUSPEND_MASK) === PORT_SUSPEND_MASK)) break;
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_PORT", "Actual port suspend/resume/HS status deadline")
      #100us;
    end
    `uvm_info("OCP_L2_PORT", $sformatf(
      "port=%0d suspended=%0b actual_status=%04h change=%04h time=%0t",
      port,suspended,status,change,$realtime), UVM_LOW)
    if (!suspended && (change & PORT_SUSPEND_MASK) != 0)
      ocp_do_check_control(0,8'h23,svt_usb_types::HUB_CLASS_CLEAR_FEATURE,
        C_PORT_SUSPEND,16'(port),0,empty,data);
  endtask

  task ocp_do_check_device_identity(int device);
    bytes_t empty;
    bytes_t data;
    // Retention/data violations do not suppress subsequent safe traffic.
    ocp_do_check_control(device,8'h80,svt_usb_types::GET_CONFIGURATION,0,0,1,empty,data);
    if (data.size() != 1 || data[0] !== configuration_value[device])
      `uvm_error("OCP_L2_RETENTION", "Device configuration differs from runtime USB discovery")
    ocp_do_check_control(device,8'h80,svt_usb_types::GET_DESCRIPTOR,16'h0100,0,18,empty,data);
    if (data !== device_descriptor_bytes[device])
      `uvm_error("OCP_L2_RETENTION", "Device descriptor identity/data changed across L2")
  endtask

  task ocp_do_check_retained_recovery();
    bytes_t data;
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_CTRL,data);
    ocp_do_check_read(OCP_CMD_INDIRECT_FIFO_STATUS,data);
    ocp_do_check_read(OCP_CMD_RECOVERY_CTRL,data);
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,data);
    ocp_do_check_read(OCP_CMD_RECOVERY_STATUS,data);
    ocp_poll_observation();
  endtask

  task ocp_check_quiet_watch();
    l2.ocp_check_quiet_entry(observer.next_order);
    fork
      begin
        while (l2.quiet_active) begin
          l2.ocp_check_native();
          #10us;
        end
        native_watch_finished = 1;
      end
    join_none
  endtask

  task ocp_poll_quiet_progress();
    time deadline;
    int unsigned required_bytes;
    deadline = $time + case_timeout;
    required_bytes = (l2.saved_words < 64) ? l2.saved_words*4 : 256;
    while ($realtime < l2.quiet_at + quiet_interval ||
           (l2.mode == usb_ocp_suspend_model::DEV1 && l2.window_returned < required_bytes)) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_PROGRESS", "Stable quiet interval/real published DMA progress deadline")
      #10us;
    end
    ocp_poll_observation();
  endtask

  task ocp_do_check_resume();
    longint unsigned sof_floor;
    int unsigned guard_read_floor[2];
    bit guard_active;
    bit guard_finished;
    time deadline;
    l2.ocp_check_close_quiet();
    wait (native_watch_finished);
    if (l2.mode == usb_ocp_suspend_model::GLOBAL) begin
      ocp_do_check_native_service(usb_ocp_suspend_service_record::LINK_CLEAR);
      // Service end is NOT EOR or HS restoration. SOF restart follows real
      // ENABLED/L0/HS promptly, before downstream polls and the nominal guard.
      ocp_poll_link(0);
      sof_floor = observer.sof_serial;
      ocp_do_sof(1);
    end else begin
      sof_floor = observer.sof_serial;
      ocp_do_check_port_feature((l2.mode == usb_ocp_suspend_model::DEV0) ? 1 : 2,0);
    end
    ocp_poll_dsus(0);
    l2.ocp_check_resume();
    // The selectively resumed hub remains on an unaffected upstream segment.
    // In GLOBAL mode no hub CONTROL is legal before TRSMRCY expires.
    if (l2.mode != usb_ocp_suspend_model::GLOBAL)
      for (int port = 1; port <= 2; port++) ocp_do_poll_port_status(port,0);
    deadline = $time + case_timeout;
    while (observer.sof_serial <= sof_floor) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_NATIVE", "No actual SOF after resume/SOF_ON")
      #10us;
    end
    sof_floor = observer.sof_serial;
    guard_read_floor = l2.live_reads;
    ocp_poll_observation();
    l2.recovery_guard_at = $realtime;
    `uvm_info("OCP_L2_GUARD", $sformatf(
      "mode=%s ready=%0t start=%0t minimum=%0t",
      l2.mode.name(),l2.resumed_at,l2.recovery_guard_at,recovery_guard), UVM_LOW)
    guard_active = 1;
    guard_finished = 0;
    fork
      begin
        while (guard_active) begin
          l2.ocp_check_recovery_guard();
          #10us;
        end
        guard_finished = 1;
      end
    join_none
    #(recovery_guard);
    guard_active = 0;
    wait (guard_finished);
    l2.recovery_guard_end_at = $realtime;
    `uvm_info("OCP_L2_GUARD", $sformatf(
      "mode=%s end=%0t elapsed=%0t",
      l2.mode.name(),l2.recovery_guard_end_at,
      l2.recovery_guard_end_at-l2.recovery_guard_at), UVM_LOW)
    deadline = $time + case_timeout;
    while (l2.live_reads[0] <= guard_read_floor[0] ||
           l2.live_reads[1] <= guard_read_floor[1]) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_L2_DSUS", "Recovery guard lacks fresh owned status observations")
      #10us;
    end
    ocp_poll_dsus(0);
    ocp_poll_link(0);
    l2.ocp_check_resume();
    if (observer.sof_serial <= sof_floor)
      `uvm_fatal("OCP_L2_NATIVE", "SOFs did not continue through nominal resume recovery")
    if (l2.mode == usb_ocp_suspend_model::GLOBAL)
      for (int port = 1; port <= 2; port++) ocp_do_poll_port_status(port,0);
    for (int device = 0; device < 3; device++) ocp_do_check_device_identity(device);
    ocp_do_check_retained_recovery();
    cycle_finished = 1;
  endtask

  virtual task ocp_do_check_image_progress(int offset, int words);
    if (!cycle_started) begin
      if (offset <= 0 || offset >= words)
        `uvm_fatal("OCP_L2_ENTRY", "First completed chunk must leave a partial image")
      ocp_do_check_retained_recovery();
      l2.ocp_check_entry(observer.next_order);
      cycle_started = 1;
      if (l2.mode == usb_ocp_suspend_model::GLOBAL) begin
        ocp_do_sof(0);
        ocp_poll_link(1);
      end else begin
        ocp_poll_link(0);
        ocp_do_check_port_feature((l2.mode == usb_ocp_suspend_model::DEV0) ? 1 : 2,1);
      end
      ocp_poll_dsus(1);
      if (l2.mode != usb_ocp_suspend_model::GLOBAL)
        ocp_do_poll_port_status((l2.mode == usb_ocp_suspend_model::DEV0) ? 1 : 2,1);
      ocp_poll_observation();
      ocp_check_quiet_watch();
      if (l2.mode == usb_ocp_suspend_model::DEV0) ocp_do_check_device_identity(2);
      if (l2.mode != usb_ocp_suspend_model::DEV1) begin
        ocp_poll_quiet_progress();
        ocp_do_check_resume();
      end
      return;
    end
    if (!cycle_finished && l2.mode == usb_ocp_suspend_model::DEV1 &&
        offset >= ((words < 64) ? words : 64)) begin
      // Genuine subsequent FIFO controls publish the normal first batch (or
      // final short image). Caliptra, not this host, performs all FIXED reads.
      ocp_poll_quiet_progress();
      ocp_do_check_resume();
    end
  endtask

  virtual task ocp_do_check_host_completion();
    time deadline;
    if (!cycle_finished)
      `uvm_fatal("OCP_L2_INCOMPLETE", "Selected pending-image L2 cycle did not finish")
    // This is a bounded response observation tail, not a claimed vendor
    // guarantee. All initial, OFF, CLEAR, ON and teardown issuers remain live
    // through it, with every response checked and native warnings untouched.
    #2ms;
    foreach (live_services[i]) live_services[i].release_requested = 1;
    deadline = $time + case_timeout;
    foreach (live_services[i]) begin
      while (!live_services[i].finished ||
             live_services[i].issuer.get_sequence_state() != UVM_FINISHED) begin
        if ($time >= deadline)
          `uvm_fatal("OCP_L2_SERVICE_API", "Live native service retirement deadline")
        #1us;
      end
    end
    observer.service_callback.l2_record = null;
    observer.l2_link_callback.active_record = null;
    ocp_poll_observation();
    foreach (l2.exit_generation[d])
      l2.exit_generation[d] = scoreboard.model.control[d].generation;
    l2.finished = 1;
  endtask
endclass
