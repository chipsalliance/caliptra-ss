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

class usb_l2_remote_wake_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_l2_remote_wake_host_seq)

  // Candidate stimulus budget, not an external-DUT timing oracle.
  localparam time ACCELERATED_HOST_RESUME_BUDGET = 4ms;
  // Clock-quiescence observation window, not a hardware suspend timer.
  localparam time CLOCK_QUIET_OBSERVATION = 1us;
  virtual usb_tb_ctrl_if #(
    .UW(usb_tb_pkg::USB_TB_AXI_USER_WIDTH),
    .COMBO_NUM_USERS(usb_tb_pkg::USB_COMBO_NUM_PRIV_AXI_USERS),
    .DEV1_NUM_USERS(usb_tb_pkg::USB_DEV1_NUM_PRIV_AXI_USERS)
  ) ctrl_vif;
  uvm_event host_suspended;
  uvm_event wake_requested;
  uvm_event host_resumed;
  uvm_event recovery_complete;
  bit [6:0] device_address;
  time link_state_timeout = 35ms;
  // Coarse scheduler-progress bound, not a replacement for native SOF timing checks.
  time sof_progress_timeout = 1ms;
  time scaled_remote_wake_idle;
  time scaled_recovery;
  int unsigned post_resume_sof_count;
  bit digital_mac_request_checked;

  function new(string name = "usb_l2_remote_wake_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_L2_REMOTE_HOST";
  endfunction

  function void report_protocol_status(string stage);
    svt_usb_device_status device_status;
    svt_usb_endpoint_status endpoint_status;

    if (shared_status.local_host_status == null) begin
      `uvm_fatal(report_id(), "Native local host status is unavailable")
    end
    `uvm_info(report_id(), $sformatf("%s: link=%s SOF enabled=%0b microframe=%0d max_empty_sof=%0d", stage,
      shared_status.link_usb_20_state.name(), shared_status.local_host_status.sof_generation_enabled,
      shared_status.local_host_status.micro_frame_count, usb_cfg.local_host_cfg.max_empty_sof), UVM_LOW)
    device_status = shared_status.get_remote_device_status(device_address, 0);
    if (device_status != null) endpoint_status = device_status.get_endpoint_status(1, svt_usb_types::OUT);
    if (endpoint_status == null) begin
      `uvm_info(report_id(), $sformatf("%s: native status for address %0d EP1 OUT is not allocated", stage, device_address), UVM_LOW)
    end else begin
      `uvm_info(report_id(), $sformatf("%s: native EP1 OUT processing=%s", stage, endpoint_status.processing_paused.name()), UVM_LOW)
    end
  endfunction

  // Check only the public digital MAC request; native checks own physical resume/EOR.
  function void check_digital_mac_request(string stage);
    if (ctrl_vif.dut_txvalid !== 1'b0 || $isunknown(ctrl_vif.dut_opmode)) begin
      `uvm_fatal(report_id(), $sformatf("Accelerated profile incompatible at %s: MAC TXValid=%b OpMode=%b; wake drive must not be requested",
        stage, ctrl_vif.dut_txvalid, ctrl_vif.dut_opmode))
    end
    digital_mac_request_checked = 1'b1;
    `uvm_info(report_id(), $sformatf("Digital MAC request guard passed at %s: TXValid=%b OpMode=%b; not physical release proof",
      stage, ctrl_vif.dut_txvalid, ctrl_vif.dut_opmode), UVM_LOW)
  endfunction

  virtual task body();
    svt_usb_protocol_service_20_sof_off_sequence sof_off;
    svt_usb_protocol_service_20_sof_on_sequence sof_on;
    svt_usb_status phy_status;
    process observer;
    process wake_observer;
    process sof_observer;
    process sof_watchdog;
    process eor_observer;
    process watchdog;
    bit device_origin;
    bit resume_complete;
    time suspend_observed_at;
    time state_deadline;

    completed = 1'b0;
    device_origin = 1'b0;
    resume_complete = 1'b0;
    digital_mac_request_checked = 1'b0;
    post_resume_sof_count = 0;
    if (host_suspended == null || wake_requested == null || host_resumed == null || recovery_complete == null) begin
      `uvm_fatal(report_id(), "Suspend, wake, resume and recovery coordination events are required")
    end
    if (sof_progress_timeout == 0 || ctrl_vif == null) begin
      `uvm_fatal(report_id(), "SOF progress timeout must be nonzero and passive UTMI observation is required")
    end
    resolve_host_context(1'b1);
    `uvm_info(report_id(),
      $sformatf("Accelerated native profile: idle=%0.0f ps recovery=%0.0f ps host_budget=%0.0f ps recovery_SOF=%0b progress_bound=%0t",
        usb_cfg.twtrsm, usb_cfg.trsmrcy, usb_cfg.tdrsmdn, usb_cfg.enable_sof_during_recovery, sof_progress_timeout), UVM_LOW)
    if ((usb_cfg.enable_sof_during_recovery !== 1'b1) || ((usb_cfg.trsmrcy == (800ns / 1ps)) !== 1'b1) ||
        ((usb_cfg.twtrsm == (100us / 1ps)) !== 1'b1) ||
        ((usb_cfg.tdrsmdn == (ACCELERATED_HOST_RESUME_BUDGET / 1ps)) !== 1'b1) ||
        ((usb_cfg.tdrsmup_min == (1ms / 1ps)) !== 1'b1) || ((usb_cfg.tdrsmup_max == (15ms / 1ps)) !== 1'b1)) begin
      `uvm_fatal(report_id(), "Accelerated profile requires native 100 us idle/800 ns recovery, 4 ms host budget and real 1..15 ms upstream bounds")
    end
    scaled_remote_wake_idle = time'(usb_cfg.twtrsm * 1ps);
    scaled_recovery = time'(usb_cfg.trsmrcy * 1ps);
    report_protocol_status("Before suspend");
    phy_status = p_sequencer.get_remote_shared_status(this);
    if (phy_status == null || phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE == null) begin
      `uvm_fatal(report_id(), "Native DUT-PHY wake observation is unavailable")
    end
    // The Device-A host FSM reports suspend and EOR completion, but not every
    // intermediate host enum. Use the native DUT-PHY K notification for origin.
    fork
      begin
        wake_observer = process::self();
        host_suspended.wait_on();
        while (!device_origin) begin
          phy_status.NOTIFY_PHYSICAL_USB_20_LINESTATE_CHANGE.wait_trigger();
          if (phy_status.physical_usb_20_linestate === svt_usb_types::LINESTATE_K) begin
            if (!wake_requested.is_on()) begin
              `uvm_fatal(report_id(), "Device resume appeared before the software wake request")
            end
            device_origin = 1'b1;
            `uvm_info(report_id(), "Native DUT-PHY observed remote-wake K; awaiting native host takeover/EOR", UVM_LOW)
          end
        end
      end
      begin
        observer = process::self();
        forever begin
          @(shared_status.link_20_host_bus_state_event);
          `uvm_info(report_id(), $sformatf("Native host transition: %s", shared_status.link_20_host_bus_state.name()), UVM_LOW)
          case (shared_status.link_20_host_bus_state)
            svt_usb_status::SUSPENDED_TO_RESUME_VIA_HOST:
              `uvm_fatal(report_id(), "Host-originated resume cannot satisfy a device remote-wakeup scenario")
            svt_usb_status::RESUMING_TO_SEND_EOR:
              check_digital_mac_request("RESUMING_TO_SEND_EOR");
            svt_usb_status::SEND_EOR_TO_ENABLED: begin
              if (!device_origin || !digital_mac_request_checked) begin
                `uvm_fatal(report_id(), "Native EOR completed without DUT-origin K and pre-EOR digital MAC request guard")
              end
              resume_complete = 1'b1;
            end
            default: ;
          endcase
        end
      end
      begin
        eor_observer = process::self();
        // Device-A does not publish every host-transition enum; observe its public link state too.
        wait (shared_status.link_usb_20_state === svt_usb_types::SEND_EOR);
        check_digital_mac_request("native SEND_EOR");
      end
      begin
        uvm_object observed_object;
        svt_usb_packet packet;

        sof_observer = process::self();
        forever begin
          host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(observed_object);
          if (!$cast(packet, observed_object) || packet == null) begin
            `uvm_fatal(report_id(), "Native host TX notification did not contain a USB packet")
          end
          if (resume_complete && shared_status.link_usb_20_state === svt_usb_types::ENABLED &&
              packet.get_pid_name_val() === svt_usb_packet::SOF) begin
            post_resume_sof_count++;
            if (post_resume_sof_count == 1 || post_resume_sof_count % 8 == 0) begin
              `uvm_info(report_id(), $sformatf("Post-resume native SOF progress: transmitted=%0d", post_resume_sof_count), UVM_LOW)
            end
          end
        end
      end
      begin
        int unsigned previous_count;

        sof_watchdog = process::self();
        wait (resume_complete);
        while (!recovery_complete.is_on()) begin
          previous_count = post_resume_sof_count;
          #(sof_progress_timeout);
          if (!recovery_complete.is_on() && post_resume_sof_count == previous_count) begin
            `uvm_fatal(report_id(), $sformatf("No native post-resume SOF progress for %0t: transmitted=%0d state=%s",
              sof_progress_timeout, post_resume_sof_count, shared_status.link_usb_20_state.name()))
          end
        end
      end
      begin
        watchdog = process::self();
        #(link_state_timeout);
        `uvm_fatal(report_id(), $sformatf("Remote wake timed out: device_origin=%0b complete=%0b state=%s",
          device_origin, resume_complete, shared_status.link_usb_20_state.name()))
      end
    join_none
    #0;
    `uvm_info(report_id(), "Stopping SOFs and waiting for native L2 suspend", UVM_LOW)
    sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
    sof_off.start(p_sequencer.prot_service_sequencer);
    wait (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED);
    suspend_observed_at = $time;
    state_deadline = $time + sof_progress_timeout;
    `uvm_info(report_id(), "Native suspend observed; qualifying scaled idle, actual UTMI clock quiescence and DUT low power", UVM_LOW)
    // Observe real UTMI pins/clock; do not assume aggregate PHY status mirrors this port.
    while (!((shared_status.link_usb_20_state === svt_usb_types::SUSPENDED) &&
             (ctrl_vif.dut_suspendm === 1'b0) &&
             ctrl_vif.utmi_clock_quiet(CLOCK_QUIET_OBSERVATION) && ($time - suspend_observed_at >= scaled_remote_wake_idle))) begin
      if ($time >= state_deadline) begin
        `uvm_fatal(report_id(), $sformatf("Accelerated suspend/gating guard timed out: link=%s SuspendM=%b clock_quiet=%b idle=%0t/%0t",
          shared_status.link_usb_20_state.name(), ctrl_vif.dut_suspendm,
          ctrl_vif.utmi_clock_quiet(CLOCK_QUIET_OBSERVATION), $time - suspend_observed_at, scaled_remote_wake_idle))
      end
      @(posedge ctrl_vif.clk);
    end
    `uvm_info(report_id(), "Scaled idle and actual suspended/gated-clock observations qualified; authorizing software wake request", UVM_LOW)
    host_suspended.trigger();
    wake_requested.wait_on();
    wait (device_origin);
    // Rearm native framing during the observed device resume, before EOR.
    // The native link FSM still owns takeover/EOR; this is not host resume.
    sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
    sof_on.start(p_sequencer.prot_service_sequencer);
    `uvm_info(report_id(), "Native DUT wake observed; SOF generation rearmed before EOR", UVM_LOW)
    wait (resume_complete && shared_status.link_usb_20_state === svt_usb_types::ENABLED);
    `uvm_info(report_id(), "Native EOR completed; waiting for an actual transmitted SOF", UVM_LOW)
    wait (post_resume_sof_count != 0);
    state_deadline = $time + sof_progress_timeout;
    // Public DUT Speed is checked after scaled recovery; native PHY checks own UTMI speed behavior.
    `uvm_info(report_id(), "Actual SOF observed; awaiting real UTMI non-suspend/known-control state; DUT HS is checked through CSR", UVM_LOW)
    while (!((ctrl_vif.dut_suspendm === 1'b1) && !$isunknown(ctrl_vif.dut_opmode))) begin
      if ($time >= state_deadline) begin
        `uvm_fatal(report_id(), $sformatf("Accelerated UTMI non-suspend/control guard timed out: SuspendM=%b OpMode=%b; DUT HS check follows recovery",
          ctrl_vif.dut_suspendm, ctrl_vif.dut_opmode))
      end
      @(posedge ctrl_vif.clk);
    end
    `uvm_info(report_id(), "Real UTMI non-suspend/known controls observed; awaiting continued actual SOF progress under the existing watchdog", UVM_LOW)
    wait (post_resume_sof_count >= 2);
    `uvm_info(report_id(), "Continued actual SOF progress observed; proceeding to scaled recovery and checked bulk", UVM_LOW)
    observer.kill();
    if (eor_observer.status() != process::FINISHED) eor_observer.kill();
    if (wake_observer.status() != process::FINISHED) wake_observer.kill();
    watchdog.kill();

    report_protocol_status("After transmitted post-resume SOF");
    host_resumed.trigger();
    `uvm_info(report_id(), "Native device wake/EOR and first SOF verified; observing SOFs through checked recovery", UVM_LOW)
    recovery_complete.wait_on();
    sof_observer.kill();
    if (sof_watchdog.status() != process::FINISHED) sof_watchdog.kill();
    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("Native device wake and checked recovery completed with %0d post-resume SOFs observed",
      post_resume_sof_count), UVM_LOW)
  endtask
endclass
