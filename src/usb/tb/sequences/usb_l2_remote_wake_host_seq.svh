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
  localparam time ACCELERATED_HOST_RESUME_BUDGET = USB_ACCELERATED_HOST_RESUME_BUDGET;
  uvm_event host_suspended;
  uvm_event wake_requested;
  uvm_event host_resumed;
  uvm_event recovery_complete;
  bit [6:0] device_address;
  time link_state_timeout = 35ms;
  time scaled_remote_wake_idle;
  time scaled_recovery;
  int unsigned post_resume_sof_count;

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

  virtual task body();
    svt_usb_protocol_service_20_sof_off_sequence sof_off;
    svt_usb_protocol_service_20_sof_on_sequence sof_on;
    svt_usb_status phy_status;
    process observer;
    process wake_observer;
    process sof_observer;
    process watchdog;
    bit device_origin;
    bit resume_complete;

    completed = 1'b0;
    device_origin = 1'b0;
    resume_complete = 1'b0;
    post_resume_sof_count = 0;
    if (host_suspended == null || wake_requested == null || host_resumed == null || recovery_complete == null) begin
      `uvm_fatal(report_id(), "Suspend, wake, resume and recovery coordination events are required")
    end
    resolve_host_context(1'b1);
    `uvm_info(report_id(),
      $sformatf("Accelerated native profile: idle=%0.0f ps recovery=%0.0f ps host_budget=%0.0f ps recovery_SOF=%0b",
        usb_cfg.twtrsm, usb_cfg.trsmrcy, usb_cfg.tdrsmdn, usb_cfg.enable_sof_during_recovery), UVM_LOW)
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
            svt_usb_status::SEND_EOR_TO_ENABLED: begin
              if (!device_origin) begin
                `uvm_fatal(report_id(), "Native EOR completed without DUT-origin K")
              end
              resume_complete = 1'b1;
            end
            default: ;
          endcase
        end
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
        watchdog = process::self();
        #(link_state_timeout);
        `uvm_fatal(report_id(), $sformatf("Remote wake/recovery timed out: device_origin=%0b complete=%0b SOFs=%0d recovery=%0b state=%s",
          device_origin, resume_complete, post_resume_sof_count, recovery_complete.is_on(), shared_status.link_usb_20_state.name()))
      end
    join_none
    `uvm_info(report_id(), "Stopping SOFs and waiting for native L2 suspend", UVM_LOW)
    sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
    sof_off.start(p_sequencer.prot_service_sequencer);
    wait (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED);
    `uvm_info(report_id(), $sformatf("Native suspend observed; holding scaled idle for %0t before authorizing software wake",
      scaled_remote_wake_idle), UVM_LOW)
    #(scaled_remote_wake_idle);
    if (shared_status.link_usb_20_state !== svt_usb_types::SUSPENDED) begin
      `uvm_fatal(report_id(), "Native link left suspend before software wake was authorized")
    end
    `uvm_info(report_id(), "Native suspend and scaled idle qualified; authorizing software wake request", UVM_LOW)
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
    `uvm_info(report_id(), "Actual SOF observed; awaiting two transmitted SOFs before DUT status and recovery checks", UVM_LOW)
    wait (post_resume_sof_count >= 2);
    `uvm_info(report_id(), "Continued actual SOF progress observed; proceeding to scaled recovery and checked bulk", UVM_LOW)
    observer.kill();
    if (wake_observer.status() != process::FINISHED) wake_observer.kill();

    report_protocol_status("After transmitted post-resume SOF");
    host_resumed.trigger();
    `uvm_info(report_id(), "Native device wake/EOR and first SOF verified; observing SOFs through checked recovery", UVM_LOW)
    recovery_complete.wait_on();
    sof_observer.kill();
    watchdog.kill();
    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("Native device wake and checked recovery completed with %0d post-resume SOFs observed",
      post_resume_sof_count), UVM_LOW)
  endtask
endclass
