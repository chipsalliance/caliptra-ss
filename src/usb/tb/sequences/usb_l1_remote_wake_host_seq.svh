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

class usb_l1_remote_wake_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_l1_remote_wake_host_seq)

  uvm_event host_suspended;
  uvm_event wake_requested;
  bit [6:0] device_address;
  time link_state_timeout = 2ms;

  function new(string name = "usb_l1_remote_wake_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_L1_REMOTE_HOST";
  endfunction

  virtual task body();
    svt_usb_transaction lpm_transaction;
    svt_usb_protocol_service lpm_request;
    svt_usb_protocol_service lpm_response;
    uvm_sequence_item response;
    process entry_observer;
    process exit_observer;
    process sof_observer;
    process forbidden_observer;
    process watchdog;
    bit entered_l1;
    bit device_origin;
    bit post_wake_sof;

    completed = 1'b0;
    entered_l1 = 1'b0;
    device_origin = 1'b0;
    post_wake_sof = 1'b0;
    if (host_suspended == null || wake_requested == null) begin
      `uvm_fatal(report_id(), "Suspend and device-wake coordination events are required")
    end
    resolve_host_context(1'b1);
    if (usb_cfg.tl1residency_min != usb_vip_cfg_builder::vip_ps(50us) ||
        usb_cfg.tl1devdrvresume_min != usb_vip_cfg_builder::vip_ps(50us) ||
        usb_cfg.tl1hubreflect > usb_vip_cfg_builder::vip_ps(48us) ||
        usb_cfg.tl1hubreflect_max != usb_vip_cfg_builder::vip_ps(48us) ||
        usb_cfg.tl1hubdrvresume2 < usb_vip_cfg_builder::vip_ps(60us) ||
        usb_cfg.tl1hubdrvresume2 > usb_vip_cfg_builder::vip_ps(990us) ||
        usb_cfg.tl1hubdrvresume2_min != usb_vip_cfg_builder::vip_ps(60us) ||
        usb_cfg.tl1hubdrvresume2_max != usb_vip_cfg_builder::vip_ps(990us)) begin
      `uvm_fatal(report_id(), "Effective LPM drive/checker timers do not match the unscaled remote-wake profile")
    end
    if (shared_status.local_host_status == null) begin
      `uvm_fatal(report_id(), "Native host SOF status is unavailable")
    end
    // Native link notifications distinguish device wake from host resume.
    // Arm them before LPM; no host clear_l1suspend service is used.
    fork
      begin
        entry_observer = process::self();
        host_agent.link.NOTIFY_BUS_IS_L1SUSPENDED.wait_trigger();
        entered_l1 = 1'b1;
      end
      begin
        exit_observer = process::self();
        host_agent.link.NOTIFY_L1_EXIT_VIA_DEVICE_INITIATED_RESUME.wait_trigger();
        if (!wake_requested.is_on() || !entered_l1) begin
          `uvm_fatal(report_id(), "Device-origin L1 exit preceded the authorized software wake request")
        end
        device_origin = 1'b1;
      end
      begin
        uvm_object observed_object;
        svt_usb_packet packet;

        sof_observer = process::self();
        while (!post_wake_sof) begin
          host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(observed_object);
          if (!$cast(packet, observed_object) || packet == null) begin
            `uvm_fatal(report_id(), "Native host packet notification did not contain a USB packet")
          end
          post_wake_sof = device_origin && shared_status.link_usb_20_state === svt_usb_types::ENABLED &&
                          packet.pid_name == svt_usb_packet::SOF;
        end
      end
      begin
        forbidden_observer = process::self();
        fork
          begin
            host_agent.link.NOTIFY_L1_EXIT_VIA_HOST_INITIATED_RESUME.wait_trigger();
            `uvm_fatal(report_id(), "Host-origin L1 resume cannot satisfy device remote wake")
          end
          begin
            host_agent.link.NOTIFY_L1_EXIT_VIA_RESET.wait_trigger();
            `uvm_fatal(report_id(), "USB reset cannot satisfy L1 remote wake")
          end
          begin
            host_agent.link.NOTIFY_L1_EXIT_VIA_DEVICE_DISCONNECT.wait_trigger();
            `uvm_fatal(report_id(), "Device disconnect cannot satisfy L1 remote wake")
          end
          begin
            wait (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED);
            `uvm_fatal(report_id(), "Ordinary L2 suspend cannot satisfy the L1 scenario")
          end
        join_any
        disable fork;
      end
      begin
        watchdog = process::self();
        #(link_state_timeout);
        `uvm_fatal(report_id(), $sformatf("L1 remote wake timed out: entry=%0b device_origin=%0b post_wake_sof=%0b state=%s",
          entered_l1, device_origin, post_wake_sof, shared_status.link_usb_20_state.name()))
      end
    join_none
    #0;
    `uvm_info(report_id(), "Sending addressed LPM: L1, HIRD=1, bRemoteWake=1", UVM_LOW)
    lpm_transaction = svt_usb_transaction::type_id::create("lpm_transaction");
    lpm_transaction.cfg = usb_cfg;
    lpm_request = svt_usb_protocol_service::type_id::create("lpm_request");
    lpm_request.cfg = usb_cfg;
    lpm_request.service_xact = lpm_transaction;
    start_item(lpm_request, -1, p_sequencer.prot_service_sequencer);
    // service_xact is rand: constrain its fields in the enclosing service solve.
    if (!lpm_request.randomize() with {
          service_type == svt_usb_protocol_service::LPM;
          device_address == local::device_address;
          service_xact.xact_type == svt_usb_types::LPM_TRANSACTION;
          service_xact.device_address == local::device_address;
          service_xact.lpm_blinkstate == 4'h1;
          service_xact.lpm_hird == 4'h1;
          service_xact.lpm_bremotewake == 1'b1;
        }) begin
      `uvm_fatal(report_id(), "Unable to randomize the native LPM service")
    end
    finish_item(lpm_request);
    // Keep the submitting sequence alive until the routed response is consumed.
    get_response(response, lpm_request.get_transaction_id());
    if (!$cast(lpm_response, response) || lpm_response == null ||
        lpm_response.service_type != svt_usb_protocol_service::LPM ||
        response.get_sequence_id() != lpm_request.get_sequence_id()) begin
      `uvm_fatal(report_id(), "Native LPM service returned an invalid routed response")
    end
    // Successful LPM service submission is not proof of an ACK/L1 transition.
    wait (entered_l1 && shared_status.link_usb_20_power_state === svt_usb_types::POWER_STATE_L1);
    host_suspended.trigger();
    wake_requested.wait_on();
    wait (device_origin && shared_status.link_usb_20_state === svt_usb_types::ENABLED);
    if (!shared_status.local_host_status.sof_generation_enabled) begin
      `uvm_fatal(report_id(), "The native SOF service did not remain enabled across L1")
    end
    wait (post_wake_sof);
    if (entry_observer.status() != process::FINISHED) entry_observer.kill();
    if (exit_observer.status() != process::FINISHED) exit_observer.kill();
    if (sof_observer.status() != process::FINISHED) sof_observer.kill();
    forbidden_observer.kill();
    watchdog.kill();
    completed = 1'b1;
    `uvm_info(report_id(), "Native device-origin L1 exit completed; link active and post-wake SOF transmitted", UVM_LOW)
  endtask
endclass
