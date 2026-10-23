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

// Checks DEV0 L2 status across host resume and verifies post-resume traffic.
//
// Relies on the Synopsys SVT USB VIP's built-in suspend/resume sequences
// (svt_usb_protocol_service_20_sof_off_sequence,
// svt_usb_link_service_clear_suspend_sequence, and
// svt_usb_protocol_service_20_sof_on_sequence in
// sequences/class_svt_usb_protocol_service_20_sof_off_sequence.html,
// sequences/class_svt_usb_link_service_clear_suspend_sequence.html, and
// sequences/class_svt_usb_protocol_service_20_sof_on_sequence.html),
// shared_status.link_usb_20_state (SUSPEND -> RESUME -> L0), and built-in
// protocol/link/physical checks (enabled by default via
// register_default_chks = 1, enable_default_chks = 1 in protocolChecks.html,
// coverage/class_svt_usb_protocol_ep_sc.html,
// coverage/class_svt_usb_link_20_host_sc.html, and
// coverage/class_svt_usb_physical_20_sc.html):
//   - svt_usb_protocol_ep_sc:
//     * packet_error_check, valid_device_response_check, data_toggle_check,
//       sof_not_received_after_link_enters_l0
//   - svt_usb_link_20_host_sc:
//     * tdrsmdn_timing_check
//   - svt_usb_physical_20_sc:
//     * chk_utmi_suspendm, chk_utmi_resume_length,
//       chk_utmi_speed_before_and_after_suspend_resume,
//       chk_utmi_after_resume_switch_to_hs, utmi_signal_X_Z_check
class usb_l2_host_resume_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_l2_host_resume_seq)

  time suspend_timeout = 750us;
  time status_poll_interval = 500ns;
  bit completed;

  function new(string name = "usb_l2_host_resume_seq");
    super.new(name);
  endfunction

  // Enumerate, check L2 entry/exit, then prove endpoint traffic recovers.
  virtual task body();
    usb_init_seq init_sequence;
    usb_l2_host_resume_host_seq suspend_host_sequence;
    uvm_event dut_suspend_observed;
    logic [31:0] device_command_status;
    logic [31:0] suspend_mask;

    completed = 1'b0;
    `uvm_info("USB_L2_SEQ", "Starting L2 host-resume scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L2_SEQ", "Enumeration did not complete")
    end

    suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    dut_suspend_observed = new("dut_suspend_observed");
    suspend_host_sequence = usb_l2_host_resume_host_seq::type_id::create("suspend_host_sequence");
    suspend_host_sequence.dut_suspend_observed = dut_suspend_observed;
    suspend_host_sequence.link_state_timeout = suspend_timeout;

    fork
      begin
        suspend_host_sequence.start(p_sequencer.host_sequencer);
        if (!suspend_host_sequence.completed) begin
          `uvm_fatal("USB_L2_SEQ", "Host suspend/resume sequence returned incomplete")
        end
      end
      begin
        poll_csr_bits(
          "DEVCMDSTAT.DSUS assertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b1,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
        `uvm_info("USB_L2_SEQ", $sformatf("DUT entered L2 suspend: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
        dut_suspend_observed.trigger();
        poll_csr_bits(
          "DEVCMDSTAT.DSUS deassertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b0,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
        `uvm_info("USB_L2_SEQ", $sformatf("DUT left L2 suspend after host resume: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
      end
    join

    recovery_timeout = suspend_timeout;
    recovery_poll_interval = status_poll_interval;
    run_recovery_transfer("Post-L2 recovery bulk OUT");

    completed = 1'b1;
    `uvm_info("USB_L2_SEQ", "L2 host-resume scenario completed with DUT status transitions and recovery traffic verified", UVM_LOW)
  endtask
endclass
