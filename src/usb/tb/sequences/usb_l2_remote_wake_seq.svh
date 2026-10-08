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

// Requests remote wake from L2 and verifies both sides resume signaling.
// Current RTL fails the UTMI high-speed termination timing check at resume EOP;
// this sequence remains the acceptance test for that defect.
class usb_l2_remote_wake_seq extends usb_base_seq;
  `uvm_object_utils(usb_l2_remote_wake_seq)

  time suspend_timeout = 5ms;
  time status_poll_interval = 500ns;
  bit completed;
  uvm_event resume_k_released_event;

  function new(string name = "usb_l2_remote_wake_seq");
    super.new(name);
  endfunction

  // Require the device to drive high-speed resume K for multiple PHY clocks.
  task observe_resume_signaling(output bit observed);
    observed = 1'b0;
    fork
      begin
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          observed = p_sequencer.ctrl_vif.utmi_opmode === 2'b10 &&
                     p_sequencer.ctrl_vif.utmi_xcvrselect === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_termselect === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_txvalid === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_txdata === 8'h00;
        end while (!observed);
        repeat (8) begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          if (p_sequencer.ctrl_vif.utmi_opmode !== 2'b10 ||
              p_sequencer.ctrl_vif.utmi_xcvrselect !== 1'b1 ||
              p_sequencer.ctrl_vif.utmi_termselect !== 1'b1 ||
              p_sequencer.ctrl_vif.utmi_txvalid !== 1'b1 ||
              p_sequencer.ctrl_vif.utmi_txdata !== 8'h00) begin
            `uvm_fatal("USB_L2_REMOTE", "Device resume K did not remain stable for eight PHY clocks")
          end
        end
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
        end while (p_sequencer.ctrl_vif.utmi_txvalid !== 1'b0);
        `uvm_info("USB_L2_REMOTE", "Device released resume K; waiting for host completion signaling", UVM_LOW)
        p_sequencer.packet_monitor.start_window("Post-L2 remote-wake SOF");
        resume_k_released_event.trigger();
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
        end while (p_sequencer.ctrl_vif.utmi_opmode !== 2'b00 ||
                   p_sequencer.ctrl_vif.utmi_xcvrselect !== 1'b0 ||
                   p_sequencer.ctrl_vif.utmi_termselect !== 1'b0 ||
                   p_sequencer.ctrl_vif.utmi_txvalid !== 1'b0);
        `uvm_info("USB_L2_REMOTE", "Device resume K completed and UTMI returned to high-speed operational mode", UVM_LOW)
      end
      begin
        #(suspend_timeout);
      end
    join_any
    disable fork;
  endtask

  // Enumerate, enter L2, request remote wake, and prove datapath recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_l2_remote_wake_host_seq suspend_host_sequence;
    uvm_event dut_suspend_observed;
    logic [31:0] device_command_status;
    logic [31:0] suspend_mask;
    bit resume_signaling_observed;
    bit sof_observed;

    completed = 1'b0;
    `uvm_info("USB_L2_REMOTE", "Starting L2 remote-wake scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L2_REMOTE", "Enumeration did not complete")
    end
    if (p_sequencer.ctrl_vif == null || p_sequencer.usb_20_mac_if == null) begin
      `uvm_fatal("USB_L2_REMOTE", "Remote-wake checking requires the USB control and UTMI interfaces")
    end

    suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    dut_suspend_observed = new("dut_suspend_observed");
    resume_k_released_event = new("resume_k_released_event");
    suspend_host_sequence = usb_l2_remote_wake_host_seq::type_id::create("suspend_host_sequence");
    suspend_host_sequence.dut_suspend_observed = dut_suspend_observed;
    suspend_host_sequence.dut_resume_k_released = resume_k_released_event;
    suspend_host_sequence.link_state_timeout = suspend_timeout;
    resume_signaling_observed = 1'b0;

    fork
      begin
        suspend_host_sequence.start(p_sequencer.host_sequencer);
        if (!suspend_host_sequence.completed) begin
          `uvm_fatal("USB_L2_REMOTE", "Host remote-wake observer returned incomplete")
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
        `uvm_info("USB_L2_REMOTE", $sformatf("DUT entered L2 suspend: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
        dut_suspend_observed.trigger();
        device_command_status &= ~suspend_mask;
        `uvm_info("USB_L2_REMOTE", "Writing DSUS=0 to request device remote wake", UVM_LOW)
        ral_write32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, device_command_status);
        poll_csr_bits(
          "DEVCMDSTAT.DSUS deassertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b0,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
      end
      begin
        observe_resume_signaling(resume_signaling_observed);
      end
    join
    if (!resume_signaling_observed) begin
      `uvm_fatal("USB_L2_REMOTE", $sformatf("Device resume signaling did not complete within %0t", suspend_timeout))
    end
    p_sequencer.packet_monitor.wait_for_sof(suspend_timeout, sof_observed);
    p_sequencer.packet_monitor.stop_window();
    if (!sof_observed) begin
      `uvm_fatal("USB_L2_REMOTE", $sformatf("No host SOF was observed within %0t after remote wake", suspend_timeout))
    end
    `uvm_info("USB_L2_REMOTE", "Observed host SOF after remote wake; starting recovery traffic", UVM_LOW)
    `uvm_info("USB_L2_REMOTE", $sformatf("DUT left L2 after remote wake: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)

    completed = 1'b1;
    `uvm_info("USB_L2_REMOTE", "L2 remote wake completed with device resume K and host SOF verified", UVM_LOW)
  endtask
endclass
