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

class usb_l2_remote_wake_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_l2_remote_wake_seq)

  time resume_timeout = 35ms;
  bit completed;

  function new(string name = "usb_l2_remote_wake_seq");
    super.new(name);
  endfunction

  virtual task body();
    usb_init_seq init_sequence;
    usb_remote_wake_enable_host_seq enable_sequence;
    usb_l2_remote_wake_host_seq host_sequence;
    uvm_event host_suspended;
    uvm_event wake_requested;
    uvm_event host_resumed;
    uvm_event recovery_complete;
    logic [31:0] command;
    logic [31:0] suspend_mask;
    logic [31:0] address_mask;
    logic [31:0] speed_mask;
    uvm_reg_field address_field;
    uvm_reg_field speed_field;
    int unsigned authorization_request_count;

    completed = 1'b0;
    `uvm_info("USB_L2_REMOTE", "Enumerating a remote-wakeup-capable device", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.remote_wakeup_supported = 1'b1;
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L2_REMOTE", "Enumeration did not complete")
    end

    enable_sequence = usb_remote_wake_enable_host_seq::type_id::create("enable_sequence");
    enable_sequence.control_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
    enable_sequence.device_address = p_sequencer.cfg.device_address;
    enable_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    authorization_request_count = init_sequence.serviced_request_count + usb_remote_wake_enable_host_seq::AUTHORIZATION_REQUEST_COUNT;
    fork
      enable_sequence.start(p_sequencer.host_sequencer);
      init_sequence.service_ep0(authorization_request_count);
    join
    if (!enable_sequence.completed || !init_sequence.remote_wakeup_enabled ||
        init_sequence.serviced_request_count != authorization_request_count) begin
      `uvm_fatal("USB_L2_REMOTE", "Protocol discovery and DEVICE_REMOTE_WAKEUP authorization did not complete")
    end

    host_suspended = new("host_suspended");
    wake_requested = new("wake_requested");
    host_resumed = new("host_resumed");
    recovery_complete = new("recovery_complete");
    host_sequence = usb_l2_remote_wake_host_seq::type_id::create("host_sequence");
    host_sequence.host_suspended = host_suspended;
    host_sequence.wake_requested = wake_requested;
    host_sequence.host_resumed = host_resumed;
    host_sequence.recovery_complete = recovery_complete;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.link_state_timeout = resume_timeout;
    host_sequence.ctrl_vif = p_sequencer.ctrl_vif;
    suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    address_field = p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR;
    address_mask = ral_field_mask(address_field);
    speed_field = p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.Speed;
    speed_mask = ral_field_mask(speed_field);
    fork
      host_sequence.start(p_sequencer.host_sequencer);
      begin
        poll_csr_bits("DUT L2 entry", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      suspend_mask, 1'b1, resume_timeout, command);
        host_suspended.wait_on();
        `uvm_info("USB_L2_REMOTE", "Native scaled idle and actual suspend/gating qualified; requesting authorized device wake", UVM_LOW)
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        if ((command & suspend_mask) !== suspend_mask || !init_sequence.remote_wakeup_enabled) begin
          `uvm_fatal("USB_L2_REMOTE", "DUT is not suspended with remote wake authorized")
        end
        wake_requested.trigger();
        // Preserve the staged address and request wake through the software interface.
        init_sequence.write_devcmdstat(command & ~suspend_mask);
        poll_csr_bits("DUT L2 exit", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      suspend_mask, 1'b0, resume_timeout, command);
        host_resumed.wait_on();
        `uvm_info("USB_L2_REMOTE", $sformatf("Native EOR/SOF and real UTMI non-suspend verified; observing scaled recovery for %0t",
          host_sequence.scaled_recovery), UVM_LOW)
        #(host_sequence.scaled_recovery);
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        // Public Speed=2'b10 is HS; descriptor ownership and checked completion prove functional admission.
        if ((command & suspend_mask) !== 32'b0 || 2'((command & speed_mask) >> speed_field.get_lsb_pos()) !== 2'b10) begin
          `uvm_fatal("USB_L2_REMOTE", $sformatf("Accelerated recovery incompatible: DUT must be non-suspended at HS, DEVCMDSTAT=0x%08h", command))
        end
        if (7'((command & address_mask) >> address_field.get_lsb_pos()) !== p_sequencer.cfg.device_address) begin
          `uvm_fatal("USB_L2_REMOTE", "Device address changed across remote wake")
        end
        host_sequence.report_protocol_status("After scaled recovery and public DUT HS/non-suspend check");
        recovery_timeout = 2ms;
        run_recovery_transfer("Post-device-remote-wake bulk OUT");
        recovery_complete.trigger();
      end
    join
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_L2_REMOTE", "VIP did not complete device-initiated resume")
    end
    completed = 1'b1;
    `uvm_info("USB_L2_REMOTE", "Authorized device remote wake preserved the address and recovered bulk traffic", UVM_LOW)
  endtask
endclass
