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

class usb_l1_remote_wake_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_l1_remote_wake_seq)

  // USB 2.0 LPM ECN section 4.9, Table 4-6: minimum 50 us, away from the boundary.
  localparam time L1_RESIDENCY = 75us;
  localparam time DEVICE_RECOVERY = 10us;
  time resume_timeout = 2ms;
  bit completed;

  function new(string name = "usb_l1_remote_wake_seq");
    super.new(name);
  endfunction

  virtual task body();
    usb_init_seq init_sequence;
    usb_lpm_capability_host_seq discovery_sequence;
    usb_l1_remote_wake_host_seq host_sequence;
    uvm_event host_suspended;
    uvm_event wake_requested;
    logic [31:0] command;
    logic [31:0] lpm_suspend_mask;
    logic [31:0] wake_permission_mask;
    logic [31:0] address_mask;
    logic [31:0] address_before_wake;
    int unsigned request_count;

    completed = 1'b0;
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.lpm_supported = 1'b1;
    `uvm_info("USB_L1_REMOTE", "Enumerating an LPM-capable device and discovering its BOS capabilities", UVM_LOW)
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L1_REMOTE", "Enumeration did not complete")
    end
    discovery_sequence = usb_lpm_capability_host_seq::type_id::create("discovery_sequence");
    discovery_sequence.control_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
    discovery_sequence.device_address = p_sequencer.cfg.device_address;
    discovery_sequence.control_transfer_timeout = p_sequencer.cfg.control_transfer_timeout;
    request_count = init_sequence.serviced_request_count + usb_lpm_capability_host_seq::DISCOVERY_REQUEST_COUNT;
    fork
      discovery_sequence.start(p_sequencer.host_sequencer);
      init_sequence.service_ep0(request_count);
    join
    if (!discovery_sequence.completed || init_sequence.serviced_request_count != request_count) begin
      `uvm_fatal("USB_L1_REMOTE", "Protocol discovery did not establish LPM capability")
    end

    host_suspended = new("host_suspended");
    wake_requested = new("wake_requested");
    host_sequence = usb_l1_remote_wake_host_seq::type_id::create("host_sequence");
    host_sequence.host_suspended = host_suspended;
    host_sequence.wake_requested = wake_requested;
    host_sequence.device_address = p_sequencer.cfg.device_address;
    host_sequence.link_state_timeout = resume_timeout;
    lpm_suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.LPM_SUS);
    wake_permission_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.LPM_REWP);
    address_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR);
    fork
      host_sequence.start(p_sequencer.host_sequencer);
      begin
        poll_csr_bits("DUT L1 entry", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      lpm_suspend_mask, 1'b1, resume_timeout, command);
        host_suspended.wait_on();
        `uvm_info("USB_L1_REMOTE", "Both peers entered L1; holding 75 us before device wake", UVM_LOW)
        #(L1_RESIDENCY);
        ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
        if ((command & (lpm_suspend_mask | wake_permission_mask)) !== (lpm_suspend_mask | wake_permission_mask)) begin
          `uvm_fatal("USB_L1_REMOTE", "DUT is not in L1 with host-granted remote-wake permission")
        end
        address_before_wake = command & address_mask;
        wake_requested.trigger();
        // LPM_SUS write-zero requests wake; hardware owns the status transition.
        init_sequence.write_devcmdstat(command & ~lpm_suspend_mask);
        poll_csr_bits("DUT L1 exit", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
                      lpm_suspend_mask, 1'b0, resume_timeout, command);
      end
    join
    if (!host_sequence.completed) begin
      `uvm_fatal("USB_L1_REMOTE", "Native host did not complete device-initiated L1 exit")
    end
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & address_mask) !== address_before_wake) begin
      `uvm_fatal("USB_L1_REMOTE", "Device address changed across L1 remote wake")
    end
    #(DEVICE_RECOVERY);
    recovery_timeout = resume_timeout;
    run_recovery_transfer("Post-device-L1-remote-wake bulk OUT");
    completed = 1'b1;
    `uvm_info("USB_L1_REMOTE", "Device-initiated L1 wake preserved the address and recovered bulk traffic", UVM_LOW)
  endtask
endclass
