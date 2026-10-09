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

// Sends an LPM L1 token, waits for DUT observation, then drives host exit.
class usb_l1_host_resume_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_l1_host_resume_host_seq)

  uvm_event dut_l1_observed;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] lpm_hird = 4'h1;
  time link_state_timeout = 750us;

  function new(string name = "usb_l1_host_resume_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_L1_HOST";
  endfunction

  // Wait for the device-side LPM_SUS check before driving L1 exit.
  task wait_for_dut_l1_observation();
    bit observed;

    if (dut_l1_observed == null) begin
      `uvm_fatal(report_id(), "No DUT L1-observation event was supplied")
    end
    observed = 1'b0;
    `uvm_info(report_id(), $sformatf("Waiting up to %0t for DUT L1 observation", link_state_timeout), UVM_LOW)
    fork
      begin
        dut_l1_observed.wait_trigger();
        observed = 1'b1;
      end
      begin
        #(link_state_timeout);
      end
    join_any
    disable fork;
    if (!observed) begin
      `uvm_fatal(report_id(), $sformatf("DUT L1 entry was not observed within %0t", link_state_timeout))
    end
  endtask

  // Drive one addressed LPM entry and host-initiated L1 exit.
  virtual task body();
    svt_usb_protocol_service_usb_20_lpm_sequence lpm_sequence;
    svt_usb_link_service_clear_l1suspend_sequence resume_sequence;

    completed = 1'b0;
    resolve_host_context(1'b1);
    `uvm_info(
      report_id(),
      $sformatf("Sending LPM token: address=%0d bLinkState=1 HIRD=%0d bRemoteWake=1", device_address, lpm_hird),
      UVM_LOW
    )
    lpm_sequence = svt_usb_protocol_service_usb_20_lpm_sequence::type_id::create("lpm_sequence");
    lpm_sequence.blinkstate = 4'h1;
    lpm_sequence.dev_address = device_address;
    lpm_sequence.lpm_hird = lpm_hird;
    lpm_sequence.lpm_bremotewake = 1'b1;
    lpm_sequence.start(p_sequencer.prot_service_sequencer);

    wait_for_dut_l1_observation();
    `uvm_info(report_id(), "Driving host L1 exit", UVM_LOW)
    resume_sequence = svt_usb_link_service_clear_l1suspend_sequence::type_id::create("resume_sequence");
    resume_sequence.start(p_sequencer.link_service_sequencer);
    wait_for_link_enabled(link_state_timeout);

    completed = 1'b1;
    `uvm_info(report_id(), "Host L1 suspend/resume cycle completed with the link ENABLED", UVM_LOW)
  endtask
endclass
