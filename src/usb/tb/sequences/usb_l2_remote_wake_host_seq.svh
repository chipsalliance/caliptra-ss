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

// Stops SOF for L2 entry and waits for device-initiated resume signaling.
class usb_l2_remote_wake_host_seq extends usb_l2_host_resume_host_seq;
  `uvm_object_utils(usb_l2_remote_wake_host_seq)

  uvm_event dut_resume_k_released;

  function new(string name = "usb_l2_remote_wake_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_L2_REMOTE_HOST";
  endfunction

  // Enter suspend, release the device-side checker, and observe remote wake.
  virtual task body();
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;
    svt_usb_link_service_clear_suspend_sequence resume_sequence;
    bit suspended;
    bit resume_k_released;

    completed = 1'b0;
    resolve_host_context(1'b1);
    `uvm_info(report_id(), "Stopping SOF generation to enter L2 suspend", UVM_LOW)
    sof_off_sequence = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off_sequence");
    sof_off_sequence.start(p_sequencer.prot_service_sequencer);

    suspended = 1'b0;
    fork
      begin
        wait (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED);
        suspended = 1'b1;
      end
      begin
        #(link_state_timeout);
      end
    join_any
    disable fork;
    if (!suspended) begin
      `uvm_fatal(report_id(), $sformatf("Host link did not reach SUSPENDED within %0t; state=%s", link_state_timeout, shared_status.link_usb_20_state.name()))
    end
    `uvm_info(report_id(), "Host link reached SUSPENDED; releasing the DUT remote-wake request", UVM_LOW)
    wait_for_dut_suspend_observation();
    if (dut_resume_k_released == null) begin
      `uvm_fatal(report_id(), "No DUT resume-K release event was supplied")
    end
    resume_k_released = 1'b0;
    fork
      begin
        dut_resume_k_released.wait_ptrigger();
        resume_k_released = 1'b1;
      end
      begin
        #(link_state_timeout);
      end
    join_any
    disable fork;
    if (!resume_k_released) begin
      `uvm_fatal(report_id(), $sformatf("DUT did not release resume K within %0t", link_state_timeout))
    end

    `uvm_info(report_id(), "DUT released resume K; completing host resume and restarting SOF", UVM_LOW)
    resume_sequence = svt_usb_link_service_clear_suspend_sequence::type_id::create("resume_sequence");
    resume_sequence.start(p_sequencer.link_service_sequencer);
    sof_on_sequence = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_sequence");
    sof_on_sequence.start(p_sequencer.prot_service_sequencer);
    wait_for_link_enabled(link_state_timeout);
    completed = 1'b1;
    `uvm_info(report_id(), "Device-initiated L2 remote wake completed with the link ENABLED", UVM_LOW)
  endtask
endclass
