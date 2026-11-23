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

// Sends LPM, holds after native/DUT admission, then checks host resume initiation.
class usb_l1_host_resume_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_l1_host_resume_host_seq)

  uvm_event dut_l1_observed;
  bit legacy_lpm_confirmed;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] lpm_hird = 4'h1;
  time link_state_timeout = 750us;

  function new(string name = "usb_l1_host_resume_host_seq");
    super.new(name);
  endfunction

  virtual function string report_id();
    return "USB_L1_HOST";
  endfunction

  // Drive one addressed LPM entry and host-initiated L1 exit.
  virtual task body();
    svt_usb_protocol_service_usb_20_lpm_sequence lpm_sequence;
    svt_usb_link_service_clear_l1suspend_sequence resume_sequence;
    int saved_protocol_action;
    int saved_link_action;

    completed = 1'b0;
    resolve_host_context(1'b1);
    if (!(legacy_lpm_confirmed === 1'b1) || !(lpm_hird === 4'h1)) begin
      `uvm_fatal(report_id(), $sformatf("Legacy policy eligibility mismatch: actual discovered_legacy=%0b HIRD=%0d; expected legacy=1 HIRD=1",
        legacy_lpm_confirmed, lpm_hird))
    end
    // Require usable resolved legacy drive/check bounds, not a second policy construction.
    if (!(usb_cfg.select_lpm_errata_mode === 1'b0) ||
        !((usb_cfg.tl1hubdrvresume1_min > 0.0) === 1'b1) ||
        !((usb_cfg.tl1hubdrvresume1 >= usb_cfg.tl1hubdrvresume1_min) === 1'b1) ||
        !((usb_cfg.tl1hubdrvresume1 <= usb_cfg.tl1hubdrvresume1_max) === 1'b1)) begin
      `uvm_fatal(report_id(), "Effective legacy LPM mode requires positive, ordered host resume drive/check bounds")
    end
    `uvm_info(report_id(), $sformatf("Native legacy HIRD1 configuration ready: mode=%0b drive/min/max=%0.0f/%0.0f/%0.0f ps",
      usb_cfg.select_lpm_errata_mode, usb_cfg.tl1hubdrvresume1, usb_cfg.tl1hubdrvresume1_min, usb_cfg.tl1hubdrvresume1_max), UVM_LOW)
    // SVT's built-in svt_dropping_response_report_catcher passes a slash-less
    // ".*" pattern to uvm_re_match(), which UVM 1800.2 routes to uvm_glob_match()
    // where "." is literal. Suppress "Sequencer" warnings here to restore SVT's
    // intended default suppression for asynchronous service responses.
    saved_protocol_action = p_sequencer.prot_service_sequencer.get_report_action(UVM_WARNING, "Sequencer");
    p_sequencer.prot_service_sequencer.set_report_severity_id_action(UVM_WARNING, "Sequencer", UVM_NO_ACTION);
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
    begin_l1_host_residency_watch(link_state_timeout);
    lpm_sequence.start(p_sequencer.prot_service_sequencer);
    p_sequencer.prot_service_sequencer.set_report_severity_id_action(UVM_WARNING, "Sequencer", saved_protocol_action);

    wait_for_l1_host_residency(dut_l1_observed);
    `uvm_info(report_id(), "Driving host L1 exit", UVM_LOW)
    resume_sequence = svt_usb_link_service_clear_l1suspend_sequence::type_id::create("resume_sequence");
    saved_link_action = p_sequencer.link_service_sequencer.get_report_action(UVM_WARNING, "Sequencer");
    p_sequencer.link_service_sequencer.set_report_severity_id_action(UVM_WARNING, "Sequencer", UVM_NO_ACTION);
    resume_sequence.start(p_sequencer.link_service_sequencer);
    p_sequencer.link_service_sequencer.set_report_severity_id_action(UVM_WARNING, "Sequencer", saved_link_action);
    // Confine the existing ENABLED wait's cancellation to its own children.
    fork begin
      wait_for_link_enabled(link_state_timeout);
    end join
    end_l1_host_residency_watch();

    completed = 1'b1;
    `uvm_info(report_id(), "Host L1 suspend/resume cycle completed with the link ENABLED", UVM_LOW)
  endtask
endclass
