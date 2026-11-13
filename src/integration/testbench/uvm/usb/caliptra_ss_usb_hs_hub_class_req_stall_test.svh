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

`ifndef CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_TEST_SV

// =============================================================================
// High-Speed hub class-request STALL decode test.
//
// Runs caliptra_ss_usb_hs_hub_class_req_stall_sequence: hub-only enumeration,
// then six UNSUPPORTED hub class requests that must each be STALLed, followed
// by one legal GetPortStatus that must complete. Stimulus for the hub half of
// coverage gap G9 of docs/usb_coverage_gaps.md.
//
// WHY THIS TEST CLASS SETS NOTHING BEYOND THE SPEED
//
// The sequence is EP0 control-transfer only. It drives no data traffic, so no
// endpoint model beyond the shared configuration's CONTROL entry is needed -
// unlike caliptra_ss_usb_hs_hub_int_ep_status_change_test, which has to declare
// the hub INTERRUPT IN endpoint because it polls it.
//
// The shared NAK retry budget is likewise left alone. A STALLed control
// transfer terminates on the STALL handshake, not by exhausting retries, so the
// large software-polled-device budget in caliptra_ss_usb_shared_cfg costs
// nothing here.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_class_req_stall_test
// =============================================================================

class caliptra_ss_usb_hs_hub_class_req_stall_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_class_req_stall_test)

    function new(string name = "caliptra_ss_usb_hs_hub_class_req_stall_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default so the VIP chirps.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_hub_class_req_stall_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_STALL_TEST_SV
