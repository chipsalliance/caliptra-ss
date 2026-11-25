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

`ifndef CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_TEST_SV

// =============================================================================
// High-Speed hub class-request INVALID test.
//
// Runs caliptra_ss_usb_hs_hub_class_req_invalid_sequence, which extends the
// class_req_stall sequence: the parent's nine steps, then hub-itself
// Clear/SetHubFeature, accepted no-op port features, PORT_ENABLE set/clear,
// further port numbers > C_HUB_NB_PORTS, invalid feature selectors, wValue and
// wIndex toggle patterns, undefined class bRequest codes and a GetHubStatus
// through a firmware-patched SETUP row (ep0_request opcode 0x72).
//
// Like the parent test class, only the speed is set: the sequence is EP0
// control transfers only, every rejected request ends on a real STALL
// handshake, and nothing times out, so no endpoint model, NAK budget or
// report catcher is needed.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_class_req_invalid_test
// =============================================================================

class caliptra_ss_usb_hs_hub_class_req_invalid_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_class_req_invalid_test)

    function new(string name = "caliptra_ss_usb_hs_hub_class_req_invalid_test",
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
            caliptra_ss_usb_hs_hub_class_req_invalid_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_CLASS_REQ_INVALID_TEST_SV
