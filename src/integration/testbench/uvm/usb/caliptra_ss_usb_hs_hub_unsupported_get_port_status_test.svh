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

`ifndef CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_TEST_SV

// =============================================================================
// High-Speed hub GetPortStatus on an UNSUPPORTED port test.
//
// Runs caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence: a hub-only
// enumeration followed by fourteen EP0 class requests - GetPortStatus on three
// illegal port numbers (one rejected by the hub decoder, two by the EP0 SETUP
// table), GetHubStatus as the discriminator, the hub-itself Clear/SetHubFeature
// no-op arms, an accepted no-op port feature, ClearPortFeature on a bad port,
// and the two L1 branch holes (ClearPortFeature(PORT_L1) on a port not in L1,
// SetAndTestPortFeature(PORT_L1) on an enabled port with LPM unsupported).
//
// Like the other hub class-request tests only the speed is set here: the
// sequence is EP0 control transfers only, every rejected request ends on a
// real STALL handshake, and nothing times out, so no endpoint model, NAK
// budget or uvm_report_catcher is needed and UVM_ERROR must be 0.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_unsupported_get_port_status_test
// =============================================================================

class caliptra_ss_usb_hs_hub_unsupported_get_port_status_test
    extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_unsupported_get_port_status_test)

    function new(string name = "caliptra_ss_usb_hs_hub_unsupported_get_port_status_test",
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
            caliptra_ss_usb_hs_hub_unsupported_get_port_status_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_UNSUPPORTED_GET_PORT_STATUS_TEST_SV
