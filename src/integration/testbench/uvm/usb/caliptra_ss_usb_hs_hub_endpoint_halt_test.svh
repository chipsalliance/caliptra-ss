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

`ifndef CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_TEST_SV

// =============================================================================
// High-Speed hub ENDPOINT_HALT round trip test.
//
// Runs caliptra_ss_usb_hs_hub_endpoint_halt_sequence: hub-only enumeration,
// then GET_STATUS / SET_FEATURE / GET_STATUS / CLEAR_FEATURE / GET_STATUS on
// the hub interrupt IN endpoint (wIndex = 0x0081). The scenario uses control
// transfers only, so the default endpoint configuration of the base test
// (endpoint_cfg[0], EP0 CONTROL) is all that is needed and no extra endpoint
// anchor has to be declared here.
//
// The hub exposes exactly one non-control endpoint, endpoint 1 IN
// (usb_ep_config_hub_pkg.p.vhdl, device 0: EPNB=1, EPDIR=EP_IN, NON_ISO), which
// is why wIndex = 0x0081 is the only meaningful endpoint index. No data traffic
// is driven to it: the Halt state is observed through the GET_STATUS data
// stage, which reads usb_ep_config_handler.reg_ep_stall back through
// epconfig_stall.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_endpoint_halt_test
// =============================================================================

class caliptra_ss_usb_hs_hub_endpoint_halt_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_endpoint_halt_test)

    function new(string name = "caliptra_ss_usb_hs_hub_endpoint_halt_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable=1 (default) so the VIP performs chirp.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_hub_endpoint_halt_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_TEST_SV
