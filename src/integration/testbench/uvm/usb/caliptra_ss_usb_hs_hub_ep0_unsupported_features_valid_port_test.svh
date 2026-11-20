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

`ifndef CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_TEST_SV

// =============================================================================
// High-Speed hub EP0 unsupported-request / SETUP-pattern coverage test.
//
// Runs caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence: hub-only
// enumeration followed by nine EP0 control transfers that between them cover
// the GetConfiguration data mux, the GetStatus(Interface) leg, the ROM wLength
// clamp, the ep0_in_stall leg for an unsupported device feature, and the two
// SETUP-match walk-and-stall arcs of usb_ep0_handler.m.vhdl. See the sequence
// file header for the full line-by-line mapping and for the two documented
// coverage waivers.
//
// Control transfers only, so the default endpoint configuration of the base
// test (endpoint_cfg[0], EP0 CONTROL) is all that is needed: no extra endpoint
// anchor is declared here and no endpoint_cfg entry is re-stamped.
//
// The VIP needs no timing or timeout relaxation either. Every stalled transfer
// below is terminated by a real STALL handshake from the DUT, which the VIP
// reports as svt_sequence_item::ABORTED, so nothing ever runs into a device
// response timeout and no uvm_report_catcher is required - unlike the
// unsupported-ENDPOINT family, where the DUT stays silent.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_test
// =============================================================================

class caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_test)

    function new(string name = "caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_test",
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
            caliptra_ss_usb_hs_hub_ep0_unsupported_features_valid_port_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_EP0_UNSUPPORTED_FEATURES_VALID_PORT_TEST_SV
