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

`ifndef CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_TEST_SV

// =============================================================================
// High-Speed hub-bypass enumeration test (device0 directly on the bus).
//
// Runs caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence. The firmware leaves
// HUB_CTRL.HUB_EN clear, so the compound structure muxes USBDC0 straight onto
// the upstream link and the hub is not a bus participant. See the sequence
// header for the four RTL muxes this exercises.
//
// No VIP configuration delta is required for the bypass topology. The host
// agent sees one High-Speed device on the bus, which is the simplest case the
// VIP supports - simpler than the hub-mode tests, which need the hub and its
// downstream device both modelled. Only the HS speed settings are pinned here,
// matching the other HS tests, and the default endpoint configuration
// (endpoint_cfg[0], EP0 CONTROL) is sufficient because this test issues
// control transfers only.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_hub_bypass_enum_test
// =============================================================================

class caliptra_ss_usb_hs_dev_hub_bypass_enum_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_dev_hub_bypass_enum_test)

    function new(string name = "caliptra_ss_usb_hs_dev_hub_bypass_enum_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default 1 so the VIP drives
        // the chirp handshake. In bypass topology the chirp is answered by
        // device0 through the sync_busreset leg of upd_dev0_portreset rather
        // than through the hub's per-port reset, which is one of the things
        // this test is here to prove works.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HUB_BYPASS_ENUM_TEST_SV
