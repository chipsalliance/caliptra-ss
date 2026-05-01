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

`ifndef CALIPTRA_SS_USB_BASIC_UTMI_TEST_SV
`define CALIPTRA_SS_USB_BASIC_UTMI_TEST_SV

// =============================================================================
// Basic USB 2.0 UTMI test for Caliptra Subsystem.
//
// This test exercises a basic init sequence over the UTMI interface:
//   - VIP host agent configured for USB 2.0 HS with UTMI MAC interface
//   - DUT (caliptra_ss_top) acts as the USB device on UTMI MAC side
//   - Runs a short directed sequence: CONTROL transfers (GET_DESCRIPTOR,
//     SET_ADDRESS) to verify basic USB enumeration-style communication
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_basic_utmi_test
// =============================================================================
class caliptra_ss_usb_basic_utmi_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_basic_utmi_test)

    function new(string name = "caliptra_ss_usb_basic_utmi_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        cfg.host_cfg.utmi_data_width = 8;

        // Use scaled-down timers for faster simulation
        void'(cfg.host_cfg.set_timer_values(
            svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));

        // Set default sequence: directed CONTROL transfers for basic init
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_init_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_BASIC_UTMI_TEST_SV
