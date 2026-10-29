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
// This test exercises the single-host-agent topology:
//   - host_cfg models the USB 2.0 HS host stack.
//   - remote_cfg models the device PHY connected to the DUT UTMI+ interface.
//   - The default sequence waits for HS link-up, then runs a small set of
//     CONTROL transfers to validate enumeration-style communication.
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

        // Start the directed USB init sequence on the host virtual sequencer.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_init_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_BASIC_UTMI_TEST_SV
