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

`ifndef GUARD_CALIPTRA_SS_USB_BASE_TEST_SV
`define GUARD_CALIPTRA_SS_USB_BASE_TEST_SV

`include "caliptra_ss_usb_env.sv"

// =============================================================================
// Base test for USB VIP host-only environment in Caliptra Subsystem.
//
// This test:
// - Creates the caliptra_ss_usb_env with a single VIP host agent
// - Configures the host for USB 2.0 HS UTMI mode (TLM internal PHY)
// - Sets up directed transfers as the default sequence
// - The DUT (caliptra_ss_top) is the USB device
// =============================================================================
class caliptra_ss_usb_base_test extends uvm_test;

    `uvm_component_utils(caliptra_ss_usb_base_test)

    caliptra_ss_usb_env        env;
    caliptra_ss_usb_shared_cfg cfg;

    function new(string name = "caliptra_ss_usb_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void end_of_elaboration_phase(uvm_phase phase);
    extern virtual function void final_phase(uvm_phase phase);

endclass

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    // Create and configure
    cfg = caliptra_ss_usb_shared_cfg::type_id::create("cfg", this);
    cfg.setup_usb_20_utmi_host_defaults();

    // Pass configuration to env
    uvm_config_db#(caliptra_ss_usb_shared_cfg)::set(this, "env", "cfg", cfg);

    // Create environment
    env = caliptra_ss_usb_env::type_id::create("env", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    super.end_of_elaboration_phase(phase);
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...", UVM_LOW)
    super.final_phase(phase);

    svr = uvm_report_server::get_server();
    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) > 0)
        `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_LOW)
    else
        `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_LOW)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
endfunction

`endif // GUARD_CALIPTRA_SS_USB_BASE_TEST_SV
