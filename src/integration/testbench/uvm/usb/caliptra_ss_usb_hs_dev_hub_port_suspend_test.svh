// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_TEST_SV

// =============================================================================
// USB HS hub downstream PORT_SUSPEND test.
//
// Usage: +UVM_TESTNAME=caliptra_ss_usb_hs_dev_hub_port_suspend_test
//
// This test needs no extra plusargs. In particular it does NOT enable
// caliptra_ss_usb_suspend_resume_checker: per-port suspend actuation is a
// documented and accepted deviation on this IP, so requiring a SuspendM edge
// here would either fail forever or force that shared checker to be relaxed for
// the global_suspend_L2 tests that rely on it as a hard pass/fail. See
// docs/usb_hub_port_suspend_not_wired_report.md.
//
// What this test does verify is the hub port status ladder including write-1-
// clear on C_PORT_SUSPEND, and that the downstream device still answers traffic
// after ClearPortFeature(PORT_SUSPEND). A PASS is therefore not evidence that
// any device suspended. The full reasoning is in the header of
// caliptra_ss_usb_hs_dev_hub_port_suspend_sequence.svh.
// =============================================================================

class caliptra_ss_usb_hs_dev_hub_port_suspend_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_dev_hub_port_suspend_test)

    function new(string name = "caliptra_ss_usb_hs_dev_hub_port_suspend_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_hub_port_suspend_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_TEST_SV
