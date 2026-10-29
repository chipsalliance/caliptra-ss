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

`ifndef CALIPTRA_SS_USB_HS_CONN_TEST_SV
`define CALIPTRA_SS_USB_HS_CONN_TEST_SV

// =============================================================================
// USB High-Speed connection test.

// This test uses the default SVT VIP configuration (high_speed_capable=1)
// so the VIP host performs HS chirp and the link attaches at HS (480 Mbit/s).
// The sequence waits for ENABLED state then holds an observation window.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_conn_test
// =============================================================================
class caliptra_ss_usb_hs_conn_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_conn_test)

    function new(string name = "caliptra_ss_usb_hs_conn_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable=1 (default) so VIP performs chirp.
        // No additional cfg overrides needed for a basic HS connection test.

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_conn_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_CONN_TEST_SV
