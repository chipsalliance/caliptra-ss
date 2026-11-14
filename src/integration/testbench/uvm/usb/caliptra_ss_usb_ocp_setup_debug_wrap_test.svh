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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_DEBUG_WRAP_TEST_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_DEBUG_WRAP_TEST_SVH
class caliptra_ss_usb_ocp_setup_debug_wrap_test
    extends caliptra_ss_usb_ocp_setup_supersession_test;
    `uvm_component_utils(caliptra_ss_usb_ocp_setup_debug_wrap_test)

    function new(string name = "caliptra_ss_usb_ocp_setup_debug_wrap_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mixed_checker.mode = "DEBUG_WRAP";
        uvm_config_db#(bit)::set(
            null, "", "usb_setup_debug_wrap_stimulus_completed", 0);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_ocp_setup_debug_wrap_sequence::type_id::get());
    endfunction

    virtual function void check_phase(uvm_phase phase);
        bit completed;
        super.check_phase(phase);
        if (!uvm_config_db#(bit)::get(
            null, "", "usb_setup_debug_wrap_stimulus_completed", completed) ||
            (completed !== 1'b1))
            `uvm_error("SETUP_DEBUG_WRAP", "The complete directed wrap stimulus/check campaign did not retire")
    endfunction
endclass
`endif
