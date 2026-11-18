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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_ADDRESS_HANDOFF_TEST_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_ADDRESS_HANDOFF_TEST_SVH

class caliptra_ss_usb_ocp_setup_address_handoff_test
    extends caliptra_ss_usb_ocp_setup_supersession_test;
    `uvm_component_utils(caliptra_ss_usb_ocp_setup_address_handoff_test)

    function new(string name = "caliptra_ss_usb_ocp_setup_address_handoff_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        svt_usb_protocol::type_id::set_inst_override(
            caliptra_ss_usb_stale_publication_protocol::get_type(),
            {get_full_name(), ".env.host_agent.prot"});
        super.build_phase(phase);
        mixed_checker.mode = "ADDRESS";
        uvm_config_db#(bit)::set(null, "", "usb_setup_address_handoff_stimulus_completed", 0);
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_ocp_setup_address_handoff_sequence::type_id::get());
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        caliptra_ss_usb_stale_publication_protocol address_gate;
        super.connect_phase(phase);
        if (!$cast(address_gate, env.host_agent.prot)) begin
            `uvm_error("SETUP_ADDRESS_CHECK", "Host pre-token protocol override missing")
            `uvm_fatal("SETUP_ADDRESS_CHECK", "No qualified interruption boundary")
        end
        uvm_config_db#(caliptra_ss_usb_stale_publication_protocol)::set(
            null, "*", "usb_stale_publication_gate", address_gate);
    endfunction

    virtual function void check_phase(uvm_phase phase);
        bit completed;
        super.check_phase(phase);
        if (!uvm_config_db#(bit)::get(null, "", "usb_setup_address_handoff_stimulus_completed", completed) ||
            (completed !== 1'b1))
            `uvm_error("SETUP_ADDRESS_INCOMPLETE", "Required Address-state handoff inventory did not retire")
    endfunction
endclass
`endif
