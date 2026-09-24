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

`ifndef CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_TEST_SV
`define CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_TEST_SV

// Thin test wrapper for the mirrored-SETUP protocol-STALL and error-code
// matrix. Reuses the post-sync arbiter test base, which installs the arbiter
// checker. This test opts into mirrored-SETUP behavior
// before the environment creates that checker.
class caliptra_ss_usb_ocp_protocol_stall_matrix_test
    extends caliptra_ss_usb_ocp_arbiter_test_base;

    `uvm_component_utils(caliptra_ss_usb_ocp_protocol_stall_matrix_test)

    function new(
        string name = "caliptra_ss_usb_ocp_protocol_stall_matrix_test",
        uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        uvm_config_db#(bit)::set(
            null, "", "ocp_arbiter_mirrored_setup_mode", 1'b1);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(
            this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_protocol_stall_matrix_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_PROTOCOL_STALL_MATRIX_TEST_SV
