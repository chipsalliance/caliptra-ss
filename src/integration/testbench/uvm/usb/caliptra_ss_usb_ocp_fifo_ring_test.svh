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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_RING_TEST_SV
`define CALIPTRA_SS_USB_OCP_FIFO_RING_TEST_SV

// =============================================================================
// caliptra_ss_usb_ocp_fifo_ring_test
//
// Focused INDIRECT_FIFO protocol test. Reuses the OCP scoreboard environment
// and drives the directed 64-DWORD fill / rejected 65th push / wrap-drain
// sequence from caliptra_ss_usb_ocp_fifo_ring_sequence.
// =============================================================================
class caliptra_ss_usb_ocp_fifo_ring_test extends caliptra_ss_usb_basic_utmi_test;

    `uvm_component_utils(caliptra_ss_usb_ocp_fifo_ring_test)

    function new(string name = "caliptra_ss_usb_ocp_fifo_ring_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_type_override_by_type(
            caliptra_ss_usb_env::get_type(),
            caliptra_ss_usb_ocp_recovery_env::get_type());

        super.build_phase(phase);

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_ocp_fifo_ring_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_RING_TEST_SV
