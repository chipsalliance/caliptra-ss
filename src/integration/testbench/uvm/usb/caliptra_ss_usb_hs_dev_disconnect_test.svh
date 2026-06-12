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

`ifndef CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV

// =============================================================================
// USB High-Speed device disconnect/reconnect test.
// DUT is the USB device controller. VIP host connects at HS, then
// powers off the port to disconnect, waits, then reconnects and verifies
// the HS link is re-established.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_disconnect_test
// =============================================================================
class caliptra_ss_usb_hs_dev_disconnect_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_disconnect_test)

    function new(string name = "caliptra_ss_usb_hs_dev_disconnect_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode defaults (high_speed_capable=1).
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_disconnect_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_DISCONNECT_TEST_SV
