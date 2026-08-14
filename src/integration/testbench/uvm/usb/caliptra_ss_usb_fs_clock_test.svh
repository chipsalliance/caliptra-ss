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

`ifndef CALIPTRA_SS_USB_FS_CLOCK_TEST_SV
`define CALIPTRA_SS_USB_FS_CLOCK_TEST_SV

// =============================================================================
// USB Full-Speed clock test.
// Verifies that the USB clock path is active and toggling at the expected
// frequency after the USB device controller is brought up in full-speed mode.
// Differences from caliptra_ss_usb_basic_utmi_test:
//   - The VIP host cfg is reconfigured with high_speed_capable=0 so the VIP
//     remote-device model does not offer the HS chirp. The link therefore
//     attaches and enumerates at full speed (12 Mbit/s), exercising the USB FS
//     clock domain.
//   - The active sequence is caliptra_ss_usb_fs_clock_sequence (no control
//     transfers; just link-up + SOF + observation window).
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_clock_test
// =============================================================================
class caliptra_ss_usb_fs_clock_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_clock_test)

    function new(string name = "caliptra_ss_usb_fs_clock_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Override the host cfg to disable HS negotiation so the VIP and DUT
        // link at full speed. high_speed_capable=0 prevents the VIP from
        // driving the HS chirp during bus reset, causing both sides to settle
        // at FS (12 Mbit/s). The DUT USB clock domain is then exercised at FS.
        //
        // NOTE: cfg is already created and set in caliptra_ss_usb_base_test
        // build_phase (called via super.build_phase above). We only need to
        // clear the HS capability bit on the already-created host_cfg object.
        cfg.host_cfg.local_host_cfg.high_speed_capable = 0;
        `uvm_info("build_phase",
            "FS clock test: high_speed_capable overridden to 0 (full-speed).",
            UVM_LOW)

        // Set the FS clock sequence as the default on the host virtual
        // sequencer so it runs automatically during main_phase.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_fs_clock_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_CLOCK_TEST_SV
