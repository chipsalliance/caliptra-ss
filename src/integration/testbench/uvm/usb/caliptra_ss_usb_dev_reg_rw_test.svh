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

`ifndef CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV
`define CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV

// =============================================================================
// USB device-controller register RW test.
//
// Standalone register read/write access test for BOTH embedded USB device
// controllers (USBDC0 / dev0 and USBDC1 / dev1) in a single run. All register
// checking is performed by the MCU firmware (caliptra_ss_usb_dev_reg_rw.c),
// which walks a shared register-disposition table over both banks directly
// over the MCU LSU AXI master:
//   - RW registers: masked random write / read-back compare.
//   - RO registers: three distinct writes, proving the RO bits are immutable.
//
// This test does NOT bring up the USB link and drives no USB traffic. Unlike
// caliptra_ss_usb_fs_clock_test it therefore leaves the base-test host cfg
// untouched (no high_speed_capable override) and simply installs
// caliptra_ss_usb_dev_reg_rw_sequence as the main_phase default sequence. That
// sequence just holds the phase objection open long enough for the firmware to
// finish and report its verdict.
//
// Verdict (two judges):
//   - firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dev_reg_rw_test
// =============================================================================
class caliptra_ss_usb_dev_reg_rw_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_dev_reg_rw_test)

    function new(string name = "caliptra_ss_usb_dev_reg_rw_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Install the standalone register-RW sequence as the default on the
        // host virtual sequencer so it runs automatically during main_phase.
        // No host cfg override: the link is intentionally left un-brought-up.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            caliptra_ss_usb_dev_reg_rw_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV
