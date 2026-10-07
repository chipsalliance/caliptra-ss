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

`ifndef CALIPTRA_SS_USB_DEV1_RAM_RW_TEST_SV
`define CALIPTRA_SS_USB_DEV1_RAM_RW_TEST_SV

// =============================================================================
// USB device-controller RAM RW test - USBDC1 (dev1) variant.
//
// dev1 counterpart of caliptra_ss_usb_dev_ram_rw_test. Standalone RAM read/write
// access test for the DMA/SRAM window of the second embedded USB device
// controller (USBDC1 / dev1). All RAM checking is performed by the MCU firmware
// (caliptra_ss_usb_dev1_ram_rw.c, built with -DUSB_DEV_SEL=1), which exercises
// the USBDC1 RAM window (0x2001_0100) directly over the MCU LSU AXI master:
//   - Phase 1: deterministic per-word pattern sweep with read-back compare.
//   - Phase 2: random word/value walk with deferred read-back compare.
//
// This test does NOT bring up the USB link and drives no USB traffic. It leaves
// the base-test host cfg untouched (no high_speed_capable override) and simply
// installs caliptra_ss_usb_mem_rw_sequence as the main_phase default
// sequence. That sequence just holds the phase objection open long enough for
// the firmware to finish and report its verdict.
//
// Verdict (two judges):
//   - firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dev1_ram_rw_test
// =============================================================================
class caliptra_ss_usb_dev1_ram_rw_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_dev1_ram_rw_test)

    function new(string name = "caliptra_ss_usb_dev1_ram_rw_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        caliptra_ss_usb_mem_rw_sequence mem_rw_seq;

        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Install the shared standalone access sequence as the default on the
        // host virtual sequencer so it runs automatically during main_phase. No
        // host cfg override: the link is intentionally left un-brought-up.
        // Window sizing: MCU boot plus the RAM sweep (960 words, ~2k AXI
        // accesses) plus 5 random-walk loops of 256 accesses each (~2.5k more);
        // 5000 us gives generous margin before the coarse MCU-halt timeout
        // closes the run. The sequence OBJECT is registered rather than its
        // type wrapper so this per-test window can be set as a field.
        mem_rw_seq = caliptra_ss_usb_mem_rw_sequence::type_id::create("mem_rw_seq");
        mem_rw_seq.run_window_us = 5000;
        mem_rw_seq.window_desc   = "the dev1 RAM sweep and random walks";

        uvm_config_db#(uvm_sequence_base)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            mem_rw_seq);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DEV1_RAM_RW_TEST_SV
