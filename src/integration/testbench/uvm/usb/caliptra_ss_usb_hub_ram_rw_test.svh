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

`ifndef CALIPTRA_SS_USB_HUB_RAM_RW_TEST_SV
`define CALIPTRA_SS_USB_HUB_RAM_RW_TEST_SV

// =============================================================================
// USB HUB descriptor-array (ep0_mem) RW / write-lock test.
//
// Standalone read/write and write-lock test for the embedded hub descriptor
// array (ep0_mem, 172 words at USB_HUB_REG_BASE_ADDR). All checking is
// performed by the MCU firmware (caliptra_ss_usb_hub_ram_rw.c), which exercises
// the array directly over the MCU LSU AXI master in three unlocked/locked
// loops:
//   - Unlocked (HUB_EN=1, HUB_CONNECT=0): every word (except word 15, the Hub
//     Control/Status register) is written a random value and must accept it.
//   - Locked (HUB_EN=1, HUB_CONNECT=1): the array is frozen, so every word
//     (except word 15) must preserve its captured baseline against random write
//     attempts.
//
// This test does NOT bring up the USB link and drives no USB traffic. Like the
// dev RAM/register tests it leaves the base-test host cfg untouched and simply
// installs caliptra_ss_usb_mem_rw_sequence as the main_phase default
// sequence, which holds the phase objection open long enough for the firmware
// to finish and report its verdict.
//
// Verdict (two judges):
//   - firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hub_ram_rw_test
// =============================================================================
class caliptra_ss_usb_hub_ram_rw_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hub_ram_rw_test)

    function new(string name = "caliptra_ss_usb_hub_ram_rw_test",
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
        // Window sizing: MCU boot plus 3 loops of (unlocked write pass + locked
        // capture/write/read-back pass) over the 172-word array, roughly
        // 3 x (171 + 3*171) ~= 2k AXI accesses; 5000 us gives generous margin
        // before the coarse MCU-halt timeout closes the run. The sequence
        // OBJECT is registered rather than its type wrapper so this per-test
        // window can be set as a field.
        mem_rw_seq = caliptra_ss_usb_mem_rw_sequence::type_id::create("mem_rw_seq");
        mem_rw_seq.run_window_us = 5000;
        mem_rw_seq.window_desc   = "the hub ep0_mem RW / write-lock loops";

        uvm_config_db#(uvm_sequence_base)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            mem_rw_seq);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HUB_RAM_RW_TEST_SV
