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

`ifndef CALIPTRA_SS_USB_MEM_RW_SEQUENCE_SV
`define CALIPTRA_SS_USB_MEM_RW_SEQUENCE_SV

// =============================================================================
// Shared observation-window sequence for the standalone USB register / RAM
// access tests.
//
// Single companion sequence used by every STANDALONE access test where all the
// checking is done by the MCU firmware directly over the MCU LSU AXI master:
//
//   caliptra_ss_usb_dev_reg_rw_test    (both device register banks)
//   caliptra_ss_usb_dev_ram_rw_test    (USBDC0 DMA/SRAM window)
//   caliptra_ss_usb_dev1_ram_rw_test   (USBDC1 DMA/SRAM window, 0x2001_0100)
//   caliptra_ss_usb_hub_ram_rw_test    (hub ep0_mem descriptor array)
//
// Those tests never bring the USB link up and drive no USB traffic, so unlike
// the enumeration-based sequences this one does NOT:
//   - wait for the host link to reach ENABLED (there is no device to attach),
//   - start SOF generation,
//   - issue any control/data transfers.
//
// Its only job is to keep the UVM run/main phase objection raised long enough
// for the firmware to finish its access loops and halt. The pass/fail verdict
// comes from two judges evaluated elsewhere:
//   - the firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - the UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// pre_start()/post_start() (inherited from caliptra_ss_usb_base_sequence) raise
// and drop the starting phase's objection, so simply holding this body() open
// keeps the phase from ending before the firmware finishes.
//
// The per-test wait time is the only thing that differs between those tests, so
// it is a field here (run_window_us) rather than a separate sequence class per
// test. The test builds an instance, assigns run_window_us (and optionally
// window_desc for the log line) and registers the OBJECT - not the type wrapper
// - as the main_phase default_sequence:
//
//   seq = caliptra_ss_usb_mem_rw_sequence::type_id::create("mem_rw_seq");
//   seq.run_window_us = 1500;
//   seq.window_desc   = "both device register bank checks";
//   uvm_config_db#(uvm_sequence_base)::set(this,
//       "env.host_agent.virt_sequencer.main_phase", "default_sequence", seq);
//
// Sizing guidance for run_window_us: the dominant cost is MCU boot, plus the
// firmware access loops at roughly a few hundred nanoseconds per AXI access.
// A short register walk needs ~1500 us; a full RAM sweep plus random walks
// (a few thousand accesses) needs ~5000 us. The window must still close before
// the coarse MCU-halt timeout ends the run.
// =============================================================================
class caliptra_ss_usb_mem_rw_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_mem_rw_sequence)

    // Observation window, in microseconds, held open so the MCU firmware has
    // time to boot, run its register/RAM access checks and halt. Set by the
    // test; the default suits the RAM tests.
    int unsigned run_window_us = 5000;

    // Short human-readable description of what the firmware is doing during
    // the window. Used in the info log only; it has no functional effect.
    string window_desc = "register/RAM accesses";

    function new(string name = "caliptra_ss_usb_mem_rw_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("USB_MEM_RW_SEQ",
            $sformatf({"Standalone access test: holding run phase for %0d us ",
                       "while MCU firmware performs %s."},
                      run_window_us, window_desc),
            UVM_LOW)

        #(run_window_us * 1us);

        `uvm_info("USB_MEM_RW_SEQ",
            "Run window complete; MCU firmware verdict is authoritative.",
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_MEM_RW_SEQUENCE_SV
