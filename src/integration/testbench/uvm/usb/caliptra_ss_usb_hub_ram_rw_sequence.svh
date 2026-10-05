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

`ifndef CALIPTRA_SS_USB_HUB_RAM_RW_SEQUENCE_SV
`define CALIPTRA_SS_USB_HUB_RAM_RW_SEQUENCE_SV

// =============================================================================
// USB HUB descriptor-array (ep0_mem) RW / write-lock sequence.
//
// Companion sequence for the caliptra_ss_usb_hub_ram_rw test. This is a
// STANDALONE memory-access test: all checking is done by the MCU firmware
// (caliptra_ss_usb_hub_ram_rw.c) directly over the MCU LSU AXI master against
// the hub ep0_mem array at USB_HUB_REG_BASE_ADDR. The USB link is never brought
// up and no USB traffic is driven, so unlike the enumeration-based sequences
// this one does NOT:
//   - wait for the host link to reach ENABLED (there is no device to attach),
//   - start SOF generation,
//   - issue any control/data transfers.
//
// Its only job is to keep the UVM run/main phase objection raised long enough
// for the firmware to run three unlocked/locked loops over the 172-word hub
// descriptor array and halt. The pass/fail verdict comes from two judges
// evaluated elsewhere:
//   - the firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - the UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// pre_start()/post_start() (inherited from caliptra_ss_usb_base_sequence) raise
// and drop the starting phase's objection, so simply holding this body() open
// keeps the phase from ending before the firmware finishes.
// =============================================================================
class caliptra_ss_usb_hub_ram_rw_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hub_ram_rw_sequence)

    // Observation window held open so the firmware has time to boot the MCU and
    // run 3 loops of (unlocked write pass + locked capture/write/read-back pass)
    // over the 172-word array. That is roughly 3 x (171 + 3*171) ~= 2k AXI
    // accesses; 5000 us gives generous margin before the coarse MCU-halt timeout
    // closes the run.
    int unsigned run_window_us = 5000;

    function new(string name = "caliptra_ss_usb_hub_ram_rw_sequence");
        super.new(name);
    endfunction


    virtual task body();
        `uvm_info("USB_HUB_RAM_RW_SEQ",
            $sformatf({"Standalone hub RAM test: holding run phase for %0d us ",
                       "while MCU firmware exercises the hub ep0_mem array."},
                      run_window_us),
            UVM_LOW)

        #(run_window_us * 1us);

        `uvm_info("USB_HUB_RAM_RW_SEQ",
            "Run window complete; MCU firmware verdict is authoritative.",
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HUB_RAM_RW_SEQUENCE_SV
