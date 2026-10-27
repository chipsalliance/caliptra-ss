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

`ifndef CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV
`define CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV

// =============================================================================
// USB device (USBD) basic connection sequence.

// Sequence flow:
//   1. Wait for FS host link to reach ENABLED (device D+ pullup detected,
//      reset/chirp completed, link in FS ENABLED state).
//   2. Start SOF generation to keep the FS link alive.
//   3. Hold an observation window for MCU firmware to confirm connection
//      and log the result.
// =============================================================================

// Extends caliptra_ss_usb_base_sequence (see caliptra_ss_usb_base_sequence.svh)
// and uses its pre_start()/post_start() objection handling plus the shared
// resolve_shared_status(), wait_for_link_enabled() and start_sof_generation()
// helpers. This sequence issues no control transfers, so do_control_xfer()/
// wait_xfer_done() are unused here.
class caliptra_ss_usb_usbd_conn_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_usbd_conn_sequence)

    int unsigned obs_window_us = 100;

    function new(string name = "caliptra_ss_usb_usbd_conn_sequence");
        super.new(name);
    endfunction

    virtual task body();

        svt_usb_status shared_status;

        shared_status = resolve_shared_status();

        // Step 1: Wait for FS link ENABLED (device D+ pullup detected, reset
        // and chirp completed). Untimed wait - handled by the base class.
        wait_for_link_enabled(shared_status, "FS host link");

        // Step 2: Start SOF generation to keep the FS link alive.
        start_sof_generation();

        // Step 3: Observation window for MCU firmware to log connection result.
        `uvm_info("USB_USBD_CONN_SEQ",
            $sformatf("Holding observation window for %0d us.", obs_window_us), UVM_LOW)
        #(obs_window_us * 1us);

        `uvm_info("USB_USBD_CONN_SEQ",
            "USB device basic connection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV
