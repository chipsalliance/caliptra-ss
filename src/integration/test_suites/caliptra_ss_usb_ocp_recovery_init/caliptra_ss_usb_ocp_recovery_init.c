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
//
// Caliptra Subsystem MCU firmware for the USB OCP Recovery bring-up path.
// Per plan D0.E, the MCU owns USB bring-up and class-interface advertisement,
// then reuses the existing RI_DOWNLOAD_FIRMWARE mailbox handoff so Caliptra
// core firmware can consume the recovery aperture. The USB event loop must
// keep running while streaming boot is active.

#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "mci.h"
#include "printf.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#define USB_EVENT_LOOP_DIAG_PERIOD 1000u
#include "usb.h"
#include "usb_ocp_recovery.h"

#define SS_GENERIC_FW_EXEC_CTRL_GO_MASK (1u << 2)
#define USB_EVENT_LOOP_SLICE_ITERS 1000u
// Smaller slice for the post-handoff FW_EXEC_CTRL wait loop: the MCU must notice
// Caliptra's completion signal (and report the pass) promptly, so it re-checks
// FW_EXEC_CTRL every ~few us instead of once per ~89us USB-servicing slice.
// (Using the large slice here makes end-of-test latency depend on slice/FW_EXEC
// alignment, 0..~89us.) Enumeration servicing is unaffected -- this loop runs
// post-enumeration, and USB is still serviced every iteration, just in smaller
// batches.
#define USB_FW_EXEC_POLL_SLICE_ITERS 32u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t main(void) {
    VPRINTF(LOW, "===============================\n");
    VPRINTF(LOW, "MCU: USB OCP recovery init test\n");
    VPRINTF(LOW, "===============================\n\n");

    boot_mcu();

    usb_dump_state("pre-boot");
    // Boot the USB device controller AND advertise the OCP recovery interface
    // in one step: the OCP composite config descriptor + recovery class-request
    // handler are installed as boot_usb_core's hooks, so any host VIP
    // enumeration that begins later already sees the recovery descriptor and
    // class endpoints (OCP Recovery v1.1 sec 8.5: recovery interface must be
    // advertised before any class request; otherwise GET_DESCRIPTOR(CONFIG) and
    // class requests would be STALLed).
    boot_usb_core(usb_ocp_recovery_get_config_descriptor,
                  usb_ocp_recovery_handle_class_request);
    usb_dump_state("post-boot");

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();

    // Per debug RCA (research/usb_setup_nak_root_cause.md): the Caliptra
    // mailbox does not become ready for ~250 us after USB bring-up, during
    // which the host VIP issues SETUPs that MUST be ACKed within
    // tend_to_end_delay (~2.3 us). Interleave the USB event loop while
    // waiting for the mailbox to avoid violating USB 2.0 sec 8.4.5.
    //
    // Defer the Caliptra handoff until USB enumeration is COMPLETE (device in
    // Configured state). Caliptra's recovery flow polls DEVICE_STATUS over the
    // AXI/recovery aperture; if it starts while enumeration is still running,
    // its DMA traffic contends with the USB controller's AXI accesses and can
    // stall enumeration (and itself). Recovery cannot become pending until
    // after the host has enumerated and pushed an image anyway (OCP Recovery
    // v1.1 sec 8.5: respond once USB enumeration is complete and the device is
    // Configured), so waiting for usb_is_configured() removes the contention
    // window without delaying any real work.
    VPRINTF(LOW, "MCU: Waiting for CPTRA mailbox and USB enumeration while servicing USB\n");
    while (!mcu_cptra_mb_ready_nb() || !usb_is_configured()) {
        usb_event_loop(USB_EVENT_LOOP_SLICE_ITERS);
    }
    VPRINTF(LOW, "MCU: CPTRA mailbox ready and USB configured; starting Caliptra streaming boot\n");
    caliptra_mailbox_send_ri_download_firmware();

    VPRINTF(LOW, "MCU: Entering USB event loop until SS_GENERIC_FW_EXEC_CTRL_0[2] is asserted\n");
    while ((lsu_read_32(SOC_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0)
            & SS_GENERIC_FW_EXEC_CTRL_GO_MASK) == 0u) {
        usb_event_loop(USB_FW_EXEC_POLL_SLICE_ITERS);
    }

    usb_dump_state("streaming-boot-complete");
    VPRINTF(LOW, "MCU: Streaming boot complete; reporting pass to the testbench\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while(1);
}
