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

// Description: USB HS device resume test firmware. Boots HS device, handles EP0, detects suspend (DSUS) and resume (DSUS_C clear).

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Each poll iteration takes ~51 ns at MCU clock rate. The RTL suspend timer
// (usb_timers_sf SUSPEND_TIME=1) requires 2 Clk1kHz ticks = 2 ms minimum
// before DSUS asserts. 10000 iters (~0.5 ms) timed out before DSUS asserted.
// 100000 iters provides ~5 ms headroom for both suspend and resume detection.
#define USB_POLL_TIMEOUT 100000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t dsus_seen = 0;

    VPRINTF(LOW, "MCU: hs_dev_resume test\n");
    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // lsu_write_32(SOC_USBHSD_INTEN, lsu_read_32(SOC_USBHSD_INTEN) | 0xFFFFFFFF);
    lsu_write_32(SOC_USBHSD_INTEN,
    lsu_read_32(SOC_USBHSD_INTEN) | USBHSD_INTEN_FRAME_INT_EN_MASK);
    // lsu_write_32(SOC_USBHSD_INTSETSTAT, lsu_read_32(SOC_USBHSD_INTSETSTAT) | 0xFFFFFFFF);

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        // usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            // reg_data was sampled at the top of the loop (before the DEV_INT
            // W1C write below), so DSUS_C is still readable here.
            // usb_handle_bus_reset() also reads DRES_C before the W1C write.
            // Writing DEV_INT W1C to INTSTAT has a hardware side effect of
            // clearing all change-detect bits (DRES_C, DSUS_C, DCON_C) in
            // DEVCMDSTAT.  Do NOT re-read DEVCMDSTAT before the DSUS_C check
            // or the bit will appear clear.
            // usb_handle_bus_reset();
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
            // Require DSUS (steady-state suspended bit) to also be set when
            // DSUS_C fires. During HS bus reset / chirp the controller can
            // assert DSUS_C transiently while DSUS=0 (device is resetting, not
            // truly suspended). Accepting that transient causes a false PASSED
            // before the real suspend/resume phase even begins.
            if (!dsus_seen && (reg_data & USBHSD_DEVCMDSTAT_DSUS_C_MASK)
                           && (reg_data & USBHSD_DEVCMDSTAT_DSUS_MASK)) {
                // Suspend detected: clear DSUS_C (W1C) and record.
                lsu_write_32(SOC_USBHSD_DEVCMDSTAT,
                    lsu_read_32(SOC_USBHSD_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DSUS_C_MASK);
                dsus_seen = 1;
                VPRINTF(LOW, "MCU: hs_dev_resume suspend detected DEVCMDSTAT=0x%x\n", reg_data);
            } else if (dsus_seen) {
                // Re-read DEVCMDSTAT for the DSUS (current-state) bit, which is
                // not a change-detect bit and is safe to read after the W1C.
                reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                if (!(reg_data & USBHSD_DEVCMDSTAT_DSUS_MASK)) {
                    // Resume detected: DSUS cleared after suspend was seen.
                    VPRINTF(LOW, "USB HS device resume PASSED\r\n");
                    break;
                }
            }
        }
    }
    VPRINTF(LOW, "MCU: hs_dev_resume test complete\n");
    csr_write_mpmc_halt();
}
