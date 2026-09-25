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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT              2000000u
#define USB_SKIP_POLL_TIMEOUT         100000u
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u
#define USB_SRAM_EP1_OUT_BUF_OFFSET   0x200u
#define USB_EP1_OUT_PHYSICAL_INDEX    2u
#define USB_EP1_OUT_SKIP_MASK         (1u << USB_EP1_OUT_PHYSICAL_INDEX)
#define USB_RECOVERY_BYTES            16u
#define USB_RECOVERY_SENTINEL         0xDEDEDEDEu

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static uint32_t usb_ep1_out_entry(uint32_t nbytes) {
    return USB_EP_ENTRY_ACTIVE
         | USB_EP_ENTRY_NBYTES(nbytes)
         | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_BUF_OFFSET);
}

static void fail_test(const char *message) {
    VPRINTF(FATAL, "MCU: FAIL - %s\n", message);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void run_skip_update_check(void) {
    const uint32_t initial_entry = usb_ep1_out_entry(USB_RECOVERY_BYTES);
    uint32_t entry;
    uint32_t intstat;
    uint32_t poll_count;

    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                 DEV0_CSR_INTSTAT_EP1OUT_MASK);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, initial_entry);
    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_EPSKIP, USB_EP1_OUT_SKIP_MASK);

    for (poll_count = 0; poll_count < USB_SKIP_POLL_TIMEOUT; poll_count++) {
        if ((lsu_read_32(SOC_USB_COMBO_DEV0_CSR_EPSKIP)
             & USB_EP1_OUT_SKIP_MASK) == 0u)
            break;
    }
    if (poll_count == USB_SKIP_POLL_TIMEOUT)
        fail_test("EPSKIP[2] did not clear");

    entry = lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
    if (entry != (initial_entry & ~USB_EP_ENTRY_ACTIVE)) {
        VPRINTF(FATAL, "MCU: skip writeback mismatch: got 0x%x expected 0x%x\n",
                entry, initial_entry & ~USB_EP_ENTRY_ACTIVE);
        fail_test("skip writeback did not only clear Active");
    }

    intstat = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);
    if ((intstat & DEV0_CSR_INTSTAT_EP1OUT_MASK) == 0u)
        fail_test("skip update did not assert EP1OUT interrupt");

    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                 DEV0_CSR_INTSTAT_EP1OUT_MASK);
    VPRINTF(LOW, "MCU: PASS - EPSKIP[2] cleared Active and asserted EP1OUT\n");
}

static void arm_recovery_transfer(void) {
    for (uint32_t offset = 0; offset < USB_RECOVERY_BYTES; offset += 4u) {
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET + offset,
                     USB_RECOVERY_SENTINEL);
    }
    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET,
                 usb_ep1_out_entry(USB_RECOVERY_BYTES));
    VPRINTF(LOW, "MCU: EP1 OUT armed for post-skip recovery transfer\n");
}

static void verify_recovery_transfer(void) {
    uint32_t entry =
        lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
    uint32_t residual = (entry >> 11) & 0x7FFFu;

    if (residual != 0u) {
        VPRINTF(FATAL, "MCU: recovery residual=%d expected=0\n", residual);
        fail_test("recovery transfer length mismatch");
    }

    for (uint32_t offset = 0; offset < USB_RECOVERY_BYTES; offset += 4u) {
        uint32_t expected = 0xA3A2A1A0u + (0x04040404u * (offset / 4u));
        uint32_t actual =
            lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP1_OUT_BUF_OFFSET + offset);
        if (actual != expected) {
            VPRINTF(FATAL,
                    "MCU: recovery data mismatch at 0x%x: got 0x%x expected 0x%x\n",
                    offset, actual, expected);
            fail_test("recovery payload mismatch");
        }
    }

    VPRINTF(LOW, "MCU: PASS - post-skip EP1 OUT recovery transfer\n");
}

void main(void) {
    uint32_t poll_count;
    uint32_t setup_count = 0;
    bool skip_test_started = false;
    bool skip_test_pending = false;
    bool recovery_armed = false;
    bool recovery_done = false;

    VPRINTF(LOW, "=================\nMCU: USB HS device skip-state test\n=================\n\n");

    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTEN,
        lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTEN)
        | DEV0_CSR_INTSTAT_EP1OUT_MASK);

    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !recovery_done;
         poll_count++) {
        uint32_t devcmdstat;
        uint32_t intstat;

        usb_handle_bus_reset();
        devcmdstat = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
        intstat = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (intstat & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            if (devcmdstat & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                setup_count = 0;
                skip_test_started = false;
                skip_test_pending = false;
                recovery_armed = false;
            }
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                         DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                         DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (devcmdstat & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                setup_count++;
                if (setup_count == 3u)
                    skip_test_pending = true;
            }
        }

        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                         DEV0_CSR_INTSTAT_EP0IN_MASK);
            if (skip_test_pending && !skip_test_started) {
                skip_test_pending = false;
                skip_test_started = true;
                run_skip_update_check();
                arm_recovery_transfer();
                recovery_armed = true;
            }
        }

        if (recovery_armed && (intstat & DEV0_CSR_INTSTAT_EP1OUT_MASK)) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT,
                         DEV0_CSR_INTSTAT_EP1OUT_MASK);
            verify_recovery_transfer();
            recovery_done = true;
        }
    }

    if (!recovery_done)
        fail_test("timed out waiting for post-skip recovery transfer");

    VPRINTF(LOW, "MCU: USB HS device skip-state test PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    csr_write_mpmc_halt();
}
