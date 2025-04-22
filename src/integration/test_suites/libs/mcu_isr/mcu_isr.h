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
// ---------------------------------------------------------------------
// File: mcu_isr.h
// Description:
//     Provides function declarations for use by external test files, so
//     that the ISR functionality may behave like a library.
//     TODO:
//     This header file includes inline function definitions for event and
//     test specific interrupt service behavior, so it should be copied and
//     modified for each test.
// ---------------------------------------------------------------------

#ifndef MCU_ISR_H
    #define MCU_ISR_H

#define EN_ISR_PRINTS 1

#include "caliptra_ss_defines.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"

/* --------------- symbols/typedefs --------------- */
typedef struct {
    uint32_t mci_error0;
    uint32_t mci_error1;
    uint32_t mci_notif0;
    uint32_t mci_notif1;
    uint32_t i3c; // FIXME sub-banks of vectors
} mcu_intr_received_s;
extern volatile mcu_intr_received_s mcu_intr_rcv;

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//

// Performs all the CSR setup to configure and enable vectored external interrupts
void init_interrupts(void);

// These inline functions are used to insert event-specific functionality into the
// otherwise generic ISR that gets laid down by the parameterized macro "nonstd_veer_isr"
inline void service_mci_intr() {
    uint32_t sts_err, sts_ntf;
    uint32_t which = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R);
    switch (which) {
        case MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK:
            sts_err = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R);
            /* Write 1 to Clear the pending interrupt */
            // TODO should handle on a per-intr basis
            lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, sts_err);
            mcu_intr_rcv.mci_error0 |= sts_err;
            break;
        case MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK:
            sts_err = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R);
            /* Write 1 to Clear the pending interrupt */
            // TODO should handle on a per-intr basis
            lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R, sts_err);
            mcu_intr_rcv.mci_error1 |= sts_err;
            break;
        default:
            VPRINTF(FATAL, "Bad glbl err intr 0x%x\n", which);
            SEND_STDOUT_CTRL(0x1);
            while(1);
    }
    which = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R);
    switch (which) {
        case MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK:
            sts_ntf = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
            /* Write 1 to Clear the pending interrupt */
            // TODO should handle on a per-intr basis
            lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, sts_ntf);
            mcu_intr_rcv.mci_notif0 |= sts_ntf;
            break;
        case MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK:
            sts_ntf = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R);
            /* Write 1 to Clear the pending interrupt */
            // TODO should handle on a per-intr basis
            lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R, sts_ntf);
            mcu_intr_rcv.mci_notif1 |= sts_ntf;
            break;
        default:
            VPRINTF(FATAL, "Bad glbl ntf intr 0x%x\n", which);
            SEND_STDOUT_CTRL(0x1);
            while(1);
    }
    if (!sts_err && !sts_ntf) {
        VPRINTF(ERROR,"bad mci_intr sts:%x %x\n", sts_err, sts_ntf);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

inline void service_i3c_intr() {
    // TODO this ISR needs more logic for I3C interrupts
    uint32_t sts = lsu_read_32(SOC_I3CCSR_I3CBASE_INTR_STATUS) |
                   lsu_read_32(SOC_I3CCSR_PIOCONTROL_PIO_INTR_STATUS) |
                   lsu_read_32(SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_STATUS) |
                   lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS);
    /* Write 1 to Clear the pending interrupt */
    // TODO

    // Status check
    if (sts == 0) {
        VPRINTF(ERROR,"bad i3c_intr sts:%x\n", sts);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}


#endif //MCU_ISR_H
