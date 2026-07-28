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

// ==========================================================================
// cptra_usb_ocp_recovery_activation_access_semantics: Caliptra core firmware
//
// Verifies OCP Recovery v1.1 Sec 9.2 RECOVERY_CTRL.ACTIVATE source
// qualification. The activation action is gated: firmware nonzero writes
// do not cause activation; only firmware writing zero after the RA has set
// the field triggers the externally visible action.
//
// Firmware/UVM synchronization state encoding:
//   0x01 READY                   - firmware ready
//   0x21 FW_NONZERO_STORED_PRE   - firmware wrote ACTIVATE=0x0F before RA;
//                                  readback confirms 0x0F stored
//   0x22 FW_PRE_RA_CLEARED       - firmware cleared ACTIVATE=0 before RA sets
//   0x23 RA_ACTIVATE_PENDING     - RA has set ACTIVATE=0x0F; firmware reading
//                                  0x0F repeatedly, confirms pending
//   0x24 FW_NONZERO_AFTER_RA     - firmware wrote ACTIVATE=0x0F after RA set;
//                                  readback still 0x0F (stored, not triggering)
//   0x25 FW_ZERO_ARMED           - firmware observed the RA protocol-error
//                                  trigger and waits for the RA clear
//   0x26 FW_ACTIVATE_CLEARED     - firmware wrote ACTIVATE=0; this triggers
//                                  the externally visible activation action
// ==========================================================================

#include <stdint.h>

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "usb_ocp_recovery_cptra.h"

volatile char *stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

// Firmware/UVM synchronization state codes.
#define RA_FW_STATE_READY                 0x01u
#define RA_FW_STATE_FW_NONZERO_STORED_PRE 0x21u
#define RA_FW_STATE_FW_PRE_RA_CLEARED     0x22u
#define RA_FW_STATE_RA_ACTIVATE_PENDING   0x23u
#define RA_FW_STATE_FW_NONZERO_AFTER_RA   0x24u
#define RA_FW_STATE_FW_ZERO_ARMED         0x25u
#define RA_FW_STATE_FW_ACTIVATE_CLEARED   0x26u

// OCP Recovery v1.1 Sec 9.2 RECOVERY_CTRL ACTIVATE code.
#define RA_RC_ACTIVATE_CODE 0x0Fu

// RECOVERY_CTRL word layout:
//   [7:0]  CMS
//   [15:8] REC_IMG_SEL
//   [23:16] ACTIVATE_REC_IMG
#define RA_RC_ACTIVATE_MASK 0x00FF0000u
#define RA_RC_ACTIVATE_SHIFT 16u

// INDIRECT_FIFO_CTRL_0 IMAGE_SIZE field (bits [63:32] of INDIRECT_FIFO_CTRL).
// IMAGE_SIZE is in INDIRECT_FIFO_CTRL_1 (second word).
#define RA_IFC1_IMAGE_SIZE_MASK 0xFFFFFFFFu
#define RA_PROT_ERROR_MASK 0x0000FF00u

// Maximum polling iterations.
#define RA_POLL_LIMIT 200000u
#define RA_STATE_HOLD_CYCLES 10000u

static void ra_state_hold(void)
{
    for (uint32_t i = 0u; i < RA_STATE_HOLD_CYCLES; ++i) {
        __asm__ volatile ("nop");
    }
}

// Poll RECOVERY_CTRL until ACTIVATE field is the target value.
// Returns the full RECOVERY_CTRL word. Returns 0 on success.
static uint8_t ra_poll_activate_value(uint8_t target,
                                      uint32_t *rc_word_out)
{
    uint32_t rc_word = 0u;
    for (uint32_t i = 0u; i < RA_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_recovery_ctrl(&rc_word) != 0u) {
            continue;
        }
        uint8_t activate = (uint8_t)((rc_word & RA_RC_ACTIVATE_MASK)
                                     >> RA_RC_ACTIVATE_SHIFT);
        if (activate == target) {
            if (rc_word_out != 0) { *rc_word_out = rc_word; }
            return 0u;
        }
    }
    return 1u;
}

// Poll INDIRECT_FIFO_CTRL_1 (image size) until nonzero.
static uint8_t ra_poll_image_size_nonzero(void)
{
    uint32_t size_word = 0u;
    for (uint32_t i = 0u; i < RA_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_CTRL_1,
                &size_word) != 0u) {
            continue;
        }
        if (size_word != 0u) {
            return 0u;
        }
    }
    return 1u;
}

// Poll INDIRECT_FIFO_STATUS_0 until nonempty (EMPTY flag clear).
static uint8_t ra_poll_fifo_nonempty(void)
{
    uint32_t status_word = 0u;
    for (uint32_t i = 0u; i < RA_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_0,
                &status_word) != 0u) {
            continue;
        }
        if (!(status_word & 0x00000001u)) {
            return 0u;
        }
    }
    return 1u;
}

static uint8_t ra_poll_protocol_error(uint8_t expect_set)
{
    uint32_t status_word = 0u;
    for (uint32_t i = 0u; i < RA_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_device_status_word(
                &status_word) != 0u) {
            continue;
        }
        if (((status_word & RA_PROT_ERROR_MASK) != 0u) == (expect_set != 0u)) {
            return 0u;
        }
    }
    return 1u;
}

void main(void)
{
    uint32_t rc_word = 0u;
    uint32_t fifo_data = 0u;
    uint8_t activate_byte = 0u;

    VPRINTF(LOW, "CPTRA: recovery-activation access-semantics firmware start\n");

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_READY, 0u);

    // IMAGE_SIZE is the protocol-visible release from READY. This keeps the
    // pre-RA firmware states stable until USB enumeration has completed and
    // the Recovery Agent is ready to observe them.
    if (ra_poll_image_size_nonzero() != 0u) {
        VPRINTF(ERROR, "CPTRA: IMAGE_SIZE start trigger not observed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // -----------------------------------------------------------------
    // Pre-RA firmware nonzero write to RECOVERY_CTRL.ACTIVATE.
    //
    // Write ACTIVATE=0x0F before the RA has set the field. This write
    // must be stored (readback confirms) but must not trigger activation,
    // because no RA USB write has been issued yet and the required
    // firmware-zero consumption has not occurred.
    // -----------------------------------------------------------------

    // Build RECOVERY_CTRL word: CMS=0, IMG_SEL=0, ACTIVATE=0x0F.
    rc_word = (uint32_t)RA_RC_ACTIVATE_CODE << RA_RC_ACTIVATE_SHIFT;
    if (cptra_usb_ocp_recovery_write_recovery_ctrl(rc_word) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DMA write RECOVERY_CTRL ACTIVATE=0x0F (pre-RA) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    rc_word = 0u;
    if (cptra_usb_ocp_recovery_read_recovery_ctrl(&rc_word) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read RECOVERY_CTRL (pre-RA) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    activate_byte = (uint8_t)((rc_word & RA_RC_ACTIVATE_MASK) >> RA_RC_ACTIVATE_SHIFT);
    if (activate_byte != RA_RC_ACTIVATE_CODE) {
        VPRINTF(ERROR,
                "CPTRA: RECOVERY_CTRL ACTIVATE pre-RA readback 0x%02x, expected 0x%02x\n",
                activate_byte, RA_RC_ACTIVATE_CODE);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW,
            "CPTRA: RECOVERY_CTRL ACTIVATE=0x%02x stored pre-RA (no activation)\n",
            activate_byte);
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_FW_NONZERO_STORED_PRE, 0u);
    ra_state_hold();

    // Clear ACTIVATE via CPUif. No activation triggered.
    if (cptra_usb_ocp_recovery_write_recovery_ctrl(0u) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA write RECOVERY_CTRL ACTIVATE=0 failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    rc_word = 0xFFu;
    if (cptra_usb_ocp_recovery_read_recovery_ctrl(&rc_word) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read RECOVERY_CTRL after pre-RA clear failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    if ((rc_word & RA_RC_ACTIVATE_MASK) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: RECOVERY_CTRL ACTIVATE not zero after pre-RA clear: 0x%08x\n",
                rc_word);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: RECOVERY_CTRL ACTIVATE cleared pre-RA\n");
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_FW_PRE_RA_CLEARED, 0u);

    // -----------------------------------------------------------------
    // Wait for RA to program image size and make FIFO data available.
    // Consume one DWORD and optionally verify deterministic 0xC0DE0000.
    // -----------------------------------------------------------------

    if (ra_poll_fifo_nonempty() != 0u) {
        VPRINTF(ERROR, "CPTRA: FIFO did not become nonempty for activation test\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    fifo_data = 0u;
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
            &fifo_data) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read FIFO data failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    if (fifo_data != 0xC0DE0000u) {
        VPRINTF(ERROR,
                "CPTRA: FIFO data 0x%08x expected 0xC0DE0000\n",
                fifo_data);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // -----------------------------------------------------------------
    // Wait for RA USB write RECOVERY_CTRL ACTIVATE=0x0F.
    // Confirm ACTIVATE is 0x0F and remains so across repeated reads.
    // -----------------------------------------------------------------

    if (ra_poll_activate_value(RA_RC_ACTIVATE_CODE, &rc_word) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: RECOVERY_CTRL ACTIVATE did not reach 0x%02x from RA\n",
                RA_RC_ACTIVATE_CODE);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: RA ACTIVATE=0x0F is pending\n");
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_RA_ACTIVATE_PENDING, 0u);

    // -----------------------------------------------------------------
    // Firmware nonzero write to ACTIVATE after RA has set it.
    // This write must store the value without triggering activation.
    // -----------------------------------------------------------------

    rc_word = (uint32_t)RA_RC_ACTIVATE_CODE << RA_RC_ACTIVATE_SHIFT;
    if (cptra_usb_ocp_recovery_write_recovery_ctrl(rc_word) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DMA write RECOVERY_CTRL ACTIVATE=0x0F (post-RA) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    rc_word = 0u;
    if (cptra_usb_ocp_recovery_read_recovery_ctrl(&rc_word) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read RECOVERY_CTRL (post-RA write) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    activate_byte = (uint8_t)((rc_word & RA_RC_ACTIVATE_MASK) >> RA_RC_ACTIVATE_SHIFT);
    if (activate_byte == 0u) {
        VPRINTF(ERROR,
                "CPTRA: RECOVERY_CTRL ACTIVATE is zero after FW nonzero write post-RA\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: RECOVERY_CTRL ACTIVATE=0x%02x after FW nonzero post-RA\n",
            activate_byte);
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_FW_NONZERO_AFTER_RA, 0u);

    if (ra_poll_protocol_error(1u) != 0u) {
        VPRINTF(ERROR, "CPTRA: pre-zero protocol-error trigger not observed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_FW_ZERO_ARMED, 0u);

    if (ra_poll_protocol_error(0u) != 0u) {
        VPRINTF(ERROR, "CPTRA: pre-zero protocol-error clear not observed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // -----------------------------------------------------------------
    // Firmware writes ACTIVATE=0. This triggers the externally visible
    // activation action (recovery_image_activated output asserts).
    // -----------------------------------------------------------------

    if (cptra_usb_ocp_recovery_write_recovery_ctrl(0u) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DMA write RECOVERY_CTRL ACTIVATE=0 (trigger) failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    rc_word = 0xFFu;
    if (cptra_usb_ocp_recovery_read_recovery_ctrl(&rc_word) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DMA read RECOVERY_CTRL after ACTIVATE=0 failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    if ((rc_word & RA_RC_ACTIVATE_MASK) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: RECOVERY_CTRL ACTIVATE not zero after FW clear: 0x%08x\n",
                rc_word);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW,
            "CPTRA: RECOVERY_CTRL ACTIVATE cleared by firmware; activation triggered\n");
    cptra_usb_ocp_recovery_signal_state(RA_FW_STATE_FW_ACTIVATE_CLEARED, 0u);

    VPRINTF(LOW,
            "CPTRA: recovery-activation access-semantics firmware complete\n");

    // UVM sequence owns completion. Firmware remains alive.
    while (1) {}
}
