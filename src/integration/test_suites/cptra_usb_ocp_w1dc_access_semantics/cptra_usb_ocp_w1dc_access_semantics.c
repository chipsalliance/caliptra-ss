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
// cptra_usb_ocp_w1dc_access_semantics: Caliptra core firmware
//
// Verifies OCP Recovery v1.1 Sec 9.2 Write-1-Device-Clears source
// qualification for DEVICE_RESET.RESET_CTRL and INDIRECT_FIFO_CTRL.RESET.
//
// DEVICE_RESET source qualification:
//   A CPUif write of RESET_CTRL=1 must be stored in the register without
//   triggering the RA device reset action. Only an RA USB write triggers
//   reset. This firmware writes, reads back, then clears the field.
//
// INDIRECT_FIFO_CTRL RESET source qualification:
//   The USB RA resets the FIFO (indices cleared, occupancy zero, RESET
//   readback zero). Then the firmware resets the FIFO via CPUif and
//   independently observes the same behavior.
//
// Firmware/UVM synchronization state encoding:
//   0x01 READY                   - firmware ready
//   0x11 FW_DEVICE_RESET_STORED  - CPUif write RESET_CTRL=1 stored, readback OK
//   0x12 FW_DEVICE_RESET_CLEARED - CPUif write RESET_CTRL=0 verified
//   0x13 FIFO_NONEMPTY_SEEN      - RA programmed image size and FIFO nonempty
//   0x14 USB_FIFO_RESET_OBSERVED - RA USB RESET: indices match, empty, zero
//                                  data = CALIPTRA_STATUS[0] (REGION_RESET bit)
//   0x15 FW_FIFO_RESET_OBSERVED  - CPUif RESET: indices match, empty
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
#define W1DC_FW_STATE_READY                   0x01u
#define W1DC_FW_STATE_FW_DEVICE_RESET_STORED  0x11u
#define W1DC_FW_STATE_FW_DEVICE_RESET_CLEARED 0x12u
#define W1DC_FW_STATE_FIFO_NONEMPTY_SEEN      0x13u
#define W1DC_FW_STATE_USB_FIFO_RESET_OBSERVED 0x14u
#define W1DC_FW_STATE_FW_FIFO_RESET_OBSERVED  0x15u
#define W1DC_FW_STATE_FIFO_UNSUPPORTED        0x16u

// DEVICE_RESET register field masks (OCP Recovery v1.1 Sec 9.2).
// RESET_CTRL is byte 0 (bits [7:0]) of the DEVICE_RESET register word.
#define W1DC_DEVICE_RESET_CTRL_MASK 0x000000FFu
#define W1DC_DEVICE_RESET_CTRL_ONE  0x00000001u

// INDIRECT_FIFO_CTRL_0 field masks.
// RESET is byte 1 (bits [15:8]); CMS is byte 0 (bits [7:0]).
#define W1DC_IFC_RESET_MASK 0x0000FF00u
#define W1DC_IFC_CMS_MASK   0x000000FFu
#define W1DC_IFC_RESET_ONE  0x00000100u

// INDIRECT_FIFO_STATUS_0 EMPTY flag (bit 0).
#define W1DC_IFS_EMPTY_MASK 0x00000001u

// CALIPTRA_STATUS REGION_RESET bit (bit 0).
#define W1DC_CALIPTRA_STATUS_REGION_RESET_MASK 0x00000001u
#define W1DC_PROT_ERROR_MASK 0x0000FF00u
#define W1DC_FIFO_CAP_MASK \
    USB_OCP_RECOVERY_REG_PROT_CAP_2_AGENT_CAPS_FIFO_CMS_SUPPORT_MASK

// Maximum polling iterations.
#define W1DC_POLL_LIMIT 200000u

// Poll INDIRECT_FIFO_STATUS_0 until EMPTY flag is clear (FIFO nonempty).
// Returns write_index, read_index via pointers. Returns 0 on success.
static uint8_t w1dc_poll_fifo_nonempty(uint32_t *write_idx,
                                       uint32_t *read_idx)
{
    uint32_t status_word = 0u;
    for (uint32_t i = 0u; i < W1DC_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_0,
                &status_word) != 0u) {
            continue;
        }
        if (!(status_word & W1DC_IFS_EMPTY_MASK)) {
            if (write_idx != 0) {
                cptra_usb_ocp_recovery_read_dword_retry(
                    SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_1,
                    write_idx);
            }
            if (read_idx != 0) {
                cptra_usb_ocp_recovery_read_dword_retry(
                    SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_2,
                    read_idx);
            }
            return 0u;
        }
    }
    return 1u;
}

static uint8_t w1dc_poll_fifo_occupancy(uint32_t target_occupancy)
{
    uint32_t wi = 0u;
    uint32_t ri = 0u;
    uint32_t fifo_size = 0u;
    uint8_t fifo_status = 0u;

    for (uint32_t i = 0u; i < W1DC_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_fifo_status(
                &fifo_status, &wi, &ri, &fifo_size) != 0u) {
            continue;
        }
        if ((fifo_size >= 2u) &&
            (((wi + fifo_size - ri) % fifo_size) >= target_occupancy)) {
            return 0u;
        }
    }
    return 1u;
}

// Poll INDIRECT_FIFO_STATUS_0 until EMPTY and W==R.
// Returns write_index, read_index via pointers. Returns 0 on success.
static uint8_t w1dc_poll_fifo_empty_indices_match(uint32_t *write_idx,
                                                   uint32_t *read_idx)
{
    uint32_t status_word = 0u;
    uint32_t wi = 0u, ri = 0u;
    for (uint32_t i = 0u; i < W1DC_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_0,
                &status_word) != 0u) {
            continue;
        }
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_1,
                &wi) != 0u) {
            continue;
        }
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_2,
                &ri) != 0u) {
            continue;
        }
        if ((status_word & W1DC_IFS_EMPTY_MASK) && (wi == ri)) {
            if (write_idx != 0) { *write_idx = wi; }
            if (read_idx != 0) { *read_idx = ri; }
            return 0u;
        }
    }
    return 1u;
}

void main(void)
{
    uint32_t dr_val = 0u;
    uint32_t ifc_val = 0u;
    uint32_t wi = 0u, ri = 0u;
    uint32_t caliptra_sts = 0u;

    VPRINTF(LOW, "CPTRA: W1DC access-semantics firmware start\n");

    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    cptra_usb_ocp_recovery_signal_state(W1DC_FW_STATE_READY, 0u);

    // A legal negative RA command sets PROT_ERROR and releases firmware from
    // READY independently of optional FIFO capability.
    for (uint32_t i = 0u; i < W1DC_POLL_LIMIT; ++i) {
        uint32_t status_word = 0u;
        if ((cptra_usb_ocp_recovery_read_device_status_word(
                &status_word) == 0u) &&
            ((status_word & W1DC_PROT_ERROR_MASK) != 0u)) {
            break;
        }
        if ((i + 1u) == W1DC_POLL_LIMIT) {
            VPRINTF(ERROR, "CPTRA: protocol-error start trigger not observed\n");
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }
    }

    // -----------------------------------------------------------------
    // DEVICE_RESET CPUif source qualification.
    //
    // Write RESET_CTRL=1 through CPUif. Source qualification requires that
    // this write does not trigger the Recovery Agent reset action; the value
    // is stored in the register and must read back as 1.
    // -----------------------------------------------------------------

    if (cptra_usb_ocp_recovery_write_device_reset(W1DC_DEVICE_RESET_CTRL_ONE)
            != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA write DEVICE_RESET=1 failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    dr_val = 0u;
    if (cptra_usb_ocp_recovery_read_device_reset(&dr_val) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read DEVICE_RESET failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    if ((dr_val & W1DC_DEVICE_RESET_CTRL_MASK) != W1DC_DEVICE_RESET_CTRL_ONE) {
        VPRINTF(ERROR,
                "CPTRA: DEVICE_RESET.RESET_CTRL readback 0x%08x, expected 0x01\n",
                dr_val);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: DEVICE_RESET.RESET_CTRL stored as 0x01 via CPUif\n");
    cptra_usb_ocp_recovery_signal_state(
        W1DC_FW_STATE_FW_DEVICE_RESET_STORED, 0u);

    // The RA clears the start-trigger PROT_ERROR after observing STORED.
    // Use that protocol-visible clear as the acknowledgment before advancing
    // to the next firmware state.
    for (uint32_t i = 0u; i < W1DC_POLL_LIMIT; ++i) {
        uint32_t status_word = 0u;
        if ((cptra_usb_ocp_recovery_read_device_status_word(
                &status_word) == 0u) &&
            ((status_word & W1DC_PROT_ERROR_MASK) == 0u)) {
            break;
        }
        if ((i + 1u) == W1DC_POLL_LIMIT) {
            VPRINTF(ERROR, "CPTRA: start-trigger PROT_ERROR was not cleared\n");
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }
    }

    // Clear RESET_CTRL via CPUif. No RA action expected.
    if (cptra_usb_ocp_recovery_write_device_reset(0u) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA write DEVICE_RESET=0 failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    dr_val = 0xFFu;
    if (cptra_usb_ocp_recovery_read_device_reset(&dr_val) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read DEVICE_RESET after clear failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    if ((dr_val & W1DC_DEVICE_RESET_CTRL_MASK) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DEVICE_RESET.RESET_CTRL not zero after CPUif clear: 0x%08x\n",
                dr_val);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: DEVICE_RESET.RESET_CTRL cleared via CPUif\n");
    cptra_usb_ocp_recovery_signal_state(
        W1DC_FW_STATE_FW_DEVICE_RESET_CLEARED, 0u);

    // FIFO semantics are conditional on the live advertised capability.
    {
        uint32_t prot_cap_2 = 0u;
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_PROT_CAP_2,
                &prot_cap_2) != 0u) {
            VPRINTF(ERROR, "CPTRA: PROT_CAP_2 read failed\n");
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }
        if ((prot_cap_2 & W1DC_FIFO_CAP_MASK) == 0u) {
            cptra_usb_ocp_recovery_signal_state(
                W1DC_FW_STATE_FIFO_UNSUPPORTED, 0u);
            while (1) {}
        }
    }

    // -----------------------------------------------------------------
    // FIFO USB-reset phase.
    //
    // Wait for the RA to program image size and write FIFO data so the
    // FIFO becomes nonempty. Then wait for the RA USB RESET to empty it.
    // -----------------------------------------------------------------

    VPRINTF(LOW, "CPTRA: waiting for RA to fill FIFO\n");

    if (w1dc_poll_fifo_nonempty(0, 0) != 0u) {
        VPRINTF(ERROR, "CPTRA: FIFO did not become nonempty within poll limit\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: FIFO nonempty observed\n");
    cptra_usb_ocp_recovery_signal_state(
        W1DC_FW_STATE_FIFO_NONEMPTY_SEEN, 0u);

    // Wait for RA USB INDIRECT_FIFO_CTRL RESET=1 to clear the FIFO.
    // After consumption, RESET readback must be zero and indices must match.
    if (w1dc_poll_fifo_empty_indices_match(&wi, &ri) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: FIFO not empty/indices matching after RA USB RESET\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // Verify INDIRECT_FIFO_CTRL_0 RESET readback is zero (device consumed it).
    ifc_val = 0xFFu;
    if (cptra_usb_ocp_recovery_read_indirect_fifo_ctrl(&ifc_val) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read INDIRECT_FIFO_CTRL failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }
    uint8_t usb_reset_stuck =
        (ifc_val & W1DC_IFC_RESET_MASK) != 0u;
    if (usb_reset_stuck) {
        VPRINTF(ERROR,
                "CPTRA: INDIRECT_FIFO_CTRL RESET not zero after USB RESET: 0x%08x\n",
                ifc_val);
    }

    // Read CALIPTRA_STATUS as a diagnostic; it is independent of OCP RESET.
    caliptra_sts = 0u;
    (void)cptra_usb_ocp_recovery_read_caliptra_status(&caliptra_sts);
    VPRINTF(LOW,
            "CPTRA: USB FIFO reset observed W=%u R=%u caliptra_status=0x%08x\n",
            wi, ri, caliptra_sts);

    cptra_usb_ocp_recovery_signal_state(
        W1DC_FW_STATE_USB_FIFO_RESET_OBSERVED,
        (uint8_t)((caliptra_sts &
                   W1DC_CALIPTRA_STATUS_REGION_RESET_MASK) |
                  (usb_reset_stuck ? 0x02u : 0x00u)));

    // -----------------------------------------------------------------
    // FIFO firmware-reset phase.
    //
    // Wait for RA to refill FIFO. Then firmware writes
    // INDIRECT_FIFO_CTRL_0 RESET=1 through CPUif, preserving CMS.
    // Verify FIFO empty, W==R, RESET readback zero.
    // -----------------------------------------------------------------

    VPRINTF(LOW, "CPTRA: waiting for RA to refill FIFO\n");

    if (w1dc_poll_fifo_occupancy(2u) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: FIFO did not reach two DWORDs for firmware-reset phase\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // Read current INDIRECT_FIFO_CTRL to preserve CMS value.
    ifc_val = 0u;
    if (cptra_usb_ocp_recovery_read_indirect_fifo_ctrl(&ifc_val) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read INDIRECT_FIFO_CTRL before FW RESET failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // Write RESET=1 via CPUif, preserving CMS.
    {
        uint32_t cms = ifc_val & W1DC_IFC_CMS_MASK;
        if (cptra_usb_ocp_recovery_write_indirect_fifo_ctrl(
                cms | W1DC_IFC_RESET_ONE) != 0u) {
            VPRINTF(ERROR,
                    "CPTRA: DMA write INDIRECT_FIFO_CTRL RESET=1 failed\n");
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }
    }

    // Verify FIFO is now empty with matching indices.
    if (w1dc_poll_fifo_empty_indices_match(&wi, &ri) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: FIFO not empty after firmware CPUif RESET\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // Verify RESET readback zero.
    ifc_val = 0xFFu;
    if (cptra_usb_ocp_recovery_read_indirect_fifo_ctrl(&ifc_val) != 0u) {
        VPRINTF(ERROR,
                "CPTRA: DMA read INDIRECT_FIFO_CTRL after FW RESET failed\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }
    uint8_t fw_reset_stuck =
        (ifc_val & W1DC_IFC_RESET_MASK) != 0u;
    if (fw_reset_stuck) {
        VPRINTF(ERROR,
                "CPTRA: INDIRECT_FIFO_CTRL RESET not zero after FW CPUif RESET: 0x%08x\n",
                ifc_val);
    }

    caliptra_sts = 0u;
    (void)cptra_usb_ocp_recovery_read_caliptra_status(&caliptra_sts);
    VPRINTF(LOW,
            "CPTRA: FW FIFO reset observed W=%u R=%u caliptra_status=0x%08x\n",
            wi, ri, caliptra_sts);

    cptra_usb_ocp_recovery_signal_state(
        W1DC_FW_STATE_FW_FIFO_RESET_OBSERVED,
        fw_reset_stuck ? 0x01u : 0x00u);

    VPRINTF(LOW, "CPTRA: W1DC access-semantics firmware complete\n");

    // UVM sequence owns completion. Firmware remains alive.
    while (1) {}
}
