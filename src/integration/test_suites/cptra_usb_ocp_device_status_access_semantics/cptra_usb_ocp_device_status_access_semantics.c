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
// caliptra_ss_usb_ocp_device_status_access_semantics: Caliptra core firmware
//
// Verifies OCP Recovery v1.1 Sec 9.1 source-qualified clear semantics for
// DEVICE_STATUS PROT_ERROR. CPUif (DMA) reads of DEVICE_STATUS_0 are
// non-destructive; only Recovery Agent USB reads clear PROT_ERROR.
//
// Firmware handshake uses SS_GENERIC_FW_EXEC_CTRL_0[10:3] for state and
// [18:11] for data. The UVM sequence observes these via the top-level
// fw_exec_ctrl_o output.
//
// Firmware/UVM synchronization state encoding:
//   0x01 READY              - firmware ready for UVM to begin
//   0x02 CPU_READ_PRESERVED - firmware confirmed PROT_ERROR unchanged by
//                             two consecutive DMA reads; data = error byte
//   0x03 USB_CLEAR_OBSERVED - firmware confirmed PROT_ERROR cleared to zero
//                             after the UVM's RA USB read
//   0x04 STRESS_SET_SEEN    - stress iteration: firmware confirmed PROT_ERROR
//                             set and persists; data = iteration (1-based)
//   0x05 STRESS_CLEAR_SEEN  - stress iteration: firmware confirmed PROT_ERROR
//                             cleared after UVM's RA USB read; data = iteration
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
#define DS_FW_STATE_READY              0x01u
#define DS_FW_STATE_CPU_READ_PRESERVED 0x02u
#define DS_FW_STATE_USB_CLEAR_OBSERVED 0x03u
#define DS_FW_STATE_STRESS_SET_SEEN    0x04u
#define DS_FW_STATE_STRESS_CLEAR_SEEN  0x05u

// Maximum polling iterations for DMA-based register polls.
#define DS_POLL_LIMIT 200000u

// Byte mask for PROT_ERROR field in DEVICE_STATUS_0 word (bits [15:8]).
#define DS_PROT_ERROR_MASK 0x0000FF00u

// Poll DEVICE_STATUS_0 via DMA until PROT_ERROR (bits [15:8]) is nonzero.
// Returns the observed PROT_ERROR byte (bits [15:8] >> 8), or 0 on timeout.
static uint8_t ds_poll_until_prot_error_set(void)
{
    uint32_t word = 0u;
    for (uint32_t i = 0u; i < DS_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_device_status_word(&word) != 0u) {
            continue;
        }
        if (word & DS_PROT_ERROR_MASK) {
            return (uint8_t)((word & DS_PROT_ERROR_MASK) >> 8);
        }
    }
    return 0u;
}

// Poll DEVICE_STATUS_0 via DMA until PROT_ERROR is zero.
// Returns 0 on success, 1 on timeout.
static uint8_t ds_poll_until_prot_error_clear(void)
{
    uint32_t word = 0u;
    for (uint32_t i = 0u; i < DS_POLL_LIMIT; ++i) {
        if (cptra_usb_ocp_recovery_read_device_status_word(&word) != 0u) {
            continue;
        }
        if (!(word & DS_PROT_ERROR_MASK)) {
            return 0u;
        }
    }
    return 1u;
}

void main(void)
{
    uint8_t prot_error_byte = 0u;
    uint8_t second_read_byte = 0u;
    uint32_t word = 0u;

    VPRINTF(LOW, "CPTRA: device-status access-semantics firmware start\n");

    // Boot readiness allows the MCU to finish enumeration and send the
    // mailbox command that releases recovery-register polling.
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Keep recovery-register traffic out of USB reset and high-speed
    // negotiation; the MCU sends this command after enumeration completes.
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) &
            MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0u) {
    }
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (uint32_t)CMD_COMPLETE);

    // Signal READY before reading any OCP register.
    cptra_usb_ocp_recovery_signal_state(DS_FW_STATE_READY, 0u);

    VPRINTF(LOW, "CPTRA: waiting for RA to trigger PROT_ERROR\n");

    // Poll DEVICE_STATUS_0 via DMA until PROT_ERROR is set.
    // The RA issues a negative command (write to read-only PROT_CAP).
    prot_error_byte = ds_poll_until_prot_error_set();
    if (prot_error_byte == 0u) {
        VPRINTF(ERROR, "CPTRA: PROT_ERROR did not set within poll limit\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    // Perform a second DMA read and verify PROT_ERROR is still the same value.
    // This proves CPUif reads are non-destructive per OCP Recovery v1.1 Sec 9.1.
    word = 0u;
    if (cptra_usb_ocp_recovery_read_device_status_word(&word) != 0u) {
        VPRINTF(ERROR, "CPTRA: DMA read failed on PROT_ERROR persistence check\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }
    second_read_byte = (uint8_t)((word & DS_PROT_ERROR_MASK) >> 8);
    if (second_read_byte != prot_error_byte) {
        VPRINTF(ERROR,
                "CPTRA: PROT_ERROR changed between two CPUif reads: 0x%02x -> 0x%02x\n",
                prot_error_byte, second_read_byte);
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: PROT_ERROR=0x%02x preserved across two CPUif reads\n",
            prot_error_byte);
    // Publish CPU_READ_PRESERVED with observed error code as data.
    cptra_usb_ocp_recovery_signal_state(
        DS_FW_STATE_CPU_READ_PRESERVED, prot_error_byte);

    // Wait for the RA USB DEVICE_STATUS read to clear PROT_ERROR.
    // The UVM sequence reads DEVICE_STATUS (first USB read - the clearing read).
    if (ds_poll_until_prot_error_clear() != 0u) {
        VPRINTF(ERROR, "CPTRA: PROT_ERROR did not clear within poll limit\n");
        SEND_STDOUT_CTRL(0x1);
        while (1) {}
    }

    VPRINTF(LOW, "CPTRA: PROT_ERROR cleared after RA USB read\n");
    cptra_usb_ocp_recovery_signal_state(DS_FW_STATE_USB_CLEAR_OBSERVED, 0u);

    // Stress loop: 4 iterations of set/clear cycling.
    // Each iteration:
    //   1. UVM issues a negative command (set)
    //   2. Firmware polls until set, reads twice, publishes STRESS_SET_SEEN
    //   3. UVM reads DEVICE_STATUS via USB (first read - clearing read)
    //   4. Firmware polls until clear, publishes STRESS_CLEAR_SEEN
    //   5. UVM reads DEVICE_STATUS via USB (second read - expects zero)
    for (uint32_t iter = 1u; iter <= 4u; ++iter) {
        prot_error_byte = ds_poll_until_prot_error_set();
        if (prot_error_byte == 0u) {
            VPRINTF(ERROR,
                    "CPTRA: stress iter %u: PROT_ERROR did not set\n", iter);
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }

        // Second CPUif read - verifies persistence across reads.
        word = 0u;
        if (cptra_usb_ocp_recovery_read_device_status_word(&word) != 0u) {
            VPRINTF(ERROR,
                    "CPTRA: stress iter %u: second DMA read failed\n", iter);
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }
        second_read_byte = (uint8_t)((word & DS_PROT_ERROR_MASK) >> 8);
        if (second_read_byte != prot_error_byte) {
            VPRINTF(ERROR,
                    "CPTRA: stress iter %u: PROT_ERROR changed 0x%02x->0x%02x\n",
                    iter, prot_error_byte, second_read_byte);
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }

        VPRINTF(LOW, "CPTRA: stress iter %u: PROT_ERROR=0x%02x set and persistent\n",
                iter, prot_error_byte);
        cptra_usb_ocp_recovery_signal_state(
            DS_FW_STATE_STRESS_SET_SEEN, (uint8_t)iter);

        // Poll until RA USB read clears PROT_ERROR.
        if (ds_poll_until_prot_error_clear() != 0u) {
            VPRINTF(ERROR,
                    "CPTRA: stress iter %u: PROT_ERROR did not clear\n", iter);
            SEND_STDOUT_CTRL(0x1);
            while (1) {}
        }

        VPRINTF(LOW, "CPTRA: stress iter %u: PROT_ERROR cleared\n", iter);
        cptra_usb_ocp_recovery_signal_state(
            DS_FW_STATE_STRESS_CLEAR_SEEN, (uint8_t)iter);
    }

    VPRINTF(LOW, "CPTRA: device-status access-semantics firmware complete\n");

    // UVM sequence owns completion. Firmware remains alive.
    while (1) {}
}
