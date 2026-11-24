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

#include "caliptra_ss_lib.h"
#include "flow004.h"
#include "printf.h"
#include "soc_address_map.h"
#include "usb.h"
#include "usb_ocp_recovery.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
enum printf_verbosity verbosity_g = LOW;

uint8_t main(void)
{
    uint32_t poll;
    uint32_t (*entry)(void) = (uint32_t (*)(void))
        (SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + FLOW004_HEADER_BYTES);

    if (!usb_ocp_recovery_program_device_id() ||
        !usb_ocp_recovery_apply_capability_policy()) {
        handle_error("MCU: USB recovery setup failed\n");
    }
    mcu_cptra_init_d(.cfg_cptra_fuse=true, .cfg_cptra_wdt=true,
                     .cptra_wdt_cfg_0=1u, .cfg_boot_usb_core=true);
    mcu_cptra_user_init();
    for (poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if (mcu_cptra_mb_ready_nb() && usb_is_configured()) {
            break;
        }
        usb_event_loop(32u, 0);
    }
    if (poll == FLOW004_POLL_LIMIT) {
        handle_error("MCU: mailbox/enumeration timed out\n");
    }
    caliptra_mailbox_send_ri_download_firmware();
    for (poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if (lsu_read_32(SOC_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0) & 4u) {
            break;
        }
        usb_event_loop(32u, 0);
    }
    if (poll == FLOW004_POLL_LIMIT) {
        handle_error("MCU: executable image authorization timed out\n");
    }
    __asm__ volatile ("fence.i" ::: "memory");
    if (entry() != FLOW004_MCU_PASS) {
        handle_error("MCU: downloaded SRAM image failed\n");
    }
    VPRINTF(LOW, "FLOW004: downloaded MCU SRAM image sent pass mailbox\n");
    usb_ocp_recovery_wait_for_stop_and_halt(0u);
    return 0u;
}
