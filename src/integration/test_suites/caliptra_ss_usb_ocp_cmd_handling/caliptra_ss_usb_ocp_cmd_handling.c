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

#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "printf.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#define USB_EVENT_LOOP_DIAG_PERIOD 1000u
#include "usb.h"
#include "usb_ocp_recovery.h"

#define USB_OCP_CMD_EVENT_LOOP_SLICE 256u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t main(void)
{
    VPRINTF(LOW, "MCU: USB OCP command-handling test\n");

    boot_mcu();
    boot_usb_core(usb_ocp_recovery_get_v1p1_config_descriptor,
                  usb_ocp_recovery_handle_class_request);

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();

    // Keep the USB control pipe serviced while the Caliptra core reaches its
    // quiescent ready state. OCP Recovery v1.1 Sec 8.5 requires the Device to
    // respond to Recovery Agent commands after USB reaches Configured state.
    while (!mcu_cptra_mb_ready_nb() || !usb_is_configured()) {
        usb_event_loop(USB_OCP_CMD_EVENT_LOOP_SLICE, 0u);
    }

    // The UVM Recovery Agent owns test completion. Firmware remains quiescent
    // except for servicing USB SETUP traffic and never reads DEVICE_STATUS, so
    // it cannot race the RA clear-on-read checks from OCP Recovery v1.1 Sec 9.1.
    while (1) {
        usb_event_loop(USB_OCP_CMD_EVENT_LOOP_SLICE, 0u);
    }
}
