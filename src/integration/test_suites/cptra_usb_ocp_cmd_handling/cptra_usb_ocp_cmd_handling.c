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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
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

void main(void)
{
    uint64_t recovery_base;

    recovery_base = cptra_usb_ocp_recovery_get_base();
    VPRINTF(LOW,
            "CPTRA: OCP command-handling device firmware ready, recovery base lo=0x%08x hi=0x%08x\n",
            (uint32_t)recovery_base,
            (uint32_t)(recovery_base >> 32));

    // Signal readiness without reading any OCP command register. In
    // particular, this firmware must not read DEVICE_STATUS while the USB
    // Recovery Agent verifies its clear-on-read PROTOCOL_ERROR field.
    soc_ifc_set_flow_status_field(
        SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    while (1) {
    }
}
