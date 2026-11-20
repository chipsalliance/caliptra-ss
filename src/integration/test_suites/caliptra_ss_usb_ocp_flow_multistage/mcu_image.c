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

#include "flow004.h"
#include "soc_address_map.h"

__attribute__((section(".text.entry")))
uint32_t image_entry(void)
{
    volatile uint32_t *lock = (volatile uint32_t *)SOC_MBOX_CSR_MBOX_LOCK;
    volatile uint32_t *status = (volatile uint32_t *)SOC_MBOX_CSR_MBOX_STATUS;
    for (uint32_t poll = 0u; poll < FLOW004_POLL_LIMIT; ++poll) {
        if ((*lock & 1u) == 0u) {
            *(volatile uint32_t *)SOC_MBOX_CSR_MBOX_CMD = FLOW004_MCU_PASS;
            *(volatile uint32_t *)SOC_MBOX_CSR_MBOX_DLEN = 0u;
            *(volatile uint32_t *)SOC_MBOX_CSR_MBOX_EXECUTE = 1u;
            for (uint32_t ack = 0u; ack < FLOW004_POLL_LIMIT; ++ack) {
                if ((*status & 7u) == 2u) {
                    *(volatile uint32_t *)SOC_MBOX_CSR_MBOX_EXECUTE = 0u;
                    return FLOW004_MCU_PASS;
                }
            }
            return 0u;
        }
    }
    return 0u;
}
