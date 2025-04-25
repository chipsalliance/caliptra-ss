//********************************************************************************
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
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Global variable allocated to DCCM explicitly, to test DCCM access
static const char* dccm_msg __attribute__ ((section(".dccm"))) = "=================\nHello World from MCU DCCM\n=================\n\n";

uint8_t main (void) {
    int argc=0;
    char *argv[1];
    uint32_t reg_data;

    // Print message from DCCM memory
    if (dccm_msg[0] != '=') {
        VPRINTF(FATAL, "MCU: DCCM does not contain expected message!\nExpected: '=', saw '%c'\n", dccm_msg[0]);
    } else {
        VPRINTF(LOW, dccm_msg)
    }

    VPRINTF(LOW, "MCU: Caliptra bringup\n")
    mcu_cptra_init_d();

    mcu_cptra_poll_mb_ready();

    // return status is treated as an 'exit' code by mcu_crt0
    // 0-value indicates success, non-zero is error
    return 0;
}
