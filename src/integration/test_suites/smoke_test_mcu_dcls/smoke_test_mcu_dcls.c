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

// Smoke test: verify MCU_DCLS_DISABLE register read/write.
//
// The register uses MUBI4 encoding:
//   El2MuBiTrue  = 0x6  -> corruption detection DISABLED (reset default)
//   El2MuBiFalse = 0x9  -> corruption detection ENABLED
//
// The register is write-gated by axi_mcu_or_mci_soc_config_req__ss_config_unlock
// (i.e. writable until SS_CONFIG_DONE is set), so writes must happen before
// calling mcu_cptra_init_d().

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define MUBI4_TRUE  (0x6u)  // El2MuBiTrue  - detection disabled
#define MUBI4_FALSE (0x9u)  // El2MuBiFalse - detection enabled

uint8_t main(void) {
    uint32_t val;

    VPRINTF(LOW, "MCU DCLS: register smoke test\n");

    // --- 1. Check power-on default (El2MuBiTrue = disabled) ---
    val = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_DCLS_DISABLE) & 0xF;
    VPRINTF(LOW, "MCU DCLS: default = 0x%x (expect 0x6)\n", val);
    if (val != MUBI4_TRUE) {
        VPRINTF(FATAL, "MCU DCLS: FAIL default value 0x%x != 0x6\n", val);
        return 1;
    }

    // --- 2. Enable DCLS (write El2MuBiFalse = 0x9) ---
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_DCLS_DISABLE, MUBI4_FALSE);
    val = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_DCLS_DISABLE) & 0xF;
    VPRINTF(LOW, "MCU DCLS: after enable write = 0x%x (expect 0x9)\n", val);
    if (val != MUBI4_FALSE) {
        VPRINTF(FATAL, "MCU DCLS: FAIL enable readback 0x%x != 0x9\n", val);
        return 2;
    }

    // --- 3. Disable DCLS again (write El2MuBiTrue = 0x6) ---
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_DCLS_DISABLE, MUBI4_TRUE);
    val = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_DCLS_DISABLE) & 0xF;
    VPRINTF(LOW, "MCU DCLS: after disable write = 0x%x (expect 0x6)\n", val);
    if (val != MUBI4_TRUE) {
        VPRINTF(FATAL, "MCU DCLS: FAIL disable readback 0x%x != 0x6\n", val);
        return 3;
    }

    VPRINTF(LOW, "MCU DCLS: PASS\n");

    mcu_cptra_init_d();
    mcu_cptra_poll_mb_ready();

    return 0;
}
