//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//
// Test: mci_sram_error
//
// Writes a word to MCU SRAM, injects a double-bit ECC error (corrupting the
// stored ECC on the next write), then issues a byte write to the same address.
// The byte write triggers a read-modify-write (RMW) in the SRAM controller.
// During the RMW read phase the controller detects the double-bit ECC error,
// raises a fatal HW error, and suppresses the write phase so that the SRAM
// word is not modified.  The NMI handler verifies the error flag and passes.
//
//********************************************************************************
#include <stdint.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "mci.h"
#include "caliptra_ss_lib.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void nmi_handler(void);

void nmi_handler(void) {
    VPRINTF(LOW, "*** Entering NMI Handler ***\n");

    uint32_t fatal = lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL);
    if (!(fatal & MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK)) {
        handle_error("Unexpected NMI: HW_ERROR_FATAL=0x%08x, expected MCU_SRAM_ECC_UNC\n", fatal);
    }

    // Clear the fatal error.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL) & MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK) {
        handle_error("Unable to clear MCU SRAM ECC UNC fatal error\n");
    }

    VPRINTF(LOW, "INFO: MCU SRAM double-bit ECC error raised and cleared as expected\n");
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU mci_sram_error\n=================\n\n");

    // Register NMI handler so the CPU can catch the fatal ECC error.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t)(nmi_handler));

    // Unmask the MCU SRAM ECC uncorrectable fatal interrupt.
    uint32_t mask = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK);
    mask |= MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_MASK;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK, mask);

    uint32_t test_addr = get_mcu_sram_protected_region_start();
    uint32_t test_data = 0xDEADBEEF;

    // Initial clean write — establishes known data in SRAM with correct ECC.
    VPRINTF(LOW, "INFO: writing 0x%08x to SRAM addr 0x%08x\n", test_data, test_addr);
    lsu_write_32(test_addr, test_data);

    // Enable double-bit ECC injection.
    // First SRAM write after enabling injection is clean (bitflip mask is 0 at that point);
    // the second write uses the generated mask and stores corrupted ECC.
    SEND_STDOUT_CTRL(TB_CMD_INJECT_MCU_SRAM_DOUBLE_ECC_ERROR);

    // Write #1 with injection active — clean, primes the bitflip mask.
    lsu_write_32(test_addr, test_data);

    // Write #2 with injection active — stored ECC is now double-bit corrupted.
    lsu_write_32(test_addr, test_data);

    // Disable injection: the corruption is already stored in SRAM.
    SEND_STDOUT_CTRL(TB_CMD_DISABLE_MCU_SRAM_ECC_ERROR_INJECTION);

    // Issue a byte write to the same address.  The SRAM controller must perform
    // a read-modify-write (RMW): the read phase detects the double-bit ECC error,
    // the write phase is suppressed, and a fatal NMI is raised.
    VPRINTF(LOW, "INFO: issuing byte write (RMW) to trigger double-bit ECC error\n");
    *((volatile uint8_t*)(uintptr_t)test_addr) = 0xAA;

    handle_error("Test did not receive expected NMI for MCU SRAM double-bit ECC error\n");
}
