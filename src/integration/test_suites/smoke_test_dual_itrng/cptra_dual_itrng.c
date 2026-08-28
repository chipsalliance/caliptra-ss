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
//
// cptra_dual_itrng
//
// Caliptra-core half of the subsystem dual-iTRNG smoke test.
//
// Purpose: confirm the dual-iTRNG (entropy_combiner) integration at the
// caliptra_ss_top boundary is wired correctly. The subsystem drives
// cptra_ss_cptra_core_itrng1_en_i, which straps
// CPTRA_HW_CONFIG.dual_iTRNG_en inside the core, which in turn drives the
// entropy_combiner's combine_en. Reading that field back from FW therefore
// proves the whole strap path survived the SS boundary:
//
//   caliptra_ss_top_tb_soc_bfm (+CLP_ITRNG1_EN)
//     -> cptra_ss_cptra_core_itrng1_en_i   (caliptra_ss_top port)
//     -> caliptra_top .itrng1_en           (core port)
//     -> soc_ifc CPTRA_HW_CONFIG.dual_iTRNG_en
//     -> entropy_combiner .combine_en_i
//
// This is deliberately a bring-up/no-violation smoke test: it does not drive
// entropy or check digests. The combiner datapath and its error cases are
// covered by the caliptra-rtl unit benches and the caliptra_top_ss_mode_tb C
// tests. What is unique here is the subsystem-level pin plumbing, so that is
// all this test asserts.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "riscv_hw_if.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main(void) {
    uint32_t hw_cfg;
    uint32_t itrng_en;
    uint32_t dual_itrng_en;

    VPRINTF(LOW, "----------------------------------\nCaliptra: SS dual-iTRNG smoke test\n----------------------------------\n");

    hw_cfg        = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    itrng_en      = (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) ? 1 : 0;
    dual_itrng_en = (hw_cfg & SOC_IFC_REG_CPTRA_HW_CONFIG_DUAL_ITRNG_EN_MASK) ? 1 : 0;

    VPRINTF(LOW, "CPTRA_HW_CONFIG      = 0x%08x\n", hw_cfg);
    VPRINTF(LOW, "  iTRNG_en           = %d\n", itrng_en);
    VPRINTF(LOW, "  dual_iTRNG_en      = %d\n", dual_itrng_en);

    // The subsystem build always compiles the internal TRNG in, so ES0/CSRNG
    // and the combiner must be present.
    if (!itrng_en) {
        handle_error("ERROR: iTRNG_en is 0; subsystem build must have CALIPTRA_INTERNAL_TRNG\n");
    }

    // dual_iTRNG_en mirrors the itrng1_en strap driven from the SS boundary.
    // This test is launched with +CLP_ITRNG1_EN, so it must read back 1. A 0
    // here means the strap was lost somewhere between the SS top-level port and
    // soc_ifc, which is exactly the integration break this test guards.
    if (!dual_itrng_en) {
        handle_error("ERROR: dual_iTRNG_en is 0 with +CLP_ITRNG1_EN set; cptra_ss_cptra_core_itrng1_en_i did not reach soc_ifc\n");
    }

    VPRINTF(LOW, "Dual iTRNG strap reached soc_ifc: entropy_combiner in combine mode\n");
    VPRINTF(LOW, "Caliptra: SS dual-iTRNG smoke test PASSED\n");

    // Signal the MCU that Caliptra bringup and the check both succeeded.
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Wait for MCU to end the test
    while(1);
}
