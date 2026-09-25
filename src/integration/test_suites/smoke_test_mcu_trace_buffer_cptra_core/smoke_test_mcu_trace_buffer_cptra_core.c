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
//
// smoke_test_mcu_trace_buffer_cptra_core (MCU side)
//
// Companion MCU program for the Caliptra-core trace-buffer collection test. Its only
// job is to unlock debug (so the trace buffer is readable over the fabric) and then
// idle; the SV test (SMOKE_TEST_MCU_TRACE_BUFFER_CPTRA_CORE) halts this core, selects
// the Caliptra core as the trace source, and verifies the buffer captured Caliptra-core
// trace. The actual trace stream to be captured is produced by the Caliptra core
// running cptra_smoke_test_mcu_trace_buffer_cptra_core.
//
#include "soc_address_map.h"
#include "mci.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    VPRINTF(LOW, "=================\nMCU: Trace buffer Caliptra-core source test\n=================\n\n");

    // Boot the Caliptra core so it runs its companion firmware
    // (cptra_smoke_test_mcu_trace_buffer_cptra_core): an infinite loop that retires
    // instructions continuously and drives the trace_rv_i_* stream the MCI trace buffer
    // captures. Without releasing the core it stays idle, no trace is produced, and the
    // SV test hangs waiting for the buffer to fill. reset_fc_lcc_rtl() below only resets
    // FC/LCC (a TB service), not the Caliptra core, so the core keeps producing trace.
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    // Unlock debug so the trace buffer is accessible for read-back over the fabric.
    // (Trace collection itself is continuous and not debug-gated; only read access is.)
    lcc_initialization();
    transition_state(TEST_UNLOCKED0, raw_unlock_token, false);
    reset_fc_lcc_rtl();

    VPRINTF(LOW, "MCU: Debug unlocked; idling while the SV test drives the Caliptra-core trace capture.\n");

    // Idle. The SV test halts this core, selects the Caliptra-core trace source, waits
    // for the buffer to fill with Caliptra-core trace, and then verifies it.
    while (1);
}
