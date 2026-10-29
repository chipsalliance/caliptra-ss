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
// cptra_smoke_test_mcu_trace_buffer_cptra_core (Caliptra core side)
//
// Runs on the Caliptra core for the Caliptra-core trace-buffer collection test. The
// core continuously retires instructions so it produces a steady trace_rv_i_* stream.
// With the MCI trace buffer's source select set to the Caliptra core (by the SV test),
// this trace is captured into the buffer and verified. The infinite loop compiles to a
// branch-to-self, which retires every iteration and drives the trace port.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "riscv_hw_if.h"
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
    VPRINTF(LOW,"Caliptra Core - waiting for trace buffer to fill\n");
    // Continuously retire instructions to produce a Caliptra-core trace stream for the
    // MCI trace buffer to capture.
    volatile uint32_t counter = 0;
    while (1) {
        counter++;
    }
}
