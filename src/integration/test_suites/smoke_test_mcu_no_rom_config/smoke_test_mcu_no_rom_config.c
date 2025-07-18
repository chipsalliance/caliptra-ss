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


#include "soc_address_map.h"
#include "caliptra_ss_lib.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "veer-csr.h"
#include "soc_ifc.h"
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {

    VPRINTF(LOW, "=================\nHello World from MCU SRAM\n=================\n");

    VPRINTF(LOW, "MCU: Work complete\n");
    
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    csr_write_mpmc_halt();

}
