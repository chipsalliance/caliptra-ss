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
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "caliptra_ss_lib.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


void main(void) {
    int argc=0;
    char *argv[1];
    uint32_t reg;
    uint32_t wr_data;
    uint32_t rd_data;
    uint32_t wrdata_array[10];
    uint32_t rddata_array[10];
    uint32_t dword_waddr;
    uint32_t dlen = 0;
    mbox_op_s op;

    uint32_t mbox_num = decode_single_valid_mbox();

    VPRINTF(LOW, "----------------------------------\nCaliptra: MCU Mbox Burst Write/Read Test  !!\n----------------------------------\n", mbox_num);


    uint32_t sram_size_kb = cptra_mcu_mbox_get_sram_size_kb(mbox_num);
    VPRINTF(LOW, "Caliptra: Mbox SRAM size in KB: %d\n", sram_size_kb);

    cptra_mcu_mbox_acquire_lock(mbox_num, 100000, true);

    for(uint32_t i=0; i<2; i++) {

        dword_waddr = mcu_mbox_gen_rand_dword_addr(mbox_num, 0, sram_size_kb);
        uint32_t max_dword_burst_addr = (sram_size_kb * 1024 / 4) - 1 - sizeof(wrdata_array)/4;
        if (dword_waddr > max_dword_burst_addr) {
            dword_waddr = max_dword_burst_addr;
        }
           
        VPRINTF(LOW, "CALIPTRA: Mbox%x generating data for burst write\n", mbox_num);

        for(uint32_t i=0; i<10; i++) {
            wrdata_array[i] = xorshift32();
            VPRINTF(LOW, "CALIPTRA: Mbox%x data payload SRAM[%d]: 0x%x\n", mbox_num, dword_waddr + i, wrdata_array[i]);
        }

        dlen = (dword_waddr * 4) + sizeof(wrdata_array);
        VPRINTF(LOW, "CALIPTRA: Mbox%x current max DLEN: 0x%x\n", mbox_num, dlen);

        cptra_mcu_mbox_write_dword_sram_burst(mbox_num, dword_waddr, wrdata_array, sizeof(wrdata_array), 0);

        // Do burst read and check that data is correct
        cptra_mcu_mbox_read_dword_sram_burst(mbox_num, dword_waddr, &rddata_array, sizeof(wrdata_array), 0);
        for(uint32_t i=0; i<10; i++) {
            VPRINTF(LOW, "CALIPTRA: Mbox%x data payload SRAM[%d]: 0x%x\n", mbox_num, dword_waddr + i, rddata_array[i]);
            if(rddata_array[i] != wrdata_array[i]) {
                VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, dword_waddr + i, wrdata_array[i], rddata_array[i]);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        // Write Dlen
        // Clear execute and re-acquire lock
        // Check that data at written locations is 0'ed out
        cptra_mcu_mbox_write_dlen(mbox_num, dlen);
        cptra_mcu_mbox_write_execute(mbox_num, 0x1);
        cptra_mcu_mbox_write_execute(mbox_num, 0x0);
        cptra_mcu_mbox_acquire_lock(mbox_num, 1000000, true);

        // Do burst read and check that data is 0
        cptra_mcu_mbox_read_dword_sram_burst(mbox_num, dword_waddr, &rddata_array, sizeof(wrdata_array), 0);
        for(uint32_t i=0; i<10; i++) {
            VPRINTF(LOW, "CALIPTRA: Mbox%x data payload SRAM[%d]: 0x%x\n", mbox_num, dword_waddr + i, rddata_array[i]);
            if(rddata_array[i] != 0) {
                VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, dword_waddr + i, 0, rddata_array[i]);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }
    }

    VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

    SEND_STDOUT_CTRL(0xFF);
    while(1);
}
