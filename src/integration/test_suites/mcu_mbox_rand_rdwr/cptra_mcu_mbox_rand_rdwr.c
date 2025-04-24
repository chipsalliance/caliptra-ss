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
    uint32_t wdata_array[10];
    uint32_t dword_waddr[10];
    uint32_t dlen = 0;
    mbox_op_s op;

    uint32_t mbox_num = decode_single_valid_mbox();

    VPRINTF(LOW, "----------------------------------\nCaliptra: MCU Mbox Random Wr/Rd Test  !!\n----------------------------------\n", mbox_num);

    cptra_mcu_mbox_acquire_lock(mbox_num, 100000, true);

    uint32_t sram_size_kb = cptra_mcu_mbox_get_sram_size_kb(mbox_num);
    VPRINTF(LOW, "Caliptra: Mbox SRAM size in KB: %d\n", sram_size_kb);

    // Write at entry 0
    wr_data = xorshift32();
    cptra_mcu_mbox_write_dword_sram(mbox_num, 0, wr_data);

    rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, 0);
    if(rd_data != wr_data) {
        VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, 0, wr_data, rd_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Write at max size 
    wr_data = xorshift32();
    uint32_t max_size_dword = sram_size_kb * 1024/4;
    uint32_t max_addr_dword = max_size_dword - 1;
    cptra_mcu_mbox_write_dword_sram(mbox_num, max_addr_dword, wr_data);

    rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, max_addr_dword);
    if(rd_data != wr_data) {
        VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, max_addr_dword, wr_data, rd_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Write Dlen
    cptra_mcu_mbox_write_dlen(mbox_num, 1);
    cptra_mcu_mbox_write_execute(mbox_num, 0x1);
    cptra_mcu_mbox_write_execute(mbox_num, 0x0);
    cptra_mcu_mbox_acquire_lock(mbox_num, 1000000, true);

    rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, 0);
    if(rd_data != 0) {
        VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, 0, 0, rd_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    for(uint32_t i=0; i<10; i++) {
        wdata_array[i] = xorshift32();
        dword_waddr[i] = mcu_mbox_gen_rand_dword_addr(mbox_num, 0, sram_size_kb);

        if ((dword_waddr[i] + 1) * 4 > dlen) {
            dlen = (dword_waddr[i] + 1) * 4;
            VPRINTF(LOW, "CALIPTRA: Mbox%x current max DLEN: 0x%x\n", mbox_num, dlen);
        }
        cptra_mcu_mbox_write_dword_sram(mbox_num, dword_waddr[i], wdata_array[i]);
    }

    for(uint32_t i=0; i<10; i++) {
        rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, dword_waddr[i]);
        if(rd_data != wdata_array[i]) {
            VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, dword_waddr[i], wdata_array[i], rd_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    // Write Dlen
    // Clear execute and re-acquire lock
    // Check that data at written locations is 0'ed out
    // Subtract a value from 0-3 from dlen to check that non-4 byte aligned dlen still 0 the whole dword
    cptra_mcu_mbox_write_dlen(mbox_num, dlen - (xorshift32() % 4));
    cptra_mcu_mbox_write_execute(mbox_num, 0x1);
    cptra_mcu_mbox_write_execute(mbox_num, 0x0);
    cptra_mcu_mbox_acquire_lock(mbox_num, 1000000, true);

    for(uint32_t i=0; i<10; i++) {
        rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, dword_waddr[i]);
        if(rd_data != 0) {
            VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, dword_waddr[i], 0, rd_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    // Write at max size 
    wr_data = xorshift32();
    max_size_dword = sram_size_kb * 1024/4;
    max_addr_dword = max_size_dword - 1;
    cptra_mcu_mbox_write_dword_sram(mbox_num, max_addr_dword, wr_data);

    rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, max_addr_dword);
    if(rd_data != wr_data) {
        VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, max_addr_dword, wr_data, rd_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    // Set and Clear execute and re-acquire lock
    // Check that data at written locations is 0'ed out
    cptra_mcu_mbox_write_dlen(mbox_num, sram_size_kb * 1024);
    cptra_mcu_mbox_write_execute(mbox_num, 0x1);
    cptra_mcu_mbox_write_execute(mbox_num, 0x0);
    cptra_mcu_mbox_acquire_lock(mbox_num, 1000000, true);

    rd_data = cptra_mcu_mbox_read_dword_sram(mbox_num, max_addr_dword);
    if(rd_data != 0) {
        VPRINTF(FATAL, "CALIPTRA: MBOX%x SRAM data mismatch at SRAM[%d]: expected 0x%x, actual 0x%x\n", mbox_num, max_addr_dword, 0, rd_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

    SEND_STDOUT_CTRL(0xFF);
    while(1);
}
