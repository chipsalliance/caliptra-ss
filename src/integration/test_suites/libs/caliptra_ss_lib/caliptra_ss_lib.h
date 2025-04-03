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
//

#ifndef CALIPTRA_SS_LIB
#define CALIPTRA_SS_LIB

#include "soc_address_map.h"
#include "stdint.h"
#include <stdbool.h>

extern uint32_t state;

typedef struct {
    // FW_SRAM_EXEC_REGION_SIZE
    bool cfg_mcu_fw_sram_exec_reg_size;
    uint32_t mcu_fw_sram_exec_reg_size;

    // CPTRA DMA AXI USER 
    bool cfg_cptra_dma_axi_user;
    uint32_t cptra_dma_axi_user;
    
    // MCU MBOX VALID USER 
    bool cfg_mcu_mbox0_valid_user;
    uint32_t *mcu_mbox0_valid_user;
    bool cfg_mcu_mbox1_valid_user;
    uint32_t *mcu_mbox1_valid_user;

    // SOC_IFC MBOX
    bool cfg_enable_cptra_mbox_user_init;

    // FUSE DONE
    bool cfg_skip_set_fuse_done;

} mcu_cptra_init_args;
// MAIN CPTRA INIT FUNCTION EVERYONE SHOULD USER 
// TO LOAD FUSES!!!
void mcu_cptra_init(mcu_cptra_init_args args);

uint32_t xorshift32(void);

inline void mcu_sleep (const uint32_t cycles) {
    for (uint8_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void reset_fc_lcc_rtl(void);
void mcu_cptra_wait_for_fuses() ;
void mcu_cptra_set_fuse_done() ;
void mcu_cptra_advance_brkpoint() ;
void mcu_set_fw_sram_exec_region_size(uint32_t size);
void mcu_set_cptra_dma_axi_user(uint32_t value);
void mcu_mci_boot_go();
void read_check(uintptr_t rdptr, uint32_t expected_rddata);
void mcu_mci_poll_exec_lock();
void mcu_mci_req_reset();
void mcu_cptra_user_init();
void mcu_cptra_poll_mb_ready();
void mcu_cptra_mbox_cmd();
void boot_mcu();
void boot_i3c_core(void);
void boot_i3c_socmgmt_if(void);
void boot_i3c_standby_ctrl_mode();
void boot_i3c_reg(void);
void mcu_mbox_clear_lock_out_of_reset(uint32_t mbox_num);
void mcu_mbox_update_status_complete(uint32_t mbox_num);
bool mcu_mbox_wait_for_user_lock(uint32_t mbox_num, uint32_t user_axi, uint32_t attempt_count);
bool mcu_mbox_wait_for_user_execute(uint32_t mbox_num, uint32_t attempt_count);
void mcu_mbox_configure_valid_axi(uint32_t mbox_num, uint32_t *axi_user_id);
bool mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count);
bool mcu_mbox_wait_for_user_to_be_mcu(uint32_t mbox_num, uint32_t attempt_count);
void mcu_mbox_clear_mbox_cmd_avail_interrupt(uint32_t mbox_num);
void write_read_check(uintptr_t rdptr, uint32_t data);
uintptr_t get_random_address(uint32_t rnd, uintptr_t start_address, uintptr_t end_address);

#define mcu_cptra_init_d(...) mcu_cptra_init((mcu_cptra_init_args){__VA_ARGS__});


#define TB_CMD_SHA_VECTOR_TO_MCU_SRAM   0x80

#define FC_LCC_CMD_OFFSET 0xB0
#define CMD_FC_LCC_RESET                FC_LCC_CMD_OFFSET + 0x02
#define CMD_FORCE_FC_AWUSER_CPTR_CORE   FC_LCC_CMD_OFFSET + 0x03
#define CMD_FORCE_FC_AWUSER_MCU         FC_LCC_CMD_OFFSET + 0x04
#define CMD_RELEASE_AWUSER              FC_LCC_CMD_OFFSET + 0x05
#define CMD_FC_FORCE_ZEROIZATION        FC_LCC_CMD_OFFSET + 0x06
#define CMD_FC_FORCE_ZEROIZATION_RESET  FC_LCC_CMD_OFFSET + 0x07
#define CMD_RELEASE_ZEROIZATION         FC_LCC_CMD_OFFSET + 0x08
#define CMD_FORCE_LC_TOKENS             FC_LCC_CMD_OFFSET + 0x09
#define CMD_LC_FORCE_RMA_SCRAP_PPD      FC_LCC_CMD_OFFSET + 0x0a
#define CMD_FC_TRIGGER_ESCALATION       FC_LCC_CMD_OFFSET + 0x0b

#define TB_DISABLE_MCU_SRAM_PROT_ASSERTS 0xC0


#define TB_CMD_DISABLE_INJECT_ECC_ERROR     0xe0
#define TB_CMD_INJECT_ECC_ERROR_SINGLE_DCCM 0xe2
#define TB_CMD_INJECT_ECC_ERROR_DOUBLE_DCCM 0xe3

#define MCU_MBOX_NUM_STRIDE             (SOC_MCI_TOP_MCU_MBOX1_CSR_BASE_ADDR - SOC_MCI_TOP_MCU_MBOX0_CSR_BASE_ADDR)
#define MCU_MBOX_AXI_CFG_STRIDE         (SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_0 - SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0)

#endif // CALIPTRA_SS_LIB
