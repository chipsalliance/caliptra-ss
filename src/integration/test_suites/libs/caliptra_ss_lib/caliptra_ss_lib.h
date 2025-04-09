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
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "stdint.h"
#include <stdbool.h>

#define TB_CMD_SHA_VECTOR_TO_MCU_SRAM   0x80

#define FC_LCC_CMD_OFFSET 0x90
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
#define CMD_FC_LCC_EXT_CLK_500MHZ       FC_LCC_CMD_OFFSET + 0x0c
#define CMD_FC_LCC_EXT_CLK_160MHZ       FC_LCC_CMD_OFFSET + 0x0d
#define CMD_FC_LCC_EXT_CLK_400MHZ       FC_LCC_CMD_OFFSET + 0x0e
#define CMD_FC_LCC_EXT_CLK_1000MHZ      FC_LCC_CMD_OFFSET + 0x0f
#define CMD_FC_LCC_FAULT_DIGEST         FC_LCC_CMD_OFFSET + 0x10
#define CMD_FC_LCC_FAULT_BUS_ECC        FC_LCC_CMD_OFFSET + 0x11
#define CMD_LC_TRIGGER_ESCALATION0      FC_LCC_CMD_OFFSET + 0x12
#define CMD_LC_TRIGGER_ESCALATION1      FC_LCC_CMD_OFFSET + 0x13
#define TB_CMD_DISABLE_MCU_SRAM_PROT_ASSERTS 0xC0

#define TB_CMD_DISABLE_INJECT_ECC_ERROR     0xe0
#define TB_CMD_INJECT_ECC_ERROR_SINGLE_DCCM 0xe2
#define TB_CMD_INJECT_ECC_ERROR_DOUBLE_DCCM 0xe3



#define MCU_MBOX_NUM_STRIDE             (SOC_MCI_TOP_MCU_MBOX1_CSR_BASE_ADDR - SOC_MCI_TOP_MCU_MBOX0_CSR_BASE_ADDR)
#define MCU_MBOX_AXI_CFG_STRIDE         (SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_0 - SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0)
#define MCU_MBOX_MAX_SIZE_KB            2048
#define MCU_MBOX_MAX_NUM                2

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
#define mcu_cptra_init_arg_defaults           \
    /* FW_SRAM_EXEC_REGION_SIZE */            \
    .cfg_mcu_fw_sram_exec_reg_size   = false, \
    .mcu_fw_sram_exec_reg_size       = 0,     \
    /* CPTRA DMA AXI USER */                  \
    .cfg_cptra_dma_axi_user          = false, \
    .cptra_dma_axi_user              = 0,     \
    /* MCU MBOX VALID USER */                 \
    .cfg_mcu_mbox0_valid_user        = false, \
    .mcu_mbox0_valid_user            = 0,     \
    .cfg_mcu_mbox1_valid_user        = false, \
    .mcu_mbox1_valid_user            = 0,     \
    /* SOC_IFC MBOX */                        \
    .cfg_enable_cptra_mbox_user_init = false, \
    /* FUSE DONE */                           \
    .cfg_skip_set_fuse_done          = false

// MAIN CPTRA INIT FUNCTION EVERYONE SHOULD USER 
// TO LOAD FUSES!!!
void mcu_cptra_init(mcu_cptra_init_args args);
#define mcu_cptra_init_d(...) mcu_cptra_init((mcu_cptra_init_args){mcu_cptra_init_arg_defaults __VA_OPT__(,) __VA_ARGS__});

uint32_t xorshift32(void);

// Bitfield indicating which MCU Mboxes are valid for the given test
extern uint32_t valid_mbox_instances;
uint32_t decode_single_valid_mbox(void);

inline void mcu_sleep (const uint32_t cycles) {
    for (uint32_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

enum mcu_mbox_cmd_status {
    MCU_MBOX_CMD_BUSY        = 0x0,
    MCU_MBOX_DATA_READY      = 0x1,
    MCU_MBOX_CMD_COMPLETE    = 0x2,
    MCU_MBOX_CMD_FAILURE     = 0x3
};
enum mcu_mbox_target_status{
    MCU_MBOX_TARGET_STATUS_CMD_BUSY = 0x0,
    MCU_MBOX_TARGET_STATUS_READY    = 0x1,
    MCU_MBOX_TARGET_STATUS_COMPLETE = 0x2,
    MCU_MBOX_TARGET_STATUS_FAILURE  = 0x3
};

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
bool mcu_mbox_wait_for_user_execute(uint32_t mbox_num, uint32_t expected_value, uint32_t attempt_count);
void mcu_mbox_configure_valid_axi(uint32_t mbox_num, uint32_t *axi_user_id);
uint32_t mcu_mbox_generate_invalid_axi(uint32_t *axi_user_id);
bool mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count);
bool mcu_mbox_wait_for_user_to_be_mcu(uint32_t mbox_num, uint32_t attempt_count);
void mcu_mbox_clear_mbox_cmd_avail_interrupt(uint32_t mbox_num);
void write_read_check(uintptr_t rdptr, uint32_t data);
uintptr_t get_random_address(uint32_t rnd, uintptr_t start_address, uintptr_t end_address);
void mcu_mbox_clear_soc_req_while_mcu_lock_interrupt(uint32_t mbox_num);
bool is_mcu_mbox_clear_soc_req_while_mcu_lock_interrupt_set(uint32_t mbox_num);
bool mcu_mbox_wait_for_soc_req_while_mcu_lock_interrupt(uint32_t mbox_num, uint32_t attempt_count);
bool mcu_mbox_wait_for_target_status_done(uint32_t mbox_num, enum mcu_mbox_target_status status, uint32_t attempt_count);
bool is_mcu_mbox_target_done_interrupt_set(uint32_t mbox_num);
void mcu_mbox_clear_target_done_interrupt(uint32_t mbox_num);
uint32_t mcu_mbox_get_sram_size_kb(uint32_t mbox_num);
uint32_t mcu_mbox_gen_rand_dword_addr(uint32_t mbox_num, uint32_t sram_size_kb, uint32_t max_size_kb);

///////////////////////////////////////////////////
// MCU Mbox Read/Write SRAM and CSR functions
////////////////////////////////////////////////////
inline void mcu_mbox_clear_execute(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: Clearing MBOX%x Execute\n", mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0x0);
}

inline void mcu_mbox_set_execute(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: Setting MBOX%x Execute\n", mbox_num);
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0x1);
}

inline void mcu_mbox_write_cmd(uint32_t mbox_num, uint32_t cmd) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x command: 0%x\n", mbox_num, cmd); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, cmd);
}
inline uint32_t mcu_mbox_read_cmd(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading CMD: 0x%x\n", mbox_num, rd_data); 
    return rd_data;
}
inline void mcu_mbox_write_dlen(uint32_t mbox_num, uint32_t dlen) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x DLEN: 0x%x\n", mbox_num, dlen); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, dlen);
}

inline uint32_t mcu_mbox_read_dlen(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading DLEN: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}
inline void mcu_mbox_write_cmd_status(uint32_t mbox_num, enum mcu_mbox_cmd_status cmd_status) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x CMD_STATUS: 0%x\n", mbox_num, cmd_status); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, (cmd_status & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK));    
}

inline uint32_t mcu_mbox_read_cmd_status(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading CMD_STATUS: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline uint32_t mcu_mbox_read_mbox_user(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading USER: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline uint32_t mcu_mbox_read_lock(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading LOCK: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline uint32_t mcu_mbox_read_hw_status(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading HW_STATUS: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline void mcu_mbox_write_sram_dword(uint32_t mbox_num, uint32_t dword_addr, uint32_t data) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x data: 0x%x\n", mbox_num, data); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

inline uint32_t mcu_mbox_read_sram_dword(uint32_t mbox_num, uint32_t dword_addr) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading SRAM: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline void mcu_mbox_write_target_user(uint32_t mbox_num, uint32_t axi_id) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x TARGET_USER: 0%x\n", mbox_num, axi_id); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, axi_id);    
}

inline uint32_t mcu_mbox_read_target_user(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading TARGET_USER: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

inline void mcu_mbox_write_target_user_valid(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "MCU: Writing to MBOX%x TARGET_USER_VALID: 0x%x\n", mbox_num, data); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, (data & MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK));    
}

inline uint32_t mcu_mbox_read_target_user_valid(uint32_t mbox_num) {
    uint32_t rd_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "MCU: Mbox%x Reading TARGET_USER_VALID: 0x%x\n", mbox_num, rd_data);
    return rd_data;
}

#endif // CALIPTRA_SS_LIB
