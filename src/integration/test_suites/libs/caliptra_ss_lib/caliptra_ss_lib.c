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

#include "soc_address_map.h"
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "riscv_hw_if.h"
#include "string.h"
#include "caliptra_ss_clk_freq.h"
#include "caliptra_ss_lib.h"
#include <stdbool.h>
#include <stdarg.h> // For va_list, va_start, va_end

#ifdef MCU_MBOX_VALID_VECTOR
    uint32_t valid_mbox_instances = MCU_MBOX_VALID_VECTOR;
#else
    uint32_t valid_mbox_instances = 0;
#endif

#ifdef CFG_CALIPTRA_AXI_WITH_PARAM
    uint32_t cfg_caliptra_axi_with_param = CFG_CALIPTRA_AXI_WITH_PARAM;
#else
    uint32_t cfg_caliptra_axi_with_param = 0;
#endif

#ifdef MY_RANDOM_SEED
    uint32_t state = (unsigned) MY_RANDOM_SEED;
#else
    uint32_t state = 0;
#endif

void handle_error(const char *format, ...) {
    va_list args;
    va_start(args, format);
    VPRINTF(FATAL, format, args); // Pass the variable arguments to VPRINTF
    va_end(args);

    SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    while (1); // Infinite loop to halt execution
}

uint32_t xorshift32(void)
{
    state ^= state << 13;
    state ^= state >> 17;
    state ^= state << 5;
    return state;
}

void reset_fc_lcc_rtl(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_LCC_RESET);
    VPRINTF(LOW, "LCC & Fuse_CTRL is under reset!\n");
    mcu_sleep(160);
}

void write_read_check(uintptr_t rdptr, uint32_t data){
    VPRINTF(LOW, "write_read_check: Address: 0x%x -- Data: 0x%x\n", rdptr, data);

    lsu_write_32(rdptr, data);

    read_check(rdptr, data);
    
}

uintptr_t get_random_address(uint32_t rnd, uintptr_t start_address, uintptr_t end_address) {
    // Return address that is DWORD aligned
    uintptr_t range = end_address - start_address + 1;
    uintptr_t offset = rnd % range;
    uintptr_t address = (start_address + offset) & ~3;
    return address;
}

void read_check(uintptr_t rdptr, uint32_t expected_rddata){
    uint32_t data;
    data = lsu_read_32(rdptr);
    VPRINTF(LOW, "read_check: Address: 0x%x -- Expected: 0x%x Actual: 0x%x\n", rdptr, expected_rddata, data);
    if (expected_rddata != data) {
        VPRINTF(FATAL, "MCU: FATAL - read_check: Data mismatch at address: 0x%x -- Expected: 0x%x Actual: 0x%x\n", rdptr, expected_rddata, data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void mcu_set_fw_sram_exec_region_size(uint32_t size) {
    VPRINTF(LOW, "MCU: Configure EXEC REGION Size 0x%x\n", size);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE , size);
}


void mcu_set_cptra_dma_axi_user(uint32_t value) {
    VPRINTF(LOW, "MCU: Configure CPTRA DMA AXI USER 0x%x\n", value);
    lsu_write_32(SOC_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER, value);
}

void mcu_mci_boot_go() {
    // writing SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO register of MCI for CPTRA Boot FSM to bring Caliptra out of reset
    uint32_t cptra_boot_go;
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
}

void mcu_mci_poll_exec_lock() {
    uint32_t rg;
    uint32_t cnt = 0;
    do {
        mcu_sleep(64);
        if (!(cnt++ & 0xf)) {
            VPRINTF(MEDIUM, " * poll ex lk %x\n", cnt);
        }
        rg = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK;
    } while(rg != MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK);
}

void mcu_mci_req_reset() {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_RESET_REQUEST, MCI_REG_RESET_REQUEST_MCU_REQ_MASK);
}

void mcu_cptra_wait_for_fuses() {
    // Wait for ready_for_fuses
    VPRINTF(LOW, "MCU: Wait for CPTRA FLOW STATUS to indicate ready for fuses \n");
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));
    VPRINTF(LOW, "MCU: Caliptra is ready for fuses\n");
}

void mcu_cptra_set_fuse_done() {
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
}

void mcu_cptra_advance_brkpoint() {
    enum boot_fsm_state_e boot_fsm_ps;
    
    VPRINTF(LOW, "MCU: Waiting for CPTRA BOOT_DONE or BOOT_WAIT\n");
    // Wait for Boot FSM to stall (on breakpoint) or finish bootup
    boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    while(boot_fsm_ps != BOOT_DONE && boot_fsm_ps != BOOT_WAIT) {
        mcu_sleep(16);
        boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    }

    // Advance from breakpoint, if set
    if (boot_fsm_ps == BOOT_WAIT) {
        VPRINTF(LOW, "MCU: CPTRA BOOT_WAIT setting BootFSM GO\n");
        lsu_write_32(SOC_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);
    }

    VPRINTF(LOW, "MCU: CPTRA FSM in BOOT_DONE\n");

}

void mcu_cptra_user_init() {
    uint32_t mcu_lsu_axi_user = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_LSU_AXI_USER);
    // MBOX: Setup valid AXI USER
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, mcu_lsu_axi_user);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1, 1);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2, 2);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, 3);
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2_LOCK_MASK);
//    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3_LOCK_MASK);
    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");

}

void mcu_cptra_init(mcu_cptra_init_args args) {
    // DO NOT CALL DIRECTLY. USE THE mcu_cptra_init_d MACRO TO CALL THE FUNCTION
    
    // 4 MAIN OPTIONS:
    //
    // 1. Always disabled unless a new value is specified:
    //    - Add a boolean cfg_<feature>.
    //    - Add a <type> <feature_value>.
    //    - Skip configuration unless cfg_<feature> is set, then set the <feature_value>.
    //    - Use for features that most tests don't care about and will have a set value.
    //
    // 2. Always disabled unless enabled:
    //    - Add a boolean cfg_enable_<feature>.
    //    - Skip configuration unless cfg_enable_<feature> is set, then enable the feature.
    //    - Use for features that most tests don't care about and don't have an actual 
    //      value but when enabled will initiate a configuration within the design.
    //
    // 3. Always enabled unless specified:
    //    - Add a cfg_skip_<feature>.
    //    - Always program the register unless the skip is set.
    //    - Use when most tests want the feature
    //    - Use for features that are either DO or SKIP.
    //
    // 4. Always enabled unless overridden:
    //    - Add a cfg_override_<feature>.
    //    - Add a <feature_value>.
    //    - Use when most tests want the feature.
    //    - Always configure to a default value. If cfg_override_<feature> is set, 
    //      write the <feature_value> into the register.

    

    VPRINTF(LOW, "MCU: INIT CONFIGURING START\n");
    
    /////////////////////////////////
    // MCU CONFIGURATION
    /////////////////////////////////
    if (args.cfg_mcu_fw_sram_exec_reg_size) {
        VPRINTF(LOW, "MCU: args.mcu_fw_sram_exec_reg_size 0x%x\n", args.mcu_fw_sram_exec_reg_size);
        mcu_set_fw_sram_exec_region_size(args.mcu_fw_sram_exec_reg_size); 
    }

    if (args.cfg_mcu_mbox0_valid_user) {
        mcu_mbox_configure_valid_axi(0, args.mcu_mbox0_valid_user);
    }

    if (args.cfg_mcu_mbox1_valid_user) {
        mcu_mbox_configure_valid_axi(1, args.mcu_mbox1_valid_user);
    }

    /////////////////////////////////
    // BRING CPTRA OUT OF RESET
    /////////////////////////////////
    mcu_mci_boot_go();    

    mcu_cptra_wait_for_fuses();

    /////////////////////////////////
    // CPTRA FUSE CONFIGURATION
    /////////////////////////////////
    if (args.cfg_cptra_dma_axi_user){
        mcu_set_cptra_dma_axi_user(args.cptra_dma_axi_user);
    }

    if (args.cfg_enable_cptra_mbox_user_init){
        mcu_cptra_user_init();
    }

    /////////////////////////////////
    // CPTRA LOCK FUSE CONFIGURATION
    /////////////////////////////////

    // enable only to program fuses.
    if(args.cfg_cptra_fuse){
        update_cptra_fuse_cfg();
        update_pqc_key_type(); //-- FIXME : should have separate config
    }
    // enabled by default to indicate that fuses are done.
    if (!args.cfg_skip_set_fuse_done) {
        mcu_cptra_set_fuse_done();
    }
    else{
        VPRINTF(LOW, "MCU: INIT CONFIGURING: Skip Set fuse done\n");
    }

    ///////////////////////////////
    // CPTRA WDT CONFIGURATION
    ///////////////////////////////
    if (args.cfg_cptra_wdt) {
        update_cptra_wdt_cfg(1000, 250, 0);
    }
    else{
        VPRINTF(LOW, "MCU: INIT CONFIGURING: Skip CPTRA WDT\n");
    }

    /////////////////////////////////
    // BOOT I3C
    /////////////////////////////////
    if (args.cfg_boot_i3c_core) {
        boot_i3c_core();
    }
    else{
        VPRINTF(LOW, "MCU: Skipping I3C Core boot\n");
    }


    /////////////////////////////////
    // CPTRA ENSURE BREAKPOINT SET  
    /////////////////////////////////
    if (!args.cfg_skip_set_fuse_done) {
        mcu_cptra_advance_brkpoint();
    }
    else{
        VPRINTF(LOW, "MCU: INIT CONFIGURING: Skip advance CPTRA advance breakpoint\n");
    }

    /////////////////////////////////
    // TRIGGER PROD ROM
    /////////////////////////////////
    if (args.cfg_trigger_prod_rom) {
        mcu_cptra_poll_mb_ready();
        cptra_prod_rom_boot_go();
    } 
    else {
        VPRINTF(LOW, "MCU: INIT CONFIGURING: Skip Trigger Prod ROM\n");
    }


    VPRINTF(LOW, "MCU: INIT CONFIGURING END\n");
}


void mcu_mbox_clear_lock_out_of_reset(uint32_t mbox_num) {
    // MBOX: Write DLEN  (normally would be max SRAM size but using smaller size for test run time)
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE*mbox_num, 32);

    // MBOX: Clear Execute
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE*mbox_num, 0);
    VPRINTF(LOW, "MCU: Mbox%x execute clear\n", mbox_num);
    
    VPRINTF(LOW, "MCU: Mbox%x Lock out of reset cleared\n", mbox_num);
}

void mcu_mbox_update_status(uint32_t mbox_num, enum mcu_mbox_cmd_status status) {
    // MBOX: Write status
    VPRINTF(LOW, "MCU: Writing to MBOX%x status: 0x%x\n", mbox_num, status); 
    lsu_write_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE*mbox_num, status);
}

bool mcu_mbox_wait_for_user_lock(uint32_t mbox_num, uint32_t user_axi, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra to acquire the lock in mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num) == user_axi){
            VPRINTF(LOW, "MCU: Caliptra acquired Mbox%x lock\n", mbox_num);
            return true;
        }
    } 
    return false;
}

bool mcu_mbox_wait_for_user_execute(uint32_t mbox_num, uint32_t expected_value, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra to set execute in mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num) == expected_value){
            VPRINTF(LOW, "MCU: Caliptra set execute for Mbox%x\n", mbox_num);

            // Check that Mailbox cmd available from SOC interrupt has been set
            if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
                (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) == 0) {
                VPRINTF(FATAL, "MCU: Mbox%x Mailbox cmd available from SoC interrupt not set\n", mbox_num);
                SEND_STDOUT_CTRL(0x1);
                while(1);
                }
            return true;
        }
    }
    return false;
}

void mcu_mbox_clear_mbox_cmd_avail_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C cmd available interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    internal_intr |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox cmd available from SOC interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) == 1) {
        VPRINTF(FATAL, "MCU: Mbox%x Mailbox cmd available from SoC interrupt not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void mcu_mbox_clear_soc_req_while_mcu_lock_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C SoC req while MCU lock interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    internal_intr = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox cmd available from SOC interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK << mbox_num)) == 1) {
        VPRINTF(FATAL, "MCU: Mbox%x SoC req while MCU lock interrupt not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

bool mcu_mbox_wait_for_soc_req_while_mcu_lock_interrupt(uint32_t mbox_num, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra to attempt a lock while MCU has locked mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(is_mcu_mbox_clear_soc_req_while_mcu_lock_interrupt_set(mbox_num)){
            VPRINTF(LOW, "MCU: Caliptra attempted a lock while MCU has locked mbox%x\n", mbox_num);
            return true;
        }
    }
    return false;
}

bool is_mcu_mbox_clear_soc_req_while_mcu_lock_interrupt_set(uint32_t mbox_num) {
    // Check that Mailbox SoC req while MCU lock interrupt has been set
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK << mbox_num)) != 0) {
            VPRINTF(LOW, "MCU: Mbox%x SoC req while MCU lock interrupt set\n", mbox_num);
            return true;
    }
    return false;
}

bool mcu_mbox_wait_for_soc_data_avail_interrupt(uint32_t mbox_num, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for SoC data available interrupt for mbox%x\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(is_mcu_mbox_soc_data_avail_interrupt_set(mbox_num)){
            VPRINTF(LOW, "MCU: SoC agent data available for mbox%x\n", mbox_num);
            return true;
        }
    }
    return false;
}

bool is_mcu_mbox_soc_data_avail_interrupt_set(uint32_t mbox_num) {
    // Check that Mailbox SoC data available interrupt has been set
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) != 0) {
            VPRINTF(LOW, "MCU: Mbox%x SoC data available interrupt set\n", mbox_num);
            return true;
    }
    return false;
}

void clear_mcu_mbox_soc_data_avail_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C SoC data available interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    internal_intr = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox SoC data available interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK << mbox_num)) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x SoC data available interrupt not cleared\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
    }
}

bool is_only_mcu_mbox_sb_ecc_interrupt_set(uint32_t mbox_num) {
    // Check that Mailbox SB ECC interrupt has been set
    if(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) ==
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK << mbox_num)) {
            VPRINTF(LOW, "MCU: Mbox%x SB ECC interrupt set\n", mbox_num);
            return true;
    }
    return false;
}

bool is_only_mcu_mbox_db_ecc_interrupt_set(uint32_t mbox_num) {
    // Check that Mailbox DB ECC interrupt has been set
    if(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) == 
        (MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK << mbox_num)) {
            VPRINTF(LOW, "MCU: Mbox%x DB ECC interrupt set\n", mbox_num);
            return true;
    }
    return false;
}

void clear_mcu_mbox_clear_sb_ecc_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C SB ECC interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    internal_intr = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox SB ECC interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK << mbox_num)) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x SB ECC interrupt not cleared\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
    }
}

void clear_mcu_mbox_clear_db_ecc_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C DB ECC interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R);
    internal_intr = MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox DB ECC interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK << mbox_num)) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x DB ECC interrupt not cleared\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
    }
}

void mcu_mbox_configure_valid_axi(uint32_t mbox_num, uint32_t *axi_user_id) {
    
    VPRINTF(LOW, "MCU: Configuring Valid AXI USERs in Mbox%x:  0 - 0x%x; 1 - 0x%x; 2 - 0x%x; 3 - 0x%x; 4 - 0x%x;\n", mbox_num, axi_user_id[0], axi_user_id[1], axi_user_id[2], axi_user_id[3], axi_user_id[4]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[0]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[1]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[2]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[3]);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, axi_user_id[4]);

    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_MASK);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4 + MCU_MBOX_AXI_CFG_STRIDE*mbox_num, MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_MASK);
    VPRINTF(LOW, "MCU: DONE Configuring Valid AXI USERs in Mbox%x\n", mbox_num);

}

// Generate AXI that is guaranteed to not be in axi_user_id
uint32_t mcu_mbox_generate_invalid_axi(uint32_t *axi_user_id) {
    bool is_unique;
    uint32_t caliptra_uc_axi_id;
    do {
        is_unique = true;
        caliptra_uc_axi_id = xorshift32(); // Generate a new value

        // Check if the generated value matches any in axi_user_id
        for (size_t i = 0; i < sizeof(axi_user_id) / sizeof(axi_user_id[0]); i++) {
            if (caliptra_uc_axi_id == axi_user_id[i]) {
                is_unique = false; // Not unique, try again
                return caliptra_uc_axi_id;
            }
        }
    } while (!is_unique);
}

bool mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for Mbox%x lock acquired\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(!(lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK)){
            VPRINTF(LOW, "MCU: Mbox%x lock acquired\n", mbox_num);
            return true;
        }
    }
    return false;
}

bool mcu_cptra_mbox_acquire_lock(uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for CPTRA Mbox lock acquired\n");
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(!(lsu_read_32(SOC_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK)){
            VPRINTF(LOW, "MCU: CPTRA Mbox lock acquired\n");
            return true;
        }
    }
    return false;
}

bool mcu_cptra_mbox_wait_for_status(uint32_t attempt_count, enum mbox_status_e status) {
    VPRINTF(LOW, "MCU: Waiting for CPTRA Mbox status: 0x%x\n", status);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        uint32_t reg_data = lsu_read_32(SOC_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK;
        if(reg_data == status){
            VPRINTF(LOW, "MCU: CPTRA Mbox status: 0x%x\n", status);
            return true;
        }
    }
    return false;
}

bool mcu_wait_for_mcu_reset_req_interrupt(uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for CPTRA MCU Reset Request interrupt\n");
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if(lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK){
            VPRINTF(LOW, "MCU: CPTRA MCU Reset Request interrupt set\n");
            return true;
        }
    }
    return false;
}

bool mcu_mbox_wait_for_user_to_be_mcu(uint32_t mbox_num, uint32_t attempt_count) {
    // TODO: update with MCU Root Strap Value
    VPRINTF(LOW, "MCU: Wait for Lock to Reflect MBOX USER\n");
    uint32_t mbox_resp_data;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        mbox_resp_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
        if(mbox_resp_data != 0){
            VPRINTF(LOW, "MCU: MBOX%x USER = %x\n", mbox_num, mbox_resp_data);
            return true;
        }
    }
    return false;
}

bool mcu_mbox_wait_for_target_status_done(uint32_t mbox_num, enum mcu_mbox_target_status status, uint32_t attempt_count) {
    VPRINTF(LOW, "MCU: Waiting for caliptra (as TARGET USER) to set TARGET_STATUS DONE with completion code: 0x%x (%x\n", status, mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        uint32_t reg_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num);
        bool target_done = (reg_data & MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK) != 0;
        reg_data = (reg_data & MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_MASK) >> MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_LOW;
        if(target_done & (reg_data == status)){
            VPRINTF(LOW, "MCU: Caliptra (as TARGET USER) set TARGET_STATUS DONE with completion code: 0x%x (%x\n", status, mbox_num);
            return true;
        }
    }
    return false;
}

bool is_mcu_mbox_target_done_interrupt_set(uint32_t mbox_num) {
    // Check that Mailbox Target Done interrupt has been set
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK << mbox_num)) != 0) {
            VPRINTF(LOW, "MCU: Mbox%x Target Done interrupt set\n", mbox_num);
            return true;
    }
    return false;
}

void mcu_mbox_clear_target_done_interrupt(uint32_t mbox_num) {
    VPRINTF(LOW, "MCU: RW1C Target Done interrupt Mbox%x\n", mbox_num);
    uint32_t internal_intr = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK << mbox_num;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox Target Done interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        (MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK << mbox_num)) != 0) {
        VPRINTF(FATAL, "MCU: Mbox%x Target Done interrupt not cleared\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void mcu_clear_reset_req_interrupt() {
    VPRINTF(LOW, "MCU: RW1C Reset Request interrupt\n");
    uint32_t internal_intr = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK;
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, internal_intr);

    // Check that Mailbox Target Done interrupt has been cleared
    if((lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & 
        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK) != 0) {
        VPRINTF(FATAL, "MCU: Reset Request interrupt not cleared\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Returns mbox number based on valid mbox instance bitfield
// Assumes one-hot
// Default to mbox0 if multiple selected
uint32_t decode_single_valid_mbox(void) {
    uint32_t mbox_num = 0;
    VPRINTF(LOW, "Valid MBOX Vector: 0x%x\n", valid_mbox_instances);
    if (valid_mbox_instances == 0x2) {
        mbox_num = 1;
    }
    return mbox_num;
}

bool is_caliptra_axi_param(void) {
    return (cfg_caliptra_axi_with_param == 1);
}

uint32_t mcu_mbox_get_sram_size_kb(uint32_t mbox_num) {
    uint32_t data;
    uint32_t mask = MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK << ((MCU_MBOX_MAX_NUM-1 - mbox_num) * MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW);
    data = lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_CONFIG0) & mask;
    data = data >> ((MCU_MBOX_MAX_NUM-1 - mbox_num) * MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW);
    return data;
}

uint32_t mcu_mbox_gen_rand_dword_addr(uint32_t mbox_num, uint32_t min_kb, uint32_t max_kb) {
    uint32_t min_size = min_kb * 1024/4;
    uint32_t max_size = max_kb * 1024/4;
    uint32_t rand_addr = ((xorshift32() % (max_size - min_size)) + min_size);
    return rand_addr;
}

void mcu_cptra_poll_mb_ready() {
    // MBOX: Wait for ready_for_mb_processing
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK)) {
        mcu_sleep(16);
    }
    VPRINTF(LOW, "MCU: Ready for FW\n");
}

void mcu_cptra_mbox_cmd() {
    const uint32_t mbox_dlen = 64;
    uint32_t mbox_data[] = { 0x00000000,
                             0x11111111,
                             0x22222222,
                             0x33333333,
                             0x44444444,
                             0x55555555,
                             0x66666666,
                             0x77777777,
                             0x88888888,
                             0x99999999,
                             0xaaaaaaaa,
                             0xbbbbbbbb,
                             0xcccccccc,
                             0xdddddddd,
                             0xeeeeeeee,
                             0xffffffff };
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;

    // MBOX: Acquire lock
    while((lsu_read_32(SOC_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox lock acquired\n");

    // MBOX: Write CMD
    lsu_write_32(SOC_MBOX_CSR_MBOX_CMD, 0xFADECAFE | MBOX_CMD_FIELD_RESP_MASK); // Resp required

    // MBOX: Write DLEN
    lsu_write_32(SOC_MBOX_CSR_MBOX_DLEN, 64);

    // MBOX: Write datain
    for (uint32_t ii = 0; ii < mbox_dlen/4; ii++) {
        lsu_write_32(SOC_MBOX_CSR_MBOX_DATAIN, mbox_data[ii]);
    }

    // MBOX: Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox execute\n");

    // MBOX: Poll status
    while(((lsu_read_32(SOC_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> MBOX_CSR_MBOX_STATUS_STATUS_LOW) != DATA_READY) {
        mcu_sleep(16);
    }
    VPRINTF(LOW, "MCU: Mbox response ready\n");

    // MBOX: Read response data length
    mbox_resp_dlen = lsu_read_32(SOC_MBOX_CSR_MBOX_DLEN);

    // MBOX: Read dataout
    for (uint32_t ii = 0; ii < (mbox_resp_dlen/4 + (mbox_resp_dlen%4 ? 1 : 0)); ii++) {
        mbox_resp_data = lsu_read_32(SOC_MBOX_CSR_MBOX_DATAOUT);
    }
    VPRINTF(LOW, "MCU: Mbox response received\n");

    // MBOX: Clear Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox execute clear\n");
}

// -- function to update various register to default values
// PROT_CAP, DEVICE_ID, HW_STATUS
void boot_i3c_reg(void) {

    uint32_t i3c_reg_data;
    //-- PROT_CAP
    VPRINTF(LOW, "MCU: Updating I3C Recovery Registers..\n");
    
    i3c_reg_data = 0x2050434f;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr PROT_CAP_0 with 'h %0x\n", i3c_reg_data);
    i3c_reg_data = 0x56434552;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr PROT_CAP_1 with 'h %0x\n", i3c_reg_data);

    i3c_reg_data = 0x00000101;
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr PROT_CAP_2 with 'h %0x\n", i3c_reg_data);    

    //-- DEVICE_ID
    i3c_reg_data = 0x00000001; //-- Dummy value
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_0, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_1, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_2, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_3, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_4, i3c_reg_data++);
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_ID_5, i3c_reg_data++);
    VPRINTF(LOW, "MCU: Wr DEVICE_ID with 'h %0x\n", i3c_reg_data);

    //-- HW_STATUS
    i3c_reg_data = 0x00000100; //-- Dummy value
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_HW_STATUS, i3c_reg_data);
    VPRINTF(LOW, "MCU: Wr HW_STATUS with 'h %0x\n", i3c_reg_data);

}

// -- function boot standby ctrl mode
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.STBY_CR_ENABLE_INIT = 2
// tb.reg_map.I3C_EC.STDBYCTRLMODE.STBY_CR_CONTROL.TARGET_XACT_ENABLE = 1
void boot_i3c_standby_ctrl_mode(){
    uint32_t i3c_reg_data;
    i3c_reg_data = 0x00000000;

    VPRINTF(LOW, "MCU: boot_i3c_standby_ctrl_mode register writes \n");
    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL);
    i3c_reg_data = 2 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_LOW | i3c_reg_data;
    i3c_reg_data = 1 << I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL_TARGET_XACT_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_CONTROL, i3c_reg_data);

}

// Helper function to write I3C SOCMGMTIF registers
void write_i3c_socmgmtif_registers(uint32_t t_r, uint32_t t_f, uint32_t t_hd_dat, uint32_t t_su_dat) {
    VPRINTF(LOW, "MCU: boot_i3c_socmgmt_if register writes \n");
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_R_REG, t_r);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_F_REG, t_f);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_HD_DAT_REG, t_hd_dat);
    lsu_write_32(SOC_I3CCSR_I3C_EC_SOCMGMTIF_T_SU_DAT_REG, t_su_dat);
}

//-- function to boot i3c socmgmt interface
void boot_i3c_socmgmt_if(void) {
    uint32_t i3c_reg_data;

    // Read clock frequency from configuration file
    // file name : caliptra_ss_clk_freq.h
    uint32_t clk_freq = CALIPTRA_SS_CLK_FREQ;
    VPRINTF(LOW, "MCU: I3C Clock Frequency: %u MHz\n", clk_freq);

    switch (clk_freq) {
        case 160:
            //-- for 160 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        case 167:
            //-- for 167 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        case 170:
            //-- for 170 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        case 400:
            //-- for 400 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        case 500:
            //-- for 500 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        case 1000:
            //-- for 1000 MHz
            write_i3c_socmgmtif_registers(0x00000000, 0x00000000, 0x00000000, 0x00000000);
            break;
        default:
            VPRINTF(LOW, "Error: Unsupported clock frequency %u MHz\n", clk_freq);
            return;
    }

    //-- Enable the I3C bus
    VPRINTF(LOW, "MCU: Writing I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW register  \n");
    i3c_reg_data = lsu_read_32( SOC_I3CCSR_I3CBASE_HC_CONTROL);
    i3c_reg_data = 1 << I3CCSR_I3CBASE_HC_CONTROL_BUS_ENABLE_LOW | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3CBASE_HC_CONTROL, i3c_reg_data);
}

// -- function boot i3c core (i3c bringup)
void boot_i3c_core(void) {

    uint32_t i3c_reg_data;

    VPRINTF(LOW, "MCU: I3C Core Bringup .. Started \n");
    boot_i3c_socmgmt_if();
    boot_i3c_standby_ctrl_mode(); 
    boot_i3c_reg();

    //setting device address to 0x5A
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 90 << 0  | i3c_reg_data;
    i3c_reg_data = 1  << 15 | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Device Address set to 0x5A\n");

    //setting virtual device address to 0x5B
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 91 << 0  | i3c_reg_data; //0x5B
    i3c_reg_data = 1  << 15 | i3c_reg_data;   
    lsu_write_32 ( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Virtual Device Address set to 0x5B\n");
    VPRINTF(LOW, "MCU: I3C Core Bringup .. Completed \n");

}

void trigger_caliptra_go(void){
    
    enum boot_fsm_state_e boot_fsm_ps;
    // Wait for Boot FSM to stall (on breakpoint) or finish bootup
    boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    while(boot_fsm_ps != BOOT_DONE && boot_fsm_ps != BOOT_WAIT) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        boot_fsm_ps = (lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
    }

    // Advance from breakpoint, if set
    if (boot_fsm_ps == BOOT_WAIT) {
        lsu_write_32(SOC_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);
    }
    VPRINTF(LOW, "MCU: Set Caliptra BootFSM GO\n");

}

void wait_for_cptra_ready_for_mb_processing(void) {
    ////////////////////////////////////
    // Mailbox command test
    // MBOX: Wait for ready_for_mb_processing
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK)) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }
    VPRINTF(LOW, "MCU: Ready for FW\n");
}

void configure_captra_axi_user(void) {
    // MBOX: Setup valid AXI USER
    VPRINTF(LOW, "MCU: Configuring MBOX Valid AXI USER\n");
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0, 0xffffffff); // LSU AxUSER value. TODO: Derive from parameter
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0, SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK);
    VPRINTF(LOW, "MCU: Configured MBOX Valid AXI USER\n");
}

void cptra_prod_rom_boot_go(void) {

    mcu_cptra_user_init();
    
    // MBOX: Acquire lock
    VPRINTF(LOW, "MCU: Acquiring Mbox lock\n");
    while((lsu_read_32(SOC_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK));
    VPRINTF(LOW, "MCU: Mbox lock acquired\n");

    // MBOX: Write CMD
    lsu_write_32(SOC_MBOX_CSR_MBOX_CMD, 0x52494644 | MBOX_CMD_FIELD_RESP_MASK); // Resp required

    // MBOX: Write DLEN
    lsu_write_32(SOC_MBOX_CSR_MBOX_DLEN, 0);

    // MBOX: Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);
    VPRINTF(LOW, "MCU: Mbox execute\n");

    // MBOX: Poll status
    while(((lsu_read_32(SOC_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> MBOX_CSR_MBOX_STATUS_STATUS_LOW) != CMD_COMPLETE) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }
    VPRINTF(LOW, "MCU: Mbox response ready\n");

    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    // MBOX: Clear Execute
    lsu_write_32(SOC_MBOX_CSR_MBOX_EXECUTE, 0);
    VPRINTF(LOW, "MCU: Mbox execute clear\n");

    VPRINTF(LOW, "MCU: Completed with cptra_prod_rom_boot_go\n");

}

// -- function to update cptra_wdt_cfg
// -- example call to function : update_cptra_wdt_cfg(1000, 250, 1);
void update_cptra_wdt_cfg(uint16_t cptra_timer_cfg, uint16_t cptra_wdt_cfg_1, uint16_t cptra_wdt_cfg_0) {
    // programming WDT
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_TIMER_CONFIG, cptra_timer_cfg);
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_WDT_CFG_1, cptra_wdt_cfg_1);
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_WDT_CFG_0, cptra_wdt_cfg_0);
}

void update_cptra_fuse_cfg(void) {

    uint32_t reg_data_32;
    
    VPRINTF(LOW, "MCU: Updating CPTRA FUSE registers..started\n");

    // Add fuse values
    // SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0..11
    // ROM11 : 8af1e8fbb74c19b9d6b234fe4dfc403a378cb4d5dd5cf4f375fb4ecc1d03f40071a3c8471c27f02db1b296f2cb3fb923
    reg_data_32 = 0x8af1e8fb; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0, reg_data_32);
    reg_data_32 = 0xb74c19b9; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1, reg_data_32);
    reg_data_32 = 0xd6b234fe; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x4dfc403a; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6, reg_data_32);
    reg_data_32 = 0x1d03f400; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7, reg_data_32);
    reg_data_32 = 0x71a3c847; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8, reg_data_32);
    reg_data_32 = 0x1c27f02d; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9, reg_data_32);
    reg_data_32 = 0xb1b296f2; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10, reg_data_32);
    reg_data_32 = 0xcb3fb923; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0..11 
    // ROM11 : 18211dda96dc39ae5782ef97408cad8da81915087739d3eeda8581a4d4a72c16df1e4144cbf6423e1bb98990153def5b
    reg_data_32 = 0x18211dda; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0, reg_data_32);
    reg_data_32 = 0x96dc39ae; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1, reg_data_32);
    reg_data_32 = 0x5782ef97; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x408cad8d; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3, reg_data_32);
    reg_data_32 = 0xa8191508; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4, reg_data_32);
    reg_data_32 = 0x7739d3ee; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5, reg_data_32);
    reg_data_32 = 0xda8581a4; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6, reg_data_32);
    reg_data_32 = 0xd4a72c16; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7, reg_data_32);
    reg_data_32 = 0xdf1e4144; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8, reg_data_32);
    reg_data_32 = 0xcbf6423e; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9, reg_data_32);
    reg_data_32 = 0x1bb98990; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10, reg_data_32);
    reg_data_32 = 0x153def5b; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0..23
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,      reg_data_32);
    reg_data_32 = 0xFFFFFFFF; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11,     reg_data_32);
    reg_data_32 = 0x02020101; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12,     reg_data_32);
    reg_data_32 = 0x30304040; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13,     reg_data_32);
    reg_data_32 = 0x05050606; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14,     reg_data_32);
    reg_data_32 = 0x70708080; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15,     reg_data_32);

    VPRINTF(LOW, "MCU: Update CPTRA FUSE registers.. Completed\n");

}

// -- function to update pqc key type
void update_pqc_key_type(void){
    uint32_t reg_data_32;
    // Update PQC Key Type
    VPRINTF(LOW, "MCU: Update PQC Key Type.. Started\n");
    // SOC_IFC_REG_FUSE_PQC_KEY_TYPE
    reg_data_32 = 0x1;        
    lsu_write_32(SOC_SOC_IFC_REG_FUSE_PQC_KEY_TYPE,        reg_data_32);
    VPRINTF(LOW, "MCU: Update PQC Key Type.. Completed\n");
}

// -- function to boot_mcu_with_fuses
void boot_mcu(){

   
    uint32_t reg_data_32;
    
    mcu_mci_boot_go();

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

    // Add fuse values
    // SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0..11
    // Old : 53845724676e5e2f649d2c018e25c4fb80c2c28fcb6d6e93fb7cf908930a9953a9c69c3383aea9fd5573cb3db1ae0c3b
    // ROM7 : 9edb99809108c53f602883fe691943210445970d3d3d7eda4d320cc94113df3ab9d8a9741f7231851b866a64f75108e8
    // ROM11 : 8af1e8fbb74c19b9d6b234fe4dfc403a378cb4d5dd5cf4f375fb4ecc1d03f40071a3c8471c27f02db1b296f2cb3fb923
    reg_data_32 = 0x8af1e8fb; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0, reg_data_32);
    reg_data_32 = 0xb74c19b9; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1, reg_data_32);
    reg_data_32 = 0xd6b234fe; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x4dfc403a; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6, reg_data_32);
    reg_data_32 = 0x1d03f400; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7, reg_data_32);
    reg_data_32 = 0x71a3c847; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8, reg_data_32);
    reg_data_32 = 0x1c27f02d; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9, reg_data_32);
    reg_data_32 = 0xb1b296f2; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10, reg_data_32);
    reg_data_32 = 0xcb3fb923; lsu_write_32(SOC_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0..11 
    // Old : 421275a87a71acf434b4f1076acdd68377d0a315f9e2a29b26b398913e89ff33006c10dcc4f1bd7467f1e2c41b0a893a
    // ROM7 : 879d4deca00dbddc5755ebc2ba1f40fa2626c033f5b2a02ac8ac032074baebc8adcbbc0c96d9d14061ea01aaa4902e75
    // ROM11 : 18211dda96dc39ae5782ef97408cad8da81915087739d3eeda8581a4d4a72c16df1e4144cbf6423e1bb98990153def5b
    reg_data_32 = 0x18211dda; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0, reg_data_32);
    reg_data_32 = 0x96dc39ae; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1, reg_data_32);
    reg_data_32 = 0x5782ef97; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2, reg_data_32);
    reg_data_32 = 0x408cad8d; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3, reg_data_32);
    reg_data_32 = 0xa8191508; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4, reg_data_32);
    reg_data_32 = 0x7739d3ee; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5, reg_data_32);
    reg_data_32 = 0xda8581a4; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6, reg_data_32);
    reg_data_32 = 0xd4a72c16; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7, reg_data_32);
    reg_data_32 = 0xdf1e4144; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8, reg_data_32);
    reg_data_32 = 0xcbf6423e; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9, reg_data_32);
    reg_data_32 = 0x1bb98990; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10, reg_data_32);
    reg_data_32 = 0x153def5b; lsu_write_32(SOC_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11, reg_data_32);

    // SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0..23
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,      reg_data_32);
    reg_data_32 = 0xFFFFFFFF; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11,     reg_data_32);
    reg_data_32 = 0x02020101; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12,     reg_data_32);
    reg_data_32 = 0x30304040; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13,     reg_data_32);
    reg_data_32 = 0x05050606; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14,     reg_data_32);
    reg_data_32 = 0x70708080; lsu_write_32(SOC_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15,     reg_data_32);

    // -- Updating REVOCATIONS for MLDSA, LMS, ECC
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_MLDSA_REVOCATION,        reg_data_32);
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_LMS_REVOCATION,          reg_data_32);
    reg_data_32 = 0x0;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_ECC_REVOCATION,          reg_data_32);

    // SOC_IFC_REG_FUSE_PQC_KEY_TYPE
    reg_data_32 = 0x1;        lsu_write_32(SOC_SOC_IFC_REG_FUSE_PQC_KEY_TYPE,        reg_data_32);

    //-- update the Caliptra WDT Config
    update_cptra_wdt_cfg(1000, 250, 1);
    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");


}
