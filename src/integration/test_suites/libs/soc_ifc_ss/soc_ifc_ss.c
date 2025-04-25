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
#include "soc_ifc_ss.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "caliptra_reg.h"
#include "caliptra_ss_lib.h"
#include "printf.h"

uint32_t cptra_axi_dword_read(uint64_t src_addr){
    uint32_t payload[1];
    uint8_t status;
    status = soc_ifc_axi_dma_read_ahb_payload(src_addr, 0, payload, 4,0);
    return payload[0];
}

uint8_t cptra_axi_dword_read_with_status(uint64_t src_addr, uint32_t * payload){
    return soc_ifc_axi_dma_read_ahb_payload_with_status(src_addr, 0, payload, 4,0);
}

uint8_t soc_ifc_axi_dma_read_ahb_payload_with_status(uint64_t src_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size) {
    soc_ifc_axi_dma_arm_read_ahb_payload(src_addr, fixed, payload, byte_count, block_size);
    soc_ifc_axi_dma_get_read_ahb_payload(payload, byte_count);
    return soc_ifc_axi_dma_wait_idle_with_status(0, 1);
}


uint8_t cptra_axi_dword_write(uint64_t dest_addr, uint32_t data){
    uint32_t payload[1] = {data};
    uint8_t status;
    status = soc_ifc_axi_dma_send_ahb_payload(dest_addr, 0, payload, 4,0);
    return status;
}

uint8_t soc_ifc_axi_dma_wait_idle_with_status(uint8_t clr_lock, uint8_t clr_error) {
    uint8_t error = 0;
    uint32_t reg;

    // Check completion
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(LOW, "Caliptra: DMA Err Seen\n");
        error = 1;
        if(clr_error) {
            VPRINTF(LOW, "Caliptra: Flushing DMA Err\n");
            lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        }
    }

    if (clr_lock) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    }
    return error;
}


uint8_t soc_ifc_axi_dma_send_ahb_payload_with_status(uint64_t dst_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size) {
    soc_ifc_axi_dma_arm_send_ahb_payload(dst_addr, fixed, payload, byte_count, block_size);
    soc_ifc_axi_dma_get_send_ahb_payload(payload, byte_count);
    return soc_ifc_axi_dma_wait_idle_with_status(0, 1);
}

uint8_t cptra_axi_dword_write_with_status(uint64_t dest_addr, uint32_t data){
    uint32_t payload[1] = {data};
    uint8_t status;
    status = soc_ifc_axi_dma_send_ahb_payload_with_status(dest_addr, 0, payload, 4,0);
    return status;
}

uint32_t cptra_get_mcu_sram_size(){
    uint32_t data;
    data = cptra_axi_dword_read(SOC_MCI_TOP_MCI_REG_HW_CONFIG1);
    return (data & MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK) >> MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW;
}


uint32_t cptra_get_mcu_sram_size_byte(){
    return cptra_get_mcu_sram_size() * 1024;
}

uint32_t cptra_get_mcu_sram_end_addr(){
   return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + cptra_get_mcu_sram_size_byte() - 1;

}

uint32_t cptra_get_mcu_sram_last_dword(){
    return cptra_get_mcu_sram_end_addr() & ~3;
}


uint32_t cptra_get_mcu_sram_execution_region_start() {
    return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR;
}


uint32_t cptra_get_mcu_sram_execution_region_end() {
    uint32_t fw_exec_region;

    fw_exec_region = cptra_axi_dword_read(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE) + 1;

    return cptra_get_mcu_sram_execution_region_start() + (fw_exec_region * 4 * 1024) -1;
}

bool cptra_is_sram_protected_region(){
    return cptra_get_mcu_sram_protected_region_start() <= cptra_get_mcu_sram_end_addr();
}

uint32_t cptra_get_mcu_sram_protected_region_start() {
    return cptra_get_mcu_sram_execution_region_end() + 1;
}

uint32_t cptra_get_mcu_sram_protected_region_end() {
   return cptra_get_mcu_sram_end_addr();

}


void cptra_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count, bool fail_on_timeout) {
    uint32_t lock;
    uint64_t addr;
    VPRINTF(LOW, "Caliptra: Waiting for Mbox%x lock acquired\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        addr = SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num;

        lock = cptra_axi_dword_read(addr);
        lock = lock & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;
        if(!lock){
            VPRINTF(LOW, "Caliptra: Mbox%x lock acquired\n", mbox_num);
            return;
        }
    }   
    if (fail_on_timeout) {
        VPRINTF(FATAL, "Caliptra: Failed to aquire MCU MBOX%x after %d attempts", mbox_num, attempt_count);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    } 
    return;
}

void cptra_mcu_mbox_acquire_lock_set_execute(uint32_t mbox_num, uint32_t attempt_count) {
    uint64_t addr;
    cptra_mcu_mbox_acquire_lock(mbox_num, attempt_count, true);

    VPRINTF(LOW, "Caliptra: Setting MBOX%x EXECUTE\n", mbox_num);
    addr = SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num;
    cptra_axi_dword_write(addr, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);

}

void cptra_mcu_mbox_wait_for_status(uint32_t mbox_num, uint32_t attempt_count, enum mcu_mbox_cmd_status cmd_status) {
    uint32_t status;
    uint64_t addr;
    VPRINTF(LOW, "Caliptra: Waiting for Mbox%x Status: 0x%x\n", mbox_num, cmd_status);
    addr = SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        status = cptra_axi_dword_read(addr) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;

        if(status == cmd_status){
            VPRINTF(LOW, "Caliptra: Mbox%x Status 0x%x Seen!\n", mbox_num, cmd_status);
            return;
        }
    }   
    VPRINTF(FATAL, "Caliptra: Failed to get status: 0x%x from MCU MBOX%x after %d attempts", cmd_status, mbox_num, attempt_count);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

void cptra_mcu_mbox_wait_execute(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR EXECUTE to be SET\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        if(mbox_data) {
            return;
        }
    }
    VPRINTF(FATAL, "Caliptra: Failed waiting for execute to be set in MCU MBOX%x after %d attempts", mbox_num, attempt_count);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

void cptra_mcu_mbox_wait_target_user_valid(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x WAIT FOR TARGET USER VALID\n", mbox_num);
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK;
        if(mbox_data) {
            return;
        }
    }
    VPRINTF(FATAL, "Caliptra: Failed waiting for TARGET_USER_VALID MCU MBOX%x after %d attempts", mbox_num, attempt_count);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

uint32_t cptra_mcu_mbox_get_sram_size_kb(uint32_t mbox_num) {
    uint32_t data;
    uint32_t mask = MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK << ((MCU_MBOX_MAX_NUM-1 - mbox_num) * MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW);
    data = cptra_axi_dword_read(SOC_MCI_TOP_MCI_REG_HW_CONFIG0) & mask;
    data = data >> ((MCU_MBOX_MAX_NUM-1 - mbox_num) * MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW);
    return data;
}

void cptra_mcu_mbox_set_target_status_done(uint32_t mbox_num, enum mcu_mbox_target_status targ_status) {
    VPRINTF(LOW, "CALIPTRA: Set TARGET_USER_STATUS Done in MBOX%x with CMD: 0x%x\n", mbox_num, targ_status);
    uint32_t write_data = MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK |
                                (targ_status >> MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_LOW);
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, write_data);

}
    
void cptra_mcu_mbox_write_cmd(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x CMD: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_cmd(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x CMD: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_mbox_user(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x USER: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_mbox_user(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x USER: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_dlen(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x DLEN: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_dlen(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x DLEN: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_dword_sram(uint32_t mbox_num, uint32_t dword_addr, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x SRAM[%d]: 0x%x\n", mbox_num, dword_addr, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

void cptra_mcu_mbox_write_dword_sram_burst(uint32_t mbox_num, uint32_t dword_addr, uint32_t * payload, uint32_t size_in_bytes, uint16_t block_size) {
    VPRINTF(LOW, "CALIPTRA: Write burst to MBOX%x starting at SRAM[%d], size in bytes: 0x%x\n", mbox_num, dword_addr, size_in_bytes); 
    uint8_t status;
    status = soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num,
                                             0, payload, size_in_bytes, block_size);
}    

uint32_t cptra_mcu_mbox_read_dword_sram(uint32_t mbox_num, uint32_t dword_addr) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x SRAM[%d]: 0x%x\n", mbox_num, dword_addr, data);
    return data;
}

void cptra_mcu_mbox_read_dword_sram_burst(uint32_t mbox_num, uint32_t dword_addr, uint32_t * payload, uint32_t size_in_bytes, uint16_t block_size) {
    VPRINTF(LOW, "CALIPTRA: Read burst to MBOX%x starting at SRAM[%d], size in bytes: 0x%x\n", mbox_num, dword_addr, size_in_bytes); 
    uint8_t status;
    status = soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + 4*dword_addr + MCU_MBOX_NUM_STRIDE * mbox_num,
                                             0, payload, size_in_bytes, block_size);

}

void cptra_mcu_mbox_write_cmd_status(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x CMD_STATUS: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_cmd_status(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x CMD_STATUS: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_execute(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x EXECUTE: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_execute(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x EXECUTE: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_target_user(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x TARGET_USER: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_target_user(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x TARGET_USER: 0x%x\n", mbox_num, data);
    return data;
}

void cptra_mcu_mbox_write_target_user_valid(uint32_t mbox_num, uint32_t data) {
    VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x TARGET_USER_VALID: 0x%x\n", mbox_num, data); 
    cptra_axi_dword_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, data);
}

uint32_t cptra_mcu_mbox_read_target_user_valid(uint32_t mbox_num) {
    uint32_t data = cptra_axi_dword_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num);
    VPRINTF(LOW, "CALIPTRA: Reading Mbox%x TARGET_USER_VALID: 0x%x\n", mbox_num, data);
    return data;
}

bool cptra_wait_for_cptra_mbox_execute(uint32_t attempt_count) {
    VPRINTF(LOW, "CALIPTRA: Waiting for Caliptra MBOX execute\n");
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        if((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK){
            VPRINTF(LOW, "CALIPTRA: Caliptra MBOX execute set\n");
            return true;
        }
    }
    return false;
}

void cptra_wait_mcu_reset_req_interrupt_clear(uint32_t attempt_count) {
    VPRINTF(LOW, "CALIPTRA: Waiting for MCI Reset Request interrupt to be cleared\n");
    uint32_t status;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        status = cptra_axi_dword_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK;

        if(!status){
            VPRINTF(LOW, "CALIPTRA: MCI Reset Request interrupt cleared\n");
            return;
        }
    }   
    VPRINTF(FATAL, "CALIPTRA: MCI Reset Request interrupt not cleared");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

void cptra_wait_mcu_reset_status_set(uint32_t attempt_count) {
    VPRINTF(LOW, "CALIPTRA: Waiting for MCU Reset Status to be set\n");
    uint32_t status;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        status = cptra_axi_dword_read(SOC_MCI_TOP_MCI_REG_RESET_STATUS) & MCI_REG_RESET_STATUS_MCU_RESET_STS_MASK;
        if(status){
            VPRINTF(LOW, "CALIPTRA: MCU Reset Status Set\n");
            return;
        }
    }   
    VPRINTF(FATAL, "CALIPTRA: MCU Reset Status Not Set");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}