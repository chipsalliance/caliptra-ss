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
    return cptra_get_mcu_sram_protection_region_start() <= cptra_get_mcu_sram_end_addr();
}

uint32_t cptra_get_mcu_sram_protection_region_start() {
    return cptra_get_mcu_sram_execution_region_end() + 1;
}

uint32_t cptra_get_mcu_sram_protection_region_end() {
   return cptra_get_mcu_sram_end_addr();

}


void cptra_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count) {
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
    VPRINTF(FATAL, "Caliptra: Failed to aquire MCU MBOX%x after %d attempts", mbox_num, attempt_count);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

void cptra_mcu_mbox_acquire_lock_set_execute(uint32_t mbox_num, uint32_t attempt_count) {
    uint64_t addr;
    cptra_mcu_mbox_acquire_lock(mbox_num, attempt_count);

    VPRINTF(LOW, "Caliptra: Setting MBOX%x EXECUTE\n", mbox_num);
    addr = SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num;
    cptra_axi_dword_write(addr, MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);

}

void cptra_mcu_mbox_wait_for_status_complete(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t status;
    uint64_t addr;
    VPRINTF(LOW, "Caliptra: Waiting for Mbox%x Satus Complete\n", mbox_num);
    addr = SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        status = cptra_axi_dword_read(addr) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;

        if(status == 0x2){
            VPRINTF(LOW, "Caliptra: Mbox%x Status Complete Seen!\n", mbox_num);
            return;
        }
        else if(status != 0x0) {
            VPRINTF(FATAL, "Caliptra: NON-COMPLETE Status seen MCU MBOX%x: 0x%x", mbox_num, status);
            SEND_STDOUT_CTRL(0x1);
            while(1);

        }
    }   
    VPRINTF(FATAL, "Caliptra: Failed to get a status from MCU MBOX%x after %d attempts", mbox_num, attempt_count);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}
