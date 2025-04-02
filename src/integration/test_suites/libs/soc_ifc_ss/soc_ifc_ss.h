#ifndef SOC_IFC_SS 
#define SOC_IFC_SS 
#include "stdint.h"
#include <stdbool.h>

uint32_t cptra_axi_dword_read(uint64_t src_addr);

uint8_t cptra_axi_dword_read_with_status(uint64_t src_addr, uint32_t * payload);

uint8_t soc_ifc_axi_dma_read_ahb_payload_with_status(uint64_t src_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size);

uint8_t cptra_axi_dword_write(uint64_t dest_addr, uint32_t data);

uint8_t cptra_axi_dword_write_with_status(uint64_t dest_addr, uint32_t data);

uint32_t cptra_get_mcu_sram_size();

uint32_t cptra_get_mcu_sram_size_byte();

uint32_t cptra_get_mcu_sram_end_addr();

uint32_t cptra_get_mcu_sram_last_dword();

uint32_t cptra_get_mcu_sram_execution_region_start();

uint32_t cptra_get_mcu_sram_execution_region_end();

bool cptra_is_sram_protected_region();

uint32_t cptra_get_mcu_sram_protection_region_start();

uint32_t cptra_get_mcu_sram_protection_region_end();

void cptra_mcu_mbox_wait_for_status_complete(uint32_t mbox_num, uint32_t attempt_count);

void cptra_mcu_mbox_acquire_lock_set_execute(uint32_t mbox_num, uint32_t attempt_count);

void cptra_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count);

uint8_t soc_ifc_axi_dma_send_ahb_payload_with_status(uint64_t dst_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size);

uint8_t soc_ifc_axi_dma_wait_idle_with_status(uint8_t clr_lock, uint8_t clr_error);


#endif // SOC_IFC_SS

