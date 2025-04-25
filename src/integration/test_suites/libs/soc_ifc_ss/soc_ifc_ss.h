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
#ifndef SOC_IFC_SS 
#define SOC_IFC_SS 
#include "caliptra_ss_lib.h"
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

uint32_t cptra_get_mcu_sram_protected_region_start();

uint32_t cptra_get_mcu_sram_protected_region_end();

void cptra_mcu_mbox_wait_for_status(uint32_t mbox_num, uint32_t attempt_count, enum mcu_mbox_cmd_status cmd_status);

void cptra_mcu_mbox_acquire_lock_set_execute(uint32_t mbox_num, uint32_t attempt_count);

void cptra_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count, bool fail_on_timeout);

uint8_t soc_ifc_axi_dma_send_ahb_payload_with_status(uint64_t dst_addr, uint8_t fixed, uint32_t * payload, uint32_t byte_count, uint16_t block_size);

uint8_t soc_ifc_axi_dma_wait_idle_with_status(uint8_t clr_lock, uint8_t clr_error);

void cptra_mcu_mbox_wait_execute(uint32_t mbox_num, uint32_t attempt_count);

void cptra_mcu_mbox_wait_target_user_valid(uint32_t mbox_num, uint32_t attempt_count);

void cptra_mcu_mbox_set_target_status_done(uint32_t mbox_num, enum mcu_mbox_target_status targ_status);

uint32_t cptra_mcu_mbox_get_sram_size_kb(uint32_t mbox_num);

uint32_t cptra_mcu_mbox_read_cmd(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_mbox_user(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_dlen(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_dword_sram(uint32_t mbox_num, uint32_t dword_addr);
void cptra_mcu_mbox_write_dword_sram_burst(uint32_t mbox_num, uint32_t dword_addr, uint32_t * payload, uint32_t size_in_bytes, uint16_t block_size);
uint32_t cptra_mcu_mbox_read_cmd_status(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_execute(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_target_user(uint32_t mbox_num);
uint32_t cptra_mcu_mbox_read_target_user_valid(uint32_t mbox_num);

void cptra_mcu_mbox_write_dword_sram(uint32_t mbox_num, uint32_t dword_addr, uint32_t data);
void cptra_mcu_mbox_read_dword_sram_burst(uint32_t mbox_num, uint32_t dword_addr, uint32_t * payload, uint32_t size_in_bytes, uint16_t block_size);
void cptra_mcu_mbox_write_execute(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_dlen(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_cmd(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_cmd_status(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_mbox_user(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_target_user(uint32_t mbox_num, uint32_t data);
void cptra_mcu_mbox_write_target_user_valid(uint32_t mbox_num, uint32_t data);

bool cptra_wait_for_cptra_mbox_execute(uint32_t attempt_count);
void cptra_wait_mcu_reset_req_interrupt_clear(uint32_t attempt_count);
void cptra_wait_mcu_reset_status_set(uint32_t attempt_count);

#endif // SOC_IFC_SS

