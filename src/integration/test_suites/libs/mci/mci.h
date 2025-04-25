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


#ifndef MCI_LIB
#define MCI_LIB

#include <stdbool.h>
#include "stdint.h"
#include <stddef.h>

#include "mci_reg_defs.h"
#include "soc_address_map.h"

uint32_t get_mcu_sram_size();

uint32_t get_mcu_sram_size_byte();

uint32_t get_mcu_sram_end_addr();

uint32_t get_mcu_sram_last_dword();

uint32_t get_mcu_sram_execution_region_start() ;

uint32_t get_mcu_sram_execution_region_end() ;

uint32_t get_mcu_sram_protected_region_start() ;

uint32_t get_mcu_sram_protected_region_end() ;

bool get_is_sram_protected_region();

uint32_t get_fw_sram_exec_region_less_than_sram_size(uint32_t rnd);

/* Global dictionary */
extern mci_reg_exp_dict_t g_expected_data_dict;

uint32_t mci_reg_read(uint32_t reg_addr);
void mci_reg_write(uint32_t reg_addr, uint32_t value);

const mci_register_info_t* find_register_by_address(uint32_t address, mci_register_group_t *group_index, int *reg_index);
int get_total_register_count(void);
void init_reg_exp_dict(mci_reg_exp_dict_t *dict);
void reset_exp_reg_data(mci_reg_exp_dict_t *dict, reset_type_t reset_type);
int set_reg_exp_data(mci_reg_exp_dict_t *dict, uint32_t address, uint32_t value, uint32_t mask);
int get_reg_exp_data(mci_reg_exp_dict_t *dict, uint32_t address, uint32_t *value);    
void init_mask_dict(void); 
const mci_register_info_t* get_register_info(mci_register_group_t group, int index);
int get_register_count(mci_register_group_t group);
uint32_t get_register_mask(uint32_t address);    
const char* get_group_name(mci_register_group_t group);
int add_mask_entry(uint32_t address, uint32_t mask);
void write_random_to_register_group_and_track(mci_register_group_t group, mci_reg_exp_dict_t *dict);  
void write_to_register_group_and_track(mci_register_group_t group, uint32_t write_data, mci_reg_exp_dict_t *dict); 
int read_register_group_and_verify(mci_register_group_t group, mci_reg_exp_dict_t *dict); 
void read_register_group_and_track(mci_register_group_t group, mci_reg_exp_dict_t *dict);
static void address_to_bitmap_position(uint32_t reg_addr, uint32_t *word_index, uint32_t *bit_position);
int exclude_register(uint32_t reg_addr);
int is_register_excluded(uint32_t reg_addr);
uint32_t get_known_register_value(uint32_t reg_addr);
void init_excluded_registers(void);                                                                       

/* Initialization */
void mci_init(void);

#endif /* MCI_LIB */
