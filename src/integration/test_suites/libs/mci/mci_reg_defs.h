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

#ifndef MCI_REG_DEFS_H
#define MCI_REG_DEFS_H

#include <stdint.h>

// [03/26] MCI Register Count: 261
#define MAX_REGISTER_ENTRIES 300

// Enum for register sticky behavior
typedef enum {
    REG_NOT_STICKY = 0,
    REG_STICKY = 1
} register_sticky_t;


// Register info struct
typedef struct {
    uint32_t address;   /* Register address */
    const char *name;   /* Register name */
    const char *desc;   /* Register description */
    register_sticky_t is_sticky;        /* Flag to indicate if register is sticky */
} mci_register_info_t;

// Register expected data struct
typedef struct {
    uint32_t address;         // Address of the register instead of name
    uint32_t expected_data;   // Expected data value
} mci_register_exp_data_t;

// Dictionary of register expected values
typedef struct {
    mci_register_exp_data_t entries[MAX_REGISTER_ENTRIES];  /* Fixed-size array of entries */
    int count;                                             /* Current number of entries */
} mci_reg_exp_dict_t;

// Register mask struct
typedef struct {
    uint32_t address;        /* Register address */
    uint32_t combined_mask;  /* Combined mask of all readable/writable bits */
} register_mask_t;

// Dictionary of register mask values
typedef struct {
    register_mask_t entries[MAX_REGISTER_ENTRIES];  /* Fixed-size array of entries */
    int count;                                      /* Current number of entries */
} register_mask_dict_t;

typedef enum {
    COLD_RESET = 0, 
    WARM_RESET = 1
} reset_type_t;

// Register groups
typedef enum {
    REG_GROUP_KNOWN_VALUES,
    REG_GROUP_CAPABILITIES,
    REG_GROUP_CAPABILITIES_RO,
    REG_GROUP_STATUS,
    REG_GROUP_STATUS_RO,
    REG_GROUP_ERROR_W1C,
    REG_GROUP_ERROR,
    REG_GROUP_SECURITY_RO,
    REG_GROUP_WATCHDOG,
    REG_GROUP_WATCHDOG_RO,
    REG_GROUP_MCU,
    REG_GROUP_CONTROL,
    REG_GROUP_MCI_MBOX0,
    REG_GROUP_MCU_MBOX0,
    REG_GROUP_MCU_MBOX0_RO,
    REG_GROUP_MCI_MBOX1,
    REG_GROUP_MCU_MBOX1,
    REG_GROUP_MCU_MBOX1_RO,
    REG_GROUP_DFT,
    REG_GROUP_DEBUG,
    REG_GROUP_GENERIC_WIRES,
    REG_GROUP_GENERIC_WIRES_RO,
    REG_GROUP_SS,
    REG_GROUP_SS_RO,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_0,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_1,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_2,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_3,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_4,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_5,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_6,
    REG_GROUP_DEBUG_UNLOCK_PK_HASH_7,
    REG_GROUP_INTERRUPT,
    REG_GROUP_INTERRUPT_COUNTERS,
    REG_GROUP_TRACE,
    REG_GROUP_TRACE_RO,
    REG_GROUP_SOC_MBOX_CSR,
    REG_GROUP_COUNT
} mci_register_group_t;

/* Maximum number of registers in any group */
#define MAX_REGISTERS_PER_GROUP 25

/* Declare the register groups array (defined in mci_register_defs.c) */
extern const mci_register_info_t register_groups[][MAX_REGISTERS_PER_GROUP];

/* Function to get a string representation of a register group */
const char* get_group_name(mci_register_group_t group);

/* Get the number of registers in a group */
int get_register_count(mci_register_group_t group);

/* Get register information by its index within a group */
const mci_register_info_t* get_register_info(mci_register_group_t group, int index);

#endif /* MCI_REGISTER_DEFS_H */