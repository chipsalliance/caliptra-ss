#ifndef MCI_REG_DEFS_H
#define MCI_REG_DEFS_H

#include <stdint.h>

// [03/26] MCI Register Count: 261
#define MAX_REGISTER_ENTRIES 300

// Register info struct
typedef struct {
    uint32_t address;   /* Register address */
    const char *name;   /* Register name */
    const char *desc;   /* Register description */
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

// Register groups
typedef enum {
    REG_GROUP_CAPABILITIES,
    REG_GROUP_HARDWARE_STATUS,
    REG_GROUP_ERROR,
    REG_GROUP_SECURITY,
    REG_GROUP_WATCHDOG,
    REG_GROUP_MCU,
    REG_GROUP_CONTROL,
    REG_GROUP_MCI_MBOX0,
    REG_GROUP_MCU_MBOX0,
    REG_GROUP_MCI_MBOX1,
    REG_GROUP_MCU_MBOX1,
    REG_GROUP_DFT,
    REG_GROUP_DEBUG,
    REG_GROUP_GENERIC_WIRES,
    REG_GROUP_SS,
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