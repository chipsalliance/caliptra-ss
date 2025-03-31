#include <stdio.h>
#include "mci_reg_utils.h"
#include "mci_reg_access.h"

/*
 * Function to read all registers in a group and print their values
 */
void read_register_group(mci_register_group_t group) {
    int i = 0;
    const mci_register_info_t *reg_info;
    uint32_t value;
    
    printf("==== Reading %s Registers ====\n", get_group_name(group));
    
    while ((reg_info = get_register_info(group, i)) != NULL) {
        value = mci_reg_read(reg_info->address);
        printf("%-40s (0x%08x): 0x%08x\n", reg_info->name, reg_info->address, value);
        i++;
    }
    
    printf("\n");
}

/*
 * Function to read a specific register by group and index
 * Returns the register value and prints it if print_value is true
 */
uint32_t read_register(mci_register_group_t group, int index, int print_value) {
    const mci_register_info_t *reg_info = get_register_info(group, index);
    uint32_t value = 0;
    
    if (reg_info != NULL) {
        value = mci_reg_read(reg_info->address);
        
        if (print_value) {
            printf("%-40s (0x%08x): 0x%08x\n", reg_info->name, reg_info->address, value);
        }
    }
    
    return value;
}

/*
 * Function to write a specific value to all registers in a group
 */
void write_register_group(mci_register_group_t group, uint32_t value) {
    int i = 0;
    const mci_register_info_t *reg_info;
    
    printf("==== Writing 0x%08x to %s Registers ====\n", value, get_group_name(group));
    
    while ((reg_info = get_register_info(group, i)) != NULL) {
        mci_reg_write(reg_info->address, value);
        printf("%-40s (0x%08x): Written 0x%08x\n", reg_info->name, reg_info->address, value);
        i++;
    }
    
    printf("\n");
}

/*
 * Function to write a value to a specific register by group and index
 */
void write_register(mci_register_group_t group, int index, uint32_t value) {
    const mci_register_info_t *reg_info = get_register_info(group, index);
    
    if (reg_info != NULL) {
        mci_reg_write(reg_info->address, value);
        printf("%-40s (0x%08x): Written 0x%08x\n", reg_info->name, reg_info->address, value);
    }
}

/*
 * Function to capture and save register values to an array
 * Returns the number of registers captured
 */
int capture_register_snapshot(mci_register_group_t group, uint32_t *values, int max_values) {
    int i = 0;
    const mci_register_info_t *reg_info;
    
    while ((reg_info = get_register_info(group, i)) != NULL && i < max_values) {
        values[i] = mci_reg_read(reg_info->address);
        i++;
    }
    
    return i;
}

/*
 * Function to compare two register snapshots and print differences
 * Returns the number of differences found
 */
int compare_register_snapshots(mci_register_group_t group, uint32_t *snapshot1, uint32_t *snapshot2) {
    int i = 0;
    int diff_count = 0;
    const mci_register_info_t *reg_info;
    
    printf("==== Comparing %s Register Snapshots ====\n", get_group_name(group));
    
    while ((reg_info = get_register_info(group, i)) != NULL) {
        if (snapshot1[i] != snapshot2[i]) {
            printf("%-40s (0x%08x): Changed 0x%08x -> 0x%08x\n",
                   reg_info->name, reg_info->address, snapshot1[i], snapshot2[i]);
            diff_count++;
        }
        i++;
    }
    
    printf("\n");
    return diff_count;
}

/*
 * Function to dump all register values across all groups
 */
void dump_all_registers(void) {
    printf("==== Dumping All Registers ====\n\n");
    
    for (int group = 0; group < REG_GROUP_COUNT; group++) {
        read_register_group((mci_register_group_t)group);
    }
}

/*
 * Function to initialize registers with default values
 */
void initialize_registers(void) {
    // Set default values for specific registers as needed
    mci_reg_write(SOC_MCI_TOP_MCI_REG_HW_CAPABILITIES, 0x12345678);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_FW_CAPABILITIES, 0x87654321);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_HW_REV_ID, 0x00000100);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_HW_CONFIG0, 0x00003000);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_HW_CONFIG1, 0x00000140);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_SECURITY_STATE, 0x00000003);
    
    // Initialize interupt control registers
    mci_reg_write(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, 0x00000000);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R, 0x00000000);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, 0x00000000);
}

/*
 * Function to find a register by address (across all groups)
 * Returns: Register info pointer, or NULL if not found
 * Sets: group_index and reg_index if register is found
 */
const mci_register_info_t* find_register_by_address(uint32_t address, 
                                                    mci_register_group_t *group_index, 
                                                    int *reg_index) {
    for (int group = 0; group < REG_GROUP_COUNT; group++) {
        int i = 0;
        const mci_register_info_t *reg_info;
        
        while ((reg_info = get_register_info(group, i)) != NULL) {
            if (reg_info->address == address) {
                if (group_index) {
                    *group_index = (mci_register_group_t)group;
                }
                if (reg_index) {
                    *reg_index = i;
                }
                return reg_info;
            }
            i++;
        }
    }
    
    return NULL;
}