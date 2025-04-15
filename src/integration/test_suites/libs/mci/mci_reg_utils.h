#ifndef MCI_REG_UTILS_H
#define MCI_REG_UTILS_H

#include <stdint.h>
#include "mci_reg_defs.h"

/*
 * Function to read all registers in a group and print their values
 */
void read_register_group(mci_register_group_t group);

/*
 * Function to read a specific register by group and index
 * Returns the register value and prints it if print_value is true
 */
uint32_t read_register(mci_register_group_t group, int index, int print_value);

/*
 * Function to write a specific value to all registers in a group
 */
void write_register_group(mci_register_group_t group, uint32_t value);

/*
 * Function to write a value to a specific register by group and index
 */
void write_register(mci_register_group_t group, int index, uint32_t value);

/*
 * Function to capture and save register values to an array
 * Returns the number of registers captured
 */
int capture_register_snapshot(mci_register_group_t group, uint32_t *values, int max_values);

/*
 * Function to compare two register snapshots and print differences
 * Returns the number of differences found
 */
int compare_register_snapshots(mci_register_group_t group, uint32_t *snapshot1, uint32_t *snapshot2);

/*
 * Function to dump all register values across all groups
 */
void dump_all_registers(void);

/*
 * Function to initialize registers with default values
 */
void initialize_registers(void);

/*
 * Function to find a register by address (across all groups)
 * Returns: Register info pointer, or NULL if not found
 * Sets: group_index and reg_index if register is found
 */
const mci_register_info_t* find_register_by_address(uint32_t address, 
                                                    mci_register_group_t *group_index, 
                                                    int *reg_index);

#endif /* MCI_REG_UTILS_H */