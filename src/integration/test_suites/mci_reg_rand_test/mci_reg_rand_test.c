#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/* Include MCI register definitions and utilities */
#include "mci.h"


#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "fuse_ctrl_address_map.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t value, status, done;
    uint32_t mbox0_size, mbox1_size;
    uint32_t single_error, double_error;
    uint32_t before_snapshot[MAX_REGISTERS_PER_GROUP];
    uint32_t after_snapshot[MAX_REGISTERS_PER_GROUP];
    mci_register_group_t found_group;
    int found_index;
    int total_reg_count;

    uint32_t read_data;

    VPRINTF(LOW, "==================\nMCI Registers Test\n==================\n\n");

    mci_init();

    // Exclude registers from writing during group write
    exclude_register(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO);
    exclude_register(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    exclude_register(SOC_MBOX_CSR_MBOX_LOCK);
    exclude_register(SOC_MBOX_CSR_MBOX_USER);
    
    // Loop through all register groups
    for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
        if ((group == REG_GROUP_GENERIC_WIRES) || (group == REG_GROUP_SS) || (group == REG_GROUP_TRACE)) {
                continue;
        }
        else {
            // Write random values to all registers in this group
            write_random_to_register_group_and_track(group, &g_expected_data_dict);
            read_register_group_and_verify(group, &g_expected_data_dict);
        }    
    }

    printf("Completed writing random values to all register groups.\n");
 
    total_reg_count = get_total_register_count();
    printf("TOtal Register Count: %d", total_reg_count);
 
    
    printf("\nMCI Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}