
#include "caliptra_reg.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)0xd0580000;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// TODO move to an include from caliptra-rtl
enum boot_fsm_state_e {
    BOOT_IDLE   = 0x0,
    BOOT_FUSE   = 0x1,
    BOOT_FW_RST = 0x2,
    BOOT_WAIT   = 0x3,
    BOOT_DONE   = 0x4
};

void main (void) {
        int argc=0;
        char *argv[1];
        enum boot_fsm_state_e boot_fsm_ps;

        VPRINTF(LOW, "=================\nMCU Caliptra Bringup\n=================\n\n")

        // Wait for ready_for_fuses
        while(!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

        // Initialize fuses
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
        VPRINTF(LOW, "MCU: Set fuse wr done\n");

        // Wait for Boot FSM to stall (on breakpoint) or finish bootup
        boot_fsm_ps = (lsu_read_32(/*CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS*/0x3003003c) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
        while(boot_fsm_ps != BOOT_DONE && boot_fsm_ps != BOOT_WAIT) {
            for (uint8_t ii = 0; ii < 16; ii++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            boot_fsm_ps = (lsu_read_32(/*CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS*/0x3003003c) & SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK) >> SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_LOW;
        }

        // Advance from breakpoint, if set
        if (boot_fsm_ps == BOOT_WAIT) {
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);
        }
        VPRINTF(LOW, "MCU: Set BootFSM GO\n");

        // TODO Mailbox command test

}
