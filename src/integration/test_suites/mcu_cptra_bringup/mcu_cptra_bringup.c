
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

void main (void) {
        int argc=0;
        char *argv[1];

        VPRINTF(LOW, "=================\nMCU Caliptra Bringup\n=================\n\n")

        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
        for (uint8_t ii = 0; ii < 64; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO, SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK);

}
