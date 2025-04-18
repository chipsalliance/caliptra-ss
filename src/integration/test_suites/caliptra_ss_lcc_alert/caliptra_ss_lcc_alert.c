#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
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


void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
      
    lcc_initialization();

    // Fault a bit in an AXI write request, which will transfer the LCC into a terminal state.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_LCC_FATAL_BUS_INTEG_ERROR);    
    lsu_write_32(SOC_LC_CTRL_ALERT_TEST, 0x1);

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (!((lsu_read_32(SOC_LC_CTRL_STATUS) >> LC_CTRL_STATUS_BUS_INTEG_ERROR_LOW) & 0x1)) {
        VPRINTF(LOW, "ERROR: bus integ error not signaled in status register\n");
    }

    SEND_STDOUT_CTRL(0xff);
}
