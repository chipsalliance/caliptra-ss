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
    grant_caliptra_core_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    // Enable `otp_operation_done` and `otp_error` interrupts.
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_ENABLE, 0x3);

    /*
     * 1: An ordinary, successful DAI operation must result in an `otp_operation_done` interrupt.
     */

    dai_wr(0x000, 0x1, 0x1, 64, 0);

    uint32_t alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x0)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
        goto epilogue;
    }
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_STATE, 0x0);

    /*
     * 2: An invalid DAI operation must result in an `otp_error` interrupt.
     */

    grant_mcu_for_fc_writes();
    dai_wr(0x048, 0x1, 0x1, 64, OTP_CTRL_STATUS_DAI_ERROR_MASK); // invalid AXI ID

    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x1)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
        goto epilogue;
    }
    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_STATE, 0x0);


    /*
     * 3: Sanity check: triggering interrupts through the `INTR_TEST` register.
     */

    lsu_write_32(SOC_OTP_CTRL_INTERRUPT_TEST, 0x3);
    
    alert_state = lsu_read_32(SOC_OTP_CTRL_INTERRUPT_STATE);
    if (((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_OPERATION_DONE_LOW) & 0x1 != 0x1) ||
        ((alert_state >> OTP_CTRL_INTERRUPT_STATE_OTP_ERROR_LOW) & 0x1 != 0x1)) {
        VPRINTF(LOW, "ERROR: wrong interrupt signaled\n");
    }

epilogue:
    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
