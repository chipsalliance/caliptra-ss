/*
    Run this test with the following command
    submit_i cpt_build_ss -tc caliptra_ss_jtag_uds_prog -op -to 5000000
*/




#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "fuse_ctrl_address_map.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
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
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    const uint32_t mbox_dlen = 64;
    uint32_t mbox_data[] = { 0x00000000,
                             0x11111111,
                             0x22222222,
                             0x33333333,
                             0x44444444,
                             0x55555555,
                             0x66666666,
                             0x77777777,
                             0x88888888,
                             0x99999999,
                             0xaaaaaaaa,
                             0xbbbbbbbb,
                             0xcccccccc,
                             0xdddddddd,
                             0xeeeeeeee,
                             0xffffffff };
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t cptra_boot_go;

    uint32_t vector[16] = {
        0xba03f195, 0xcfb86f60, 0x6ce5adc0, 0x90be97cd,
        0x5021e4df, 0x25edab7d, 0xb141e89a, 0xd115a87b,
        0x28abfbfa, 0x5a8f41,   0x44901cee, 0x4961df3f,
        0x8db3e5ea, 0x8d489c51, 0x90e26b42, 0xaf9369e
    };
    // VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    mcu_mci_boot_go();
    cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));
    uint32_t base_address = SOC_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0;
    for (int i = 0; i < 2; i++) {
        VPRINTF(LOW, "MCU: writing 0x%x to address of 0x%x\n", vector[i], base_address + (i * 4));
        lsu_write_32(base_address + (i * 4), vector[i]);
    }

    for (uint32_t ii = 0; ii < 500; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG MANUF DEBUG TEST with ROM \n=================\n\n");

    lcc_initialization();
    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    reset_fc_lcc_rtl();

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
    

    cptra_boot_go = 0;
    VPRINTF(LOW, "MCU: waits in success loop\n");
    while(cptra_boot_go != SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK){
        cptra_boot_go = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP) & SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK;
        for (uint32_t ii = 0; ii < 500; ii++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

    VPRINTF(LOW, "MCU: Success done\n");
    reset_fc_lcc_rtl();
    for (uint32_t ii = 0; ii < 5000; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }


    SEND_STDOUT_CTRL(0xff);

}
