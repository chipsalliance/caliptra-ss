
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

volatile char* stdout = (char *)0xd0580000;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif




// DecLcStRaw = 0,
// DecLcStTestUnlocked0 = 1,
// DecLcStTestLocked0 = 2,
// DecLcStTestUnlocked1 = 3,
// DecLcStTestLocked1 = 4,
// DecLcStTestUnlocked2 = 5,
// DecLcStTestLocked2 = 6,
// DecLcStTestUnlocked3 = 7,
// DecLcStTestLocked3 = 8,
// DecLcStTestUnlocked4 = 9,
// DecLcStTestLocked4 = 10,
// DecLcStTestUnlocked5 = 11,
// DecLcStTestLocked5 = 12,
// DecLcStTestUnlocked6 = 13,
// DecLcStTestLocked6 = 14,
// DecLcStTestUnlocked7 = 15,
// DecLcStDev = 16,
// DecLcStProd = 17,
// DecLcStProdEnd = 18,
// DecLcStRma = 19,
// DecLcStScrap = 20,
// DecLcStPostTrans = 21,
// DecLcStEscalate = 22,
// DecLcStInvalid = 23


#define CLAIM_TRANS_VAL 0x96 // Tried to match MuBi8True

void lcc_initilization(){
    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    while(!(lsu_read_32(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS) & SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK));

    // Initialize fuses
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");
    uint32_t reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    uint32_t loop_ctrl = reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK; 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_READY_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = reg_value & CALIPTRA_SS_LC_CTRL_READY_MASK; 
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is ready!\n");
    reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
    loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
    while(!loop_ctrl){
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x anded with 0x%08x \n", LC_CTRL_STATUS_OFFSET, reg_value, CALIPTRA_SS_LC_CTRL_INIT_MASK); 
        reg_value = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        loop_ctrl = ((reg_value & CALIPTRA_SS_LC_CTRL_INIT_MASK)>>1) & 1; 
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is initalized!\n");
    
}

void sw_transition_req(uint32_t next_lc_state,
                        uint32_t token_127_96,
                        uint32_t token_95_64,
                        uint32_t token_63_32,
                        uint32_t token_31_0,
                        uint32_t conditional) {
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;
    int trigger_alert = 0;

    VPRINTF(LOW, "Starting sw_transition_req...\n");

    // Step 1: Set Claim Transition Register
    loop_ctrl = 0;
    while (loop_ctrl != CLAIM_TRANS_VAL) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, CLAIM_TRANS_VAL);
        reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        loop_ctrl = reg_value & CLAIM_TRANS_VAL;
        VPRINTF(LOW, "Claim Mutex Register [0x%08x]: Read 0x%08x, expected 0x%08x\n",
                LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, reg_value, CLAIM_TRANS_VAL);
    }
    VPRINTF(LOW, "LC_CTRL: Mutex successfully acquired.\n");

    // Step 3: Set Target Lifecycle State
    VPRINTF(LOW, "Setting next lifecycle state [0x%08x]: 0x%08x\n", LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);
    lsu_write_32(LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state);

    // Step 4: Write Transition Tokens
    if (conditional == 1) {        
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_127_96);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_127_96);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_95_64);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_95_64);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_63_32);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_63_32);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_31_0);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_31_0);
    }

    // Step 6: Trigger the Transition Command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    // Step 7: Poll Status Register
    VPRINTF(LOW, "Polling status register [0x%08x]...\n", LC_CTRL_STATUS_OFFSET);
    while (1) {
        status_val = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t TRANSITION_SUCCESSFUL = ((status_val & 0x8) >> 3);
        uint32_t TOKEN_ERROR = ((status_val & 0x40) >> 6);
        uint32_t OTP_ERROR = ((status_val & 0x100) >> 8);
        uint32_t RMA_ERROR = ((status_val & 0x80) >> 7);

        VPRINTF(LOW, "Status Register: 0x%08x | Transition Successful: %d | Token Error: %d | OTP Error: %d\n",
                status_val, TRANSITION_SUCCESSFUL, TOKEN_ERROR, OTP_ERROR);

        if (TRANSITION_SUCCESSFUL) {
            VPRINTF(LOW, "Transition successful.\n");
            break;
        }
        if (TOKEN_ERROR) {
            VPRINTF(LOW, "Token error detected.\n");
            break;
        }
        if (OTP_ERROR) {
            VPRINTF(LOW, "OTP error detected.\n");
            break;
        }
        if (RMA_ERROR) {
            VPRINTF(LOW, "FLASH RMA error detected.\n");
            break;
        }
    }
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);

    VPRINTF(LOW, "sw_transition_req completed.\n");
}

void RAW_to_TESTUNLOCK0(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    uint32_t next_lc_state = 0x1; // TEST_UNLOCKED0
    uint32_t next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
    uint32_t targeted_state_5 = 
        (next_lc_state_5bit << 25) | 
        (next_lc_state_5bit << 20) | 
        (next_lc_state_5bit << 15) | 
        (next_lc_state_5bit << 10) | 
        (next_lc_state_5bit << 5)  | 
        next_lc_state_5bit;

    sw_transition_req(targeted_state_5, 0xf12a5911, 0x421748a2, 0xadfc9693, 0xef1fadea, 1); //TEST_UNLOCKED0, tokenmsb, tokenlsb, conditional

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in TEST_UNLOCK0 state!\n");

}

void TESTUNLOCK0_to_N_TEST(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;
    uint32_t next_lc_state;
    uint32_t next_lc_state_5bit; 
    uint32_t targeted_state_5;

    next_lc_state = 2; // TEST_UNLOCK0
    for (uint8_t ii = 0; ii < 8; ii++) {
        next_lc_state = next_lc_state+ii;
        next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
        targeted_state_5 = 
            (next_lc_state_5bit << 25) | 
            (next_lc_state_5bit << 20) | 
            (next_lc_state_5bit << 15) | 
            (next_lc_state_5bit << 10) | 
            (next_lc_state_5bit << 5)  | 
            next_lc_state_5bit;
        sw_transition_req(targeted_state_5, 0x0, 0x0, 0x0, 0x0, 0); //DEV, tokenmsb, tokenlsb, conditional
    }
    

    sw_transition_req(targeted_state_5, 0x0, 0x0, 0x0, 0x0, 1); //DEV, tokenmsb, tokenlsb, conditional
    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in DEV state!\n");

}

void TESTUNLOCK0_to_DEV(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    uint32_t next_lc_state = 16; // DEV
    uint32_t next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
    uint32_t targeted_state_5 = 
        (next_lc_state_5bit << 25) | 
        (next_lc_state_5bit << 20) | 
        (next_lc_state_5bit << 15) | 
        (next_lc_state_5bit << 10) | 
        (next_lc_state_5bit << 5)  | 
        next_lc_state_5bit;

    sw_transition_req(targeted_state_5, 0x0, 0x0, 0x0, 0x0, 1); //DEV, tokenmsb, tokenlsb, conditional
    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in DEV state!\n");

}

void DEV_to_RMA(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    uint32_t next_lc_state = 19; // RMA
    uint32_t next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
    uint32_t targeted_state_5 = 
        (next_lc_state_5bit << 25) | 
        (next_lc_state_5bit << 20) | 
        (next_lc_state_5bit << 15) | 
        (next_lc_state_5bit << 10) | 
        (next_lc_state_5bit << 5)  | 
        next_lc_state_5bit;

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: RMA strap is high!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    sw_transition_req(targeted_state_5, 0x0, 0x0, 0x0, 0x0, 1); //DEV, tokenmsb, tokenlsb, conditional
    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in RMA state!\n");

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: RMA strap is low!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

}

void DEV_to_RMA_without_STRAP(){
    uint32_t reg_value;
    uint32_t status_val;
    uint32_t loop_ctrl;

    uint32_t next_lc_state = 19; // RMA
    uint32_t next_lc_state_5bit = next_lc_state & 0x1F; // Extract 5-bit value (DecLcStateWidth = 5)
    uint32_t targeted_state_5 = 
        (next_lc_state_5bit << 25) | 
        (next_lc_state_5bit << 20) | 
        (next_lc_state_5bit << 15) | 
        (next_lc_state_5bit << 10) | 
        (next_lc_state_5bit << 5)  | 
        next_lc_state_5bit;


    sw_transition_req(targeted_state_5, 0x0, 0x0, 0x0, 0x0, 1); //DEV, tokenmsb, tokenlsb, conditional
    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is under reset!\n");
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL cannot enter RMA state due to the STRAP!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

}



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
    
    VPRINTF(LOW, "=================\n LCC State Transitions \n=================\n\n");

    lcc_initilization();
    
    RAW_to_TESTUNLOCK0();

    TESTUNLOCK0_to_DEV();

    DEV_to_RMA_without_STRAP();

    DEV_to_RMA();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }


    SEND_STDOUT_CTRL(0xff);

}
