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

volatile char* stdout = (char *)0x21000410;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


#define CLAIM_TRANS_VAL       0x96

// This packs a 5-bit lifecycle state value repeatedly into a 30-bit field.
// Because your design reads the repeated bits for redundancy.
static inline uint32_t pack_lc_state_5bit(uint32_t lc_state) {
    // Mask the 5 bits
    uint32_t val5 = lc_state & 0x1F;
    // Repeat that 5-bit pattern across 6 chunks = 30 bits total
    // The hardware expects repeated coverage for redundancy
    return (val5 << 25) |
           (val5 << 20) |
           (val5 << 15) |
           (val5 << 10) |
           (val5 <<  5) |
            val5;
}

// Common function to request a life cycle transition
//   next_lc_state_30   = repeated 5-bit code
//   token_*            = user tokens (128 bits), if needed
//   use_token          = 1 to write tokens, 0 otherwise
void sw_transition_req(uint32_t next_lc_state_30,
                       uint32_t token_127_96,
                       uint32_t token_95_64,
                       uint32_t token_63_32,
                       uint32_t token_31_0,
                       uint32_t use_token) 
{
    // Acquire claim transition lock
    while (1) {
        lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, CLAIM_TRANS_VAL);
        uint32_t reg_value = lsu_read_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET);
        if ((reg_value & 0xFF) == CLAIM_TRANS_VAL) {
            break;
        }
    }
    VPRINTF(LOW, "LC_CTRL: Transition mutex acquired.\n");

    // Write target LC state
    VPRINTF(LOW, "Setting next lifecycle state [0x%08x]: 0x%08x\n", LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state_30);
    lsu_write_32(LC_CTRL_TRANSITION_TARGET_OFFSET, next_lc_state_30);

    // Conditionally write tokens
    if (use_token) {
        // Four 32-bit writes for the 128-bit token
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_127_96);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_127_96);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_95_64);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_95_64);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_63_32);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_63_32);
        VPRINTF(LOW, "Writing tokens: 0x%08x\n", token_31_0);
        lsu_write_32(LC_CTRL_TRANSITION_TOKEN_0_OFFSET, token_31_0);
        VPRINTF(LOW, "LC_CTRL: Tokens were written.\n");
    }
    else{
        VPRINTF(LOW, "LC_CTRL: No tokens is written.\n");
    }

    // Trigger transition command
    VPRINTF(LOW, "Triggering transition command [0x%08x]: 0x1\n", LC_CTRL_TRANSITION_CMD_OFFSET);
    lsu_write_32(LC_CTRL_TRANSITION_CMD_OFFSET, 0x1);

    // Poll status register
    while (1) {
        uint32_t s = lsu_read_32(LC_CTRL_STATUS_OFFSET);
        uint32_t transition_ok = (s >> 3) & 1; // bit [3]
        uint32_t trans_cnt_err = (s >> 4) & 1; // bit [4]
        uint32_t trans_err     = (s >> 5) & 1; // bit [5]
        uint32_t token_err     = (s >> 6) & 1; // bit [6]
        uint32_t rma_err       = (s >> 7) & 1; // bit [7]
        uint32_t otp_err       = (s >> 8) & 1; // bit [8]
        uint32_t state_err     = (s >> 9) & 1; // bit [9]

        if (transition_ok) {
            VPRINTF(LOW, "LC_CTRL: Transition successful.\n");
            break;
        }
        if (trans_cnt_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: TRANS CNT error.\n");
            break;
        }
        if (trans_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: TRANS error.\n");
            break;
        }
        if (token_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: Token error.\n");
            break;
        }
        if (rma_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: RMA error.\n");
            break;
        }
        if (otp_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: OTP error.\n");
            break;
        }
        if (state_err) {
            VPRINTF(LOW, "LC_CTRL ERROR: STATE error.\n");
            break;
        }
    }

    // Release the mutex
    lsu_write_32(LC_CTRL_CLAIM_TRANSITION_IF_OFFSET, 0x0);
    VPRINTF(LOW, "LC_CTRL: Mutex released.\n");
}

// One-time initialization
void lcc_initialization(void) {
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

// Helper to simulate “reset” or “bring-up” of the LC controller between transitions.
// Adjust or remove as needed for your environment.
static inline void lc_ctrl_wait_after_transition() {
    // Possibly read some register for side-effects.
    uint32_t reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET);
    (void)reg_value; // Just to do something with it.

    // Insert NOPs for some cycles
    for (uint32_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }
    // Insert NOPs for some cycles
    for (uint32_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }
    
}

void check_lc_state(uint32_t expected) {
    for (uint32_t i = 0; i < 512; i++) {
        __asm__ volatile ("nop");
    }
    // Read LC_STATE register and mask out the reserved bits (bits 31:30)
    uint32_t reg_val = lsu_read_32(LC_CTRL_LC_STATE_OFFSET) & 0x3FFFFFFF;
    const char *state_str;

    // Decode the redundant encoding.  (The encoding is defined as six repeated 5-bit values.)
    switch (reg_val) {
        case 0x00000000: state_str = "RAW"; break;
        case 0x02108421: state_str = "TEST_UNLOCKED0"; break;
        case 0x04210842: state_str = "TEST_LOCKED0"; break;
        case 0x06318c63: state_str = "TEST_UNLOCKED1"; break;
        case 0x08421084: state_str = "TEST_LOCKED1"; break;
        case 0x0a5294a5: state_str = "TEST_UNLOCKED2"; break;
        case 0x0c6318c6: state_str = "TEST_LOCKED2"; break;
        case 0x0e739ce7: state_str = "TEST_UNLOCKED3"; break;
        case 0x10842108: state_str = "TEST_LOCKED3"; break;
        case 0x1294a529: state_str = "TEST_UNLOCKED4"; break;
        case 0x14a5294a: state_str = "TEST_LOCKED4"; break;
        case 0x16b5ad6b: state_str = "TEST_UNLOCKED5"; break;
        case 0x18c6318c: state_str = "TEST_LOCKED5"; break;
        case 0x1ad6b5ad: state_str = "TEST_UNLOCKED6"; break;
        case 0x1ce739ce: state_str = "TEST_LOCKED6"; break;
        case 0x1ef7bdef: state_str = "TEST_UNLOCKED7"; break;
        case 0x21084210: state_str = "DEV"; break;
        case 0x2318c631: state_str = "PROD"; break;
        case 0x25294a52: state_str = "PROD_END"; break;
        case 0x2739ce73: state_str = "RMA"; break;
        case 0x294a5294: state_str = "SCRAP"; break;
        case 0x2b5ad6b5: state_str = "POST_TRANSITION"; break;
        case 0x2d6b5ad6: state_str = "ESCALATE"; break;
        case 0x2f7bdef7: state_str = "INVALID"; break;
        default:         state_str = "UNKNOWN"; break;
    }

    VPRINTF(LOW, "LC_STATE register: 0x%08x, Decoded state: %s\n", reg_val, state_str);

    if (reg_val != expected){
        VPRINTF(LOW, "LC_STATE ERROR: Expected state was: %08d\n", expected&0x1F);
    }
    else{
        VPRINTF(LOW, "LC_STATE transition is verified\n");
    }
}

void test_all_lc_transitions_no_RMA(void) {
    // The *decoded* enumeration values you gave in the source code
    // LcStRaw=0, LcStTestUnlocked0=1, LcStTestLocked0=2, etc.
    // The final step is to go to Scrap (20).
    // (We skip any special RMA strap toggling here; add it if needed.)
    uint32_t state_sequence[] = {
        0,  // LcStRaw
        1,  // LcStTestUnlocked0
        2,  // LcStTestLocked0
        3,  // LcStTestUnlocked1
        4,  // LcStTestLocked1
        5,  // LcStTestUnlocked2
        6,  // LcStTestLocked2
        7,  // LcStTestUnlocked3
        8,  // LcStTestLocked3
        9,  // LcStTestUnlocked4
        10, // LcStTestLocked4
        11, // LcStTestUnlocked5
        12, // LcStTestLocked5
        13, // LcStTestUnlocked6
        14, // LcStTestLocked6
        15, // LcStTestUnlocked7
        16, // LcStDev
        17, // LcStProd
        18, // LcStProdEnd
        20  // LcStScrap
    };

    // If you only need tokens on the very first transition (Raw -> TestUnlocked0), 
    // we can store a parallel “bool” array to indicate usage.
    // For instance, only use tokens for the 2nd element (transition *into* index1).
    // Adjust as needed for real usage.
    uint8_t use_token[] = {
        0, // from "no previous" to Raw
        1, // from Raw -> TestUnlocked0: real token
        0, // from TestUnlocked0 -> TestLocked0
        1, // ...
        0, // from TestUnlocked1 -> TestLocked1
        1,
        0, // from TestUnlocked2 -> TestLocked2
        1,
        0, // from TestUnlocked3 -> TestLocked3
        1,
        0, // from TestUnlocked4 -> TestLocked4
        1,
        0, // from TestUnlocked5 -> TestLocked5
        1,
        0, // from TestUnlocked6 -> TestLocked6
        1,
        1, // from TestUnlocked7 -> MANUF
        1, // from MANUF -> PROD
        1, // from PROD -> PROD_END
        0  // from PROD -> SCRAP
    };

    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    const uint32_t real_token[4] = {
        0xf12a5911, 0x421748a2, 0xadfc9693, 0xef1fadea
    };
    uint32_t token_value = 1;

    // We start at index0=0 (Raw). We do transitions *from* each state
    // to the *next* in the sequence. So we loop from i=0 to i=(N-2).
    int n_states = sizeof(state_sequence)/sizeof(state_sequence[0]);

    for (int i = 0; i < (n_states - 1); i++) {
        uint32_t from_state = state_sequence[i];
        uint32_t to_state   = state_sequence[i+1];
        VPRINTF(LOW, "\n=== Transition from %08d to %08d ===\n", 
                from_state, to_state);

        // Pack the 5-bit repeated code
        uint32_t next_lc_state_30 = pack_lc_state_5bit(to_state);
        
        if (i == 0){
             sw_transition_req(next_lc_state_30,
                              real_token[0],
                              real_token[1],
                              real_token[2],
                              real_token[3],
                              1 /*use_token*/);
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);
        }
        else if (i<15){

            // Decide whether to use a token
            if (use_token[i+1]) {
                // We’re using the  token for demonstration.
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                1 /*use_token*/);
            } else {
                // No token is needed
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            }
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);

            VPRINTF(LOW, "\n=== Skip Transition from %08d to %08d ===\n", 
                i, i+1);
        }
        else{

            // Decide whether to use a token
            if (use_token[i+1]) {
                // We’re using the  token for demonstration.
                sw_transition_req(next_lc_state_30,
                                token_value, token_value, token_value, token_value,
                                1 /*use_token*/);
            } else {
                // No token is needed
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            }
            token_value = token_value +1;
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);
        }

        // Perform your local “reset/wait” after each transition
    }

    VPRINTF(LOW, "All transitions complete.\n");
}


void no_Token_from_Unlocked_to_RMA(void) {

    uint32_t reg_value;
    
    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    const uint32_t real_token[4] = {
        0xf12a5911, 0x421748a2, 0xadfc9693, 0xef1fadea
    };
    uint32_t from_state = 0;
    uint32_t to_state   = 1;
    VPRINTF(LOW, "\n=== Transition from 0x%08x to 0x%08x ===\n", 
            from_state, to_state);

    // Pack the 5-bit repeated code
    uint32_t next_lc_state_30 = pack_lc_state_5bit(to_state);

    sw_transition_req(next_lc_state_30,
                              real_token[0],
                              real_token[1],
                              real_token[2],
                              real_token[3],
                              1 /*use_token*/);
    lc_ctrl_wait_after_transition();
    // check_lc_state(next_lc_state_30);

    from_state = 1;
    to_state   = 19;
    VPRINTF(LOW, "\n=== Transition from 0x%08x to 0x%08x ===\n", 
            from_state, to_state);

    // Pack the 5-bit repeated code
    next_lc_state_30 = pack_lc_state_5bit(to_state);

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: RMA strap is high!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);

    
    lc_ctrl_wait_after_transition();
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in RMA state!\n");

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC_CTRL: RMA strap is low!\n");
    for (uint8_t ii = 0; ii < 16; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    // check_lc_state(next_lc_state_30);
    VPRINTF(LOW, "All transitions complete.\n");
}

void test_all_lc_transitions_no_PROD_END(void) {
    // The *decoded* enumeration values you gave in the source code
    // LcStRaw=0, LcStTestUnlocked0=1, LcStTestLocked0=2, etc.
    // The final step is to go to Scrap (20).
    // (We skip any special RMA strap toggling here; add it if needed.)
    uint32_t state_sequence[] = {
        0,  // LcStRaw
        1,  // LcStTestUnlocked0
        2,  // LcStTestLocked0
        3,  // LcStTestUnlocked1
        4,  // LcStTestLocked1
        5,  // LcStTestUnlocked2
        6,  // LcStTestLocked2
        7,  // LcStTestUnlocked3
        8,  // LcStTestLocked3
        9,  // LcStTestUnlocked4
        10, // LcStTestLocked4
        11, // LcStTestUnlocked5
        12, // LcStTestLocked5
        13, // LcStTestUnlocked6
        14, // LcStTestLocked6
        15, // LcStTestUnlocked7
        16, // LcStDev
        17, // LcStProd
        19, // LcStRMA
        20  // LcStScrap
    };

    // If you only need tokens on the very first transition (Raw -> TestUnlocked0), 
    // we can store a parallel “bool” array to indicate usage.
    // For instance, only use tokens for the 2nd element (transition *into* index1).
    // Adjust as needed for real usage.
    uint8_t use_token[] = {
        0, // from "no previous" to Raw
        1, // from Raw -> TestUnlocked0: real token
        0, // from TestUnlocked0 -> TestLocked0
        1, // ...
        0, // from TestUnlocked1 -> TestLocked1
        1,
        0, // from TestUnlocked2 -> TestLocked2
        1,
        0, // from TestUnlocked3 -> TestLocked3
        1,
        0, // from TestUnlocked4 -> TestLocked4
        1,
        0, // from TestUnlocked5 -> TestLocked5
        1,
        0, // from TestUnlocked6 -> TestLocked6
        1,
        1, // from TestUnlocked7 -> MANUF
        1, // from MANUF -> PROD
        1, // from PROD -> RMA
        0  // from PROD -> SCRAP
    };

    // Example token for the Raw->TestUnlocked0 jump (128 bits).
    // Adjust to match your real raw-unlock token if needed.
    const uint32_t real_token[4] = {
        0xf12a5911, 0x421748a2, 0xadfc9693, 0xef1fadea
    };
    uint32_t token_value = 1;

    // We start at index0=0 (Raw). We do transitions *from* each state
    // to the *next* in the sequence. So we loop from i=0 to i=(N-2).
    int n_states = sizeof(state_sequence)/sizeof(state_sequence[0]);

    for (int i = 0; i < (n_states - 1); i++) {
        uint32_t from_state = state_sequence[i];
        uint32_t to_state   = state_sequence[i+1];
        VPRINTF(LOW, "\n=== Transition from %08d to %08d ===\n", 
                from_state, to_state);

        // Pack the 5-bit repeated code
        uint32_t next_lc_state_30 = pack_lc_state_5bit(to_state);
        
        if (i == 0){
             sw_transition_req(next_lc_state_30,
                              real_token[0],
                              real_token[1],
                              real_token[2],
                              real_token[3],
                              1 /*use_token*/);
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);
        }
        else if (i<15){

            // Decide whether to use a token
            if (use_token[i+1]) {
                // We’re using the  token for demonstration.
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                1 /*use_token*/);
            } else {
                // No token is needed
                sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            }
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);

            // VPRINTF(LOW, "\n=== Skip Transition from %08d to %08d ===\n", 
            //     i, i+1);
        }
        else if (i<17){
            sw_transition_req(next_lc_state_30,
                                token_value, token_value, token_value, token_value,
                                1 /*use_token*/);
            token_value = token_value +1;
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);
        }
        else if (i==17){ //RMA
            uint32_t reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
            VPRINTF(LOW, "LC_CTRL: RMA strap is high!\n");
            for (uint8_t ii = 0; ii < 16; ii++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            token_value = token_value +1;
            sw_transition_req(next_lc_state_30,
                                token_value, token_value, token_value, token_value,
                                1 /*use_token*/);
            lc_ctrl_wait_after_transition();
            for (uint8_t ii = 0; ii < 160; ii++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            VPRINTF(LOW, "LC_CTRL: CALIPTRA_SS_LC_CTRL is in RMA state!\n");

            reg_value = lsu_read_32(LC_CTRL_HW_REVISION1_OFFSET); // Reset the lcc and its bfm
            VPRINTF(LOW, "LC_CTRL: RMA strap is low!\n");
            for (uint8_t ii = 0; ii < 16; ii++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            // check_lc_state(next_lc_state_30);
        }
        else{

            sw_transition_req(next_lc_state_30,
                                0, 0, 0, 0,
                                0 /*use_token*/);
            lc_ctrl_wait_after_transition();
            // check_lc_state(next_lc_state_30);
        }

        // Perform your local “reset/wait” after each transition
    }

    VPRINTF(LOW, "All transitions complete.\n");
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
    uint32_t cptra_boot_go;
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_REG_CALIPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_REG_CALIPTRA_BOOT_GO\n");

    cptra_boot_go = lsu_read_32(SOC_MCI_REG_CALIPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);


    
    VPRINTF(LOW, "=================\n LCC State Transitions \n=================\n\n");

    // 2) Perform LC Controller initialization
    lcc_initialization();

    // 3) Run your test sequence
    // test_all_lc_transitions_no_RMA();

    // no_Token_from_Unlocked_to_RMA(); 

    test_all_lc_transitions_no_PROD_END();

    // Done
    for (uint16_t i=0; i<512; i++) {
        __asm__ volatile("nop");
    }

    SEND_STDOUT_CTRL(0xff);

}
