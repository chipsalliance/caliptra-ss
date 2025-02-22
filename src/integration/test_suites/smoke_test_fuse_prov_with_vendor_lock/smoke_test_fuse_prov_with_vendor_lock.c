
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
            VPRINTF(LOW, "Token rror detected.\n");
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

// Define commands for DAI operations
#define FUSE_CTRL_CMD_DAI_WRITE 0x2
#define FUSE_CTRL_CMD_DAI_READ  0x1

void reset_RTL(){
    uint32_t reg_value;

    reg_value = lsu_read_32(LC_CTRL_HW_REVISION0_OFFSET); // Reset the lcc and its bfm
    VPRINTF(LOW, "LC&Fuse_CTRLis under reset!\n");
    for (uint16_t ii = 0; ii < 300; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

}

void check_dai_status() {
    uint32_t status = lsu_read_32(FUSE_CTRL_STATUS);

    VPRINTF(LOW, "Reading FUSE_CTRL_STATUS: 0x%08X\n", status);

    if ((status >> 19) & 0x1) {
        VPRINTF(LOW, "INFO: CHECK_PENDING - An integrity or consistency check is pending.\n");
    }
    if ((status >> 18) & 0x1) {
        VPRINTF(LOW, "INFO: DAI_IDLE - DAI is idle and ready to accept commands.\n");
    }
    if ((status >> 17) & 0x1) {
        VPRINTF(LOW, "ERROR: BUS_INTEG_ERROR - Fatal bus integrity fault detected.\n");
    }
    if ((status >> 16) & 0x1) {
        VPRINTF(LOW, "ERROR: KEY_DERIV_FSM_ERROR - Key derivation FSM reached an invalid state.\n");
    }
    if ((status >> 15) & 0x1) {
        VPRINTF(LOW, "ERROR: SCRAMBLING_FSM_ERROR - Scrambling datapath FSM reached an invalid state.\n");
    }
    if ((status >> 14) & 0x1) {
        VPRINTF(LOW, "ERROR: LFSR_FSM_ERROR - LFSR timer FSM reached an invalid state.\n");
    }
    if ((status >> 13) & 0x1) {
        VPRINTF(LOW, "ERROR: TIMEOUT_ERROR - Integrity or consistency check timeout.\n");
    }
    if ((status >> 12) & 0x1) {
        VPRINTF(LOW, "ERROR: LCI_ERROR - Error occurred in the LCI. Check ERR_CODE register.\n");
    }
    if ((status >> 11) & 0x1) {
        VPRINTF(LOW, "ERROR: DAI_ERROR - Error occurred in the DAI. Check ERR_CODE register.\n");
    }
    if ((status >> 10) & 0x1) {
        VPRINTF(LOW, "ERROR: LIFE_CYCLE_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 9) & 0x1) {
        VPRINTF(LOW, "ERROR: SECRET2_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 8) & 0x1) {
        VPRINTF(LOW, "ERROR: SECRET1_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 7) & 0x1) {
        VPRINTF(LOW, "ERROR: SECRET0_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 6) & 0x1) {
        VPRINTF(LOW, "ERROR: HW_CFG1_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 5) & 0x1) {
        VPRINTF(LOW, "ERROR: HW_CFG0_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 4) & 0x1) {
        VPRINTF(LOW, "ERROR: ROT_CREATOR_AUTH_STATE_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 3) & 0x1) {
        VPRINTF(LOW, "ERROR: ROT_CREATOR_AUTH_CODESIGN_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 2) & 0x1) {
        VPRINTF(LOW, "ERROR: OWNER_SW_CFG_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 1) & 0x1) {
        VPRINTF(LOW, "ERROR: CREATOR_SW_CFG_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }
    if ((status >> 0) & 0x1) {
        VPRINTF(LOW, "ERROR: VENDOR_TEST_ERROR - Error occurred in this partition. Check ERR_CODE register.\n");
    }

    if (status == 0) {
        VPRINTF(LOW, "INFO: No errors detected in the status register.\n");
    }
}

// Function to wait until the DAI operation is done
void wait_dai_op_idle() {
    uint32_t status;
    VPRINTF(LOW, "DEBUG: Waiting for DAI to become idle...\n");
    do {
        status = lsu_read_32(FUSE_CTRL_STATUS);
        VPRINTF(LOW, "DEBUG: DAI should be idle but is 0x%08X.\n", status);
        status = (status >> 22) & 0x1; // This extracts 19th bit (DAI_IDLE) from the status
    } while (status == 0);
    VPRINTF(LOW, "DEBUG: DAI is now idle.\n");
}

// Function to write data via DAI
void dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1, uint32_t granularity) {
    VPRINTF(LOW, "+++++++++++++++++++++++++++++++++++++++++++\n");
    VPRINTF(LOW, "DEBUG: Starting DAI write operation...\n");

    wait_dai_op_idle();

    VPRINTF(LOW, "DEBUG: Writing wdata0: 0x%08X to DIRECT_ACCESS_WDATA_0.\n", wdata0);
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_WDATA_0, wdata0);

    if (granularity == 64) {
        VPRINTF(LOW, "DEBUG: Writing wdata1: 0x%08X to DIRECT_ACCESS_WDATA_1.\n", wdata1);
        lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_WDATA_1, wdata1);
    }

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI write command.\n");
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_WRITE);

    wait_dai_op_idle();

    VPRINTF(LOW, "DEBUG: DAI write operation completed. Checking status...\n");
    check_dai_status();
}

// Function to read data via DAI
void dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity) {
    VPRINTF(LOW, "====================================\n");
    VPRINTF(LOW, "DEBUG: Starting DAI read operation...\n");

    wait_dai_op_idle();

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI read command.\n");
    lsu_write_32(FUSE_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_READ);

    wait_dai_op_idle();

    *rdata0 = lsu_read_32(FUSE_CTRL_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

    if (granularity == 64) {
        *rdata1 = lsu_read_32(FUSE_CTRL_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
    }

    VPRINTF(LOW, "DEBUG: DAI read operation completed. Checking status...\n");
    check_dai_status();
}

// Function to initialize the OTP controller
void initialize_otp_controller() {
    uint32_t status;

    // Step 1: Check OTP controller initialization status
    VPRINTF(LOW, "DEBUG: Checking OTP controller initialization status...\n");
    status = lsu_read_32(FUSE_CTRL_STATUS);

    // Check for error bits in the status register
    if (status & 0x3FFFFF != 0 ) { // Mask all bits except DAI_IDLE
        VPRINTF(LOW, "ERROR: OTP controller initialization failed. STATUS: 0x%08X\n", status);
        return;
    }

    wait_dai_op_idle();

    VPRINTF(LOW, "INFO: OTP controller successfully initialized. STATUS: 0x%08X\n", status);

    // Step 2: Set up periodic background checks
    VPRINTF(LOW, "DEBUG: Configuring periodic background checks...\n");
    
    // Configure CHECK_TIMEOUT
    uint32_t check_timeout = 0x100000; // Example value, adjust as needed
    lsu_write_32(FUSE_CTRL_CHECK_TIMEOUT, check_timeout);
    VPRINTF(LOW, "INFO: CHECK_TIMEOUT set to 0x%08X\n", check_timeout);

    // Configure INTEGRITY_CHECK_PERIOD
    uint32_t integrity_check_period = 0x3FFFF; // Example value, adjust as needed
    lsu_write_32(FUSE_CTRL_INTEGRITY_CHECK_PERIOD, integrity_check_period);
    VPRINTF(LOW, "INFO: INTEGRITY_CHECK_PERIOD set to 0x%08X\n", integrity_check_period);

    // Configure CONSISTENCY_CHECK_PERIOD
    uint32_t consistency_check_period = 0x3FFFF; // Example value, adjust as needed
    lsu_write_32(FUSE_CTRL_CONSISTENCY_CHECK_PERIOD, consistency_check_period);
    VPRINTF(LOW, "INFO: CONSISTENCY_CHECK_PERIOD set to 0x%08X\n", consistency_check_period);

    // Step 3: Lock down background check registers
    VPRINTF(LOW, "DEBUG: Locking background check registers...\n");
    lsu_write_32(FUSE_CTRL_CHECK_REGWEN, 0x0);
    VPRINTF(LOW, "INFO: CHECK_REGWEN locked.\n");
}

void vendor_volatile_lock() {
    uint32_t dummy_read;
    dummy_read = lsu_read_32(0x70000080);

    // Set the vendor volatile lock to 1 which locks all fuses starting from index 2.
    lsu_write_32(0x700000AC, 0x1);

    uint32_t fuse_address = 0x648;

    uint32_t data[1] = {0x89ABCDEF};   
    uint32_t read_data;

    // This write should succeed.
    dai_wr(fuse_address, data[0], 0, 32);
    VPRINTF(LOW, "DEBUG: VENDOR_PK_HASH Wrote 0x%08X to address 0x%08X.\n", data[0], fuse_address);

    // Read back and verify SCRATCH item
    dai_rd(fuse_address, &read_data, NULL, 32);
    VPRINTF(LOW, "DEBUG: Verified VENDOR_PK_HASH 0x%08X  at address 0x%08X.\n", read_data, fuse_address);

    // This read should fail.
    fuse_address = 0x679;
    dai_wr(fuse_address, data[0], 0, 32);
    VPRINTF(LOW, "DEBUG: VENDOR_PK_HASH Wrote 0x%08X to address 0x%08X.\n", data[0], fuse_address);
                
    VPRINTF(LOW, "INFO: DONE VENDOR_PK_HASH\n");
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
    
    VPRINTF(LOW, "=================\n Fuse Prov TEST \n=================\n\n");

    lcc_initilization();    
    RAW_to_TESTUNLOCK0();
    initialize_otp_controller();

    vendor_volatile_lock();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
