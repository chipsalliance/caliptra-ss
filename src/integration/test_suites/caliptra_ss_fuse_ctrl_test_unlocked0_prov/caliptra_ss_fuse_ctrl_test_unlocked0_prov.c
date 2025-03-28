#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include <stdbool.h>

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

// XXX: Fuse addresses, eventually these should be generated automatically.
static uint32_t _addr0[] = { 0x000 };
static uint32_t _addr1[] = { 0x048 };
static uint32_t _addr2[] = { 0x090 };
static uint32_t _addr3[] = { 0x0A0 };
static uint32_t _addr4[] = { 0x0B0 };
static uint32_t _addr5[] = { 0x0C0 };
static uint32_t _addr6[] = { 0x0D0, 0x0D1, 0x131, 0x141, 0x143 };
static uint32_t _addr7[] = { 0x500, 0x510, 0x520, 0x530, 0x540, 0x550, 0x560, 0x570, 0x580, 0x590, 0x5A0 };
static uint32_t _addr8[] = { 0x620, 0x650 };
static uint32_t _addr9[] = { 
    0x660, 0x690, 0x691, 0x6C1, 0x6C2, 0x6F2, 0x6F3, 0x723, 0x724, 0x754, 0x755, 0x785,
    0x786, 0x7B6, 0x7B7, 0x7E7, 0x7E8, 0x818, 0x819, 0x849, 0x84A, 0x87A, 0x87B, 0x8AB,
    0x8AC, 0x8DC, 0x8DD, 0x90D, 0x90E, 0x93E, 0x93F
};
static uint32_t _addr10[] = { 
    0x950, 0x951, 0x955, 0x959, 0x95A, 0x95E, 0x962, 0x963, 0x967, 0x96B, 0x96C, 0x970,
    0x974, 0x975, 0x979, 0x97D, 0x97E, 0x982, 0x986, 0x987, 0x98B, 0x98F, 0x990, 0x994,
    0x998, 0x999, 0x99D, 0x9A1, 0x9A2, 0x9A6, 0x9AA, 0x9AB, 0x9AF, 0x9B3, 0x9B4, 0x9B8,
    0x9BC, 0x9BD, 0x9C1, 0x9C5, 0x9C6, 0x9CA, 0x9CE, 0x9CF, 0x9D3, 0x9D7, 0x9D8, 0x9DC
};
static uint32_t _addr11[] = { 
    0x9E8, 0xA08, 0xA28, 0xA48, 0xA68, 0xA88, 0xAA8, 0xAC8, 0xAE8, 0xB08, 0xB28, 0xB48,
    0xB68, 0xB88, 0xBA8, 0xBC8
};
static uint32_t _addr12[] = { 
    0xBF0, 0xC10, 0xC30, 0xC50, 0xC70, 0xC90, 0xCB0, 0xCD0, 0xCF0, 0xD10, 0xD30, 0xD50,
    0xD70, 0xD90, 0xDB0, 0xDD0
};

typedef struct {
    uint32_t address;
    uint32_t granularity;
    bool is_software;

    uint32_t num_fuses;
    uint32_t *fuse_addresses;
    uint32_t digest_address;
} partition_t;

// XXX: Fuse addresses, eventually these should be generated automatically.
static partition_t partitions[13] = {
    // SECRET_TEST_UNLOCK_PARTITION
    { .address = 0x000, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr0, .digest_address = 0x040 },
     // SECRET_MANUF_PARTITION
    { .address = 0x048, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr1, .digest_address = 0x088 },
    // SECRET_PROD_PARTITION_0
    { .address = 0x090, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr2, .digest_address = 0x098 },
    // SECRET_PROD_PARTITION_1 
    { .address = 0x0A0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr3, .digest_address = 0x0A8 },
    // SECRET_PROD_PARTITION_2 
    { .address = 0x0B0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr4, .digest_address = 0x0B8 },
    // SECRET_PROD_PARTITION_3
    { .address = 0x0C0, .granularity = 64, .is_software = false, .num_fuses = 1,  .fuse_addresses = _addr5, .digest_address = 0x0C8 },
    // SW_MANUF_PARTITION
    { .address = 0x0D0, .granularity = 32, .is_software = true,  .num_fuses = 5,  .fuse_addresses = _addr6, .digest_address = 0x4F8 }, 
    // SECRET_LC_TRANSITION_PARTITION
    { .address = 0x500, .granularity = 64, .is_software = false, .num_fuses = 11, .fuse_addresses = _addr7, .digest_address = 0x5B0 }, 
    // VENDOR_HASHES_MANUF_PARTITION
    { .address = 0x620, .granularity = 32, .is_software = true,  .num_fuses = 2,  .fuse_addresses = _addr8, .digest_address = 0x658 }, 
    // VENDOR_HASHES_PROD_PARTITION
    { .address = 0x660, .granularity = 32, .is_software = true,  .num_fuses = 31, .fuse_addresses = _addr9, .digest_address = 0x948 }, 
    // VENDOR_REVOCATIONS_PROD_PARTITION
    { .address = 0x950, .granularity = 32, .is_software = true,  .num_fuses = 48, .fuse_addresses = _addr10, .digest_address = 0x9E0 }, 
    // VENDOR_SECRET_PROD_PARTITION
    { .address = 0x9E8, .granularity = 64, .is_software = false, .num_fuses = 16, .fuse_addresses = _addr11, .digest_address = 0xBE8 },
    // VENDOR_NON_SECRET_PROD_PARTITION
    { .address = 0xBF0, .granularity = 64, .is_software = true,  .num_fuses = 16, .fuse_addresses = _addr12, .digest_address = 0xFA0 }, 
};

void test_unlocked0_provision() {
    const uint32_t sentinel = 0xA5;

    uint32_t act_state = lsu_read_32(LC_CTRL_LC_STATE_OFFSET);
    uint32_t exp_state = calc_lc_state_mnemonic(TEST_UNLOCKED0);
    if (act_state != exp_state) {
        VPRINTF(LOW, "ERROR: incorrect state: exp: %08X, act: %08X\n", act_state, exp_state);
        exit(1);
    }

    uint32_t read_value, zero;
    uint32_t rnd_fuse_addresses[13];

    for (uint32_t i = 0; i < 13; i++) {
        if (partitions[i].address <= 0x80) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }

        rnd_fuse_addresses[i] = partitions[i].fuse_addresses[xorshift32() % partitions[i].num_fuses];
        
        dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, 0);
        
        dai_rd(rnd_fuse_addresses[i], &read_value, &zero, partitions[i].granularity, 0);
        if ((read_value & 0xFF) != sentinel) {
            VPRINTF(LOW, "ERROR: incorrect value: exp: %08X act: %08X\n", read_value, sentinel);
        }

        if (partitions[i].is_software) {
            dai_wr(partitions[i].digest_address, sentinel, 0, 64, 0);
        } else {
            calculate_digest(partitions[i].address);
        }
    } 

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    for (uint32_t i = 0; i < 13; i++) {
        if (partitions[i].address <= 0x80) {
            grant_caliptra_core_for_fc_writes();
        } else {
            grant_mcu_for_fc_writes(); 
        }

        dai_wr(rnd_fuse_addresses[i], sentinel, 0, partitions[i].granularity, FUSE_CTRL_STATUS_DAI_ERROR_MASK);
        
        if (partitions[i].is_software) {
            dai_rd(rnd_fuse_addresses[i], &read_value, &zero, partitions[i].granularity, 0);
            if ((read_value & 0xFF) != sentinel) {
                VPRINTF(LOW, "ERROR: incorrect value: exp: %08X act: %08X\n", read_value, sentinel);
            }
        }
    } 
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n")
    
    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset 
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO %x\n", cptra_boot_go);
      
    lcc_initialization();
    grant_mcu_for_fc_writes(); 

    transition_state(TEST_UNLOCKED0, raw_unlock_token[0], raw_unlock_token[1], raw_unlock_token[2], raw_unlock_token[3], 1);
    wait_dai_op_idle(0);

    initialize_otp_controller();

    test_unlocked0_provision();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
