
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "fuse_ctrl_address_map.h"
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

void main (void) {
    int argc=0;
    char *argv[1];
    //enum boot_fsm_state_e boot_fsm_ps;
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
    uint32_t registers[] = FUSE_CTRL_REGISTERS; 
    int num_registers = sizeof(registers) / sizeof(registers[0]); 
    uint32_t random_value;
    int random_index;
    uint32_t write_data = 0xc001cafe;

    int array_size = sizeof(mbox_data) / sizeof(mbox_data[0]);

    VPRINTF(LOW, "=================\nMCU Fuse Controller Bringup\n=================\n\n")
    
    VPRINTF(LOW, "Reading all Fuse Controller CSRs\n\n");
    for (int i = 0; i < num_registers; i++) { 
        uint32_t reg_value = lsu_read_32(registers[i]); 
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x\n", registers[i], reg_value); 
    }

    VPRINTF(LOW, "Writing all Fuse Controller CSRs\n\n");
    for (int i = 0; i < num_registers; i++) { 
        // Write 0xc001cafe to register
        lsu_write_32(registers[i], write_data); 
        VPRINTF(LOW, "Write Register [0x%08x]: 0x%08x\n", registers[i], write_data); 
    }

    VPRINTF(LOW, "Reading all Fuse Controller CSRs after write\n\n");
    for (int i = 0; i < num_registers; i++) { 
        uint32_t reg_value = lsu_read_32(registers[i]); 
        VPRINTF(LOW, "Read Register [0x%08x]: 0x%08x\n", registers[i], reg_value); 
    }

    SEND_STDOUT_CTRL(0xff);

}
