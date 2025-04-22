// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
#include "soc_address_map.h"
#include "css_mcu0_defines.h"
#include "mcu_isr.h"
#include <string.h>
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv-interrupts.h"
#include "printf.h"
#include "riscv_hw_if.h"


extern volatile uint32_t intr_count;
#ifdef RV_EXCEPTION_STRUCT
extern volatile rv_exception_struct_s exc_flag;
#endif

#define CPTRA_REPT_8(X) X X X X X X X X
#define CPTRA_REPT_32(Y) CPTRA_REPT_8(Y) \
                         CPTRA_REPT_8(Y) \
                         CPTRA_REPT_8(Y) \
                         CPTRA_REPT_8(Y)

//////////////////////////////////////////////////////////////////////////////
// Function Declarations
//

// Initial ISR for first redirection following an external intr trap (pointed to by mtvec)
// Machine mode interrupt service routine
// Force the alignment for mtvec.BASE.
static void std_rv_isr(void) __attribute__ ((interrupt ("machine"), aligned(4)));

void std_rv_mtvec_exception(void) __attribute__ ((interrupt ("machine"), aligned(4)));

// Nop handlers for unimplemented events "Software" and "Timer" Interrupts
// "External Interrupts" are also included in this unimplemented list, just because the
// std_rv_isr_vector_table should never reroute to External Interrupts -- Fast
// Redirect takes care of that separately
void std_rv_nop_machine(void)     __attribute__ ((interrupt ("machine") , aligned(4)));
void std_rv_mtvec_mei(void)       __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_msi(void)       __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_mti(void)       __attribute__ ((interrupt ("machine") , aligned(4) ));
void std_rv_mtvec_sei(void)       __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_ssi(void)       __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void std_rv_mtvec_sti(void)       __attribute__ ((interrupt ("machine") , aligned(4) , weak, alias("std_rv_nop_machine") ));
void nonstd_veer_mtvec_miti0(void)__attribute__ ((interrupt ("machine") , aligned(4) ));
void nonstd_veer_mtvec_mcei(void) __attribute__ ((interrupt ("machine") , aligned(4) ));


// VeeR Per-Source Vectored ISR functions
static void nonstd_veer_isr_mci  (void) __attribute__ ((interrupt ("machine")));
static void nonstd_veer_isr_i3c  (void) __attribute__ ((interrupt ("machine")));

// Could be much more fancy with C preprocessing to pair up the ISR with Vector
// numbers as defined in caliptra_defines.h.... TODO
static void          nonstd_veer_isr_0   (void) __attribute__ ((interrupt ("machine"))); // Empty function instead of function pointer for Vec 0
static void (* const nonstd_veer_isr_1 ) (void) = nonstd_veer_isr_mci;    // Definitions come from the
static void (* const nonstd_veer_isr_2 ) (void) = nonstd_veer_isr_i3c;    // param'd macro "nonstd_veer_isr" below
static void (* const nonstd_veer_isr_3 ) (void) = std_rv_nop_machine; // -------.
static void (* const nonstd_veer_isr_4 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_5 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_6 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_7 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_8 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_9 ) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_10) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_11) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_12) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_13) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_14) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_15) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_16) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_17) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_18) (void) = std_rv_nop_machine; // Unimplemented ISR
static void (* const nonstd_veer_isr_19) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_20) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_21) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_22) (void) = std_rv_nop_machine; //        | 
static void (* const nonstd_veer_isr_23) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_24) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_25) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_26) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_27) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_28) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_29) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_30) (void) = std_rv_nop_machine; //        |
static void (* const nonstd_veer_isr_31) (void) = std_rv_nop_machine; // -------'
/* vectors 32-255 are registered to vector table directly as nop isr, to
 * reduce visual clutter in this file (not expecting to test all vectors
 * in TB */

// Table defines the VeeR non-standard vectored entries as an array of
// function pointers.
// The entries in this table are entered depending on the Ext. Interrupt ID
// E.g., Interrupt ID 2 routes to the ISR defined at offset 2*4 of this table
//       Interrupt ID 0 is (by definition) not assigned, and routes to an empty ISR
// Note that each function pointer (i.e. each entry in the vector table) must
// be 4-byte aligned per the VeeR PRM, and the base address of the table (i.e.
// the value of meivt) must be 1024-byte aligned, also per the PRM
// For support of Fast Interrupt Redirect feature, this should be in DCCM
static void (* __attribute__ ((aligned(4))) nonstd_veer_isr_vector_table [CSS_MCU0_RV_PIC_TOTAL_INT_PLUS1]) (void) __attribute__ ((aligned(1024),section (".dccm.nonstd_isr.vec_table"))) = {
    nonstd_veer_isr_0,
    nonstd_veer_isr_1,
    nonstd_veer_isr_2,
    nonstd_veer_isr_3,
    nonstd_veer_isr_4,
    nonstd_veer_isr_5,
    nonstd_veer_isr_6,
    nonstd_veer_isr_7,
    nonstd_veer_isr_8,
    nonstd_veer_isr_9,
    nonstd_veer_isr_10,
    nonstd_veer_isr_11,
    nonstd_veer_isr_12,
    nonstd_veer_isr_13,
    nonstd_veer_isr_14,
    nonstd_veer_isr_15,
    nonstd_veer_isr_16,
    nonstd_veer_isr_17,
    nonstd_veer_isr_18,
    nonstd_veer_isr_19,
    nonstd_veer_isr_20,
    nonstd_veer_isr_21,
    nonstd_veer_isr_22,
    nonstd_veer_isr_23,
    nonstd_veer_isr_24,
    nonstd_veer_isr_25,
    nonstd_veer_isr_26,
    nonstd_veer_isr_27,
    nonstd_veer_isr_28,
    nonstd_veer_isr_29,
    nonstd_veer_isr_30,
    nonstd_veer_isr_31
    /* Empty definitions up to the 255 index */
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
    CPTRA_REPT_32( ,std_rv_nop_machine )
};

// Table defines the RV standard vectored entries pointed to by mtvec
// The entries in this table are entered depending on mcause
// I.e. Exceptions and External Interrupts route to entries of this table
// This table is only consulted when MTVEC[1:0] indicates a vectored mode
static void std_rv_isr_vector_table(void) __attribute__ ((naked));

// TODO args to control per-component enables
void init_interrupts(void) {

    volatile uint32_t * const mpiccfg        = (uint32_t*) VEER_MM_PIC_MPICCFG;
    volatile uint32_t * const meipls         = (uint32_t*) VEER_MM_PIC_MEIPLS;     //
    volatile uint32_t * const meies          = (uint32_t*) VEER_MM_PIC_MEIES;      // Treat these
    volatile uint32_t * const meigwctrls     = (uint32_t*) VEER_MM_PIC_MEIGWCTRLS; // as arrays
    volatile uint32_t * const meigwclrs      = (uint32_t*) VEER_MM_PIC_MEIGWCLRS;  //
    volatile uint32_t * const mci_reg        = (uint32_t*) SOC_MCI_TOP_MCI_REG_BASE_ADDR;
    volatile uint32_t * const i3c_reg        = (uint32_t*) SOC_I3CCSR_BASE_ADDR;
    volatile uint32_t * const mtime_l        = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L;
    volatile uint32_t * const mtime_h        = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H;
    volatile uint32_t * const mtimecmp_l     = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L;
    volatile uint32_t * const mtimecmp_h     = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H;
    char* DCCM = (char *) CSS_MCU0_RV_DCCM_SADR;
    uint32_t value;

    /* -- Enable standard RISC-V interrupts (mtvec etc.) -- */

    // MSTATUS (disable mie prior to setting up VeeR PIC
    // Global interrupt disable
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

    // MTVEC
    // Setup the IRQ handler entry point
    // MODE = 1 (Vectored), this needs to point to std_rv_isr_vector_table()
    // For MODE = 0 (Basic), this needs to point to std_rv_isr()
    csr_write_mtvec((uint_xlen_t) std_rv_isr_vector_table | 1);


    /* -- Enable non-standard VeeR interrupts (PIC, meivt etc.) -- */

    // MEIVT - write the nonstd vector table base address
    __asm__ volatile ("la t0, %0;\n"
                      "csrw %1, t0;\n"
                      : /* output: none */
                      : "i" ((uintptr_t) &nonstd_veer_isr_vector_table), "i" (VEER_CSR_MEIVT)  /* input : immediate  */
                      : "t0"/* clobbers: t0 */);

    // MPICCFG
    *mpiccfg = 0x0; // 0x0 - Standard compliant priority order: 0=lowest,15=highest
                    // 0x1 - Reverse priority order: 0=highest,15=lowest
    __asm__ volatile ("fence");

    // MEIPT - No interrupts masked
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (VEER_CSR_MEIPT), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // MEIPL_S - assign interrupt priorities
    meipls[CSS_MCU0_VEER_INTR_VEC_MCI] = CSS_MCU0_VEER_INTR_PRIO_MCI; __asm__ volatile ("fence");
    meipls[CSS_MCU0_VEER_INTR_VEC_I3C] = CSS_MCU0_VEER_INTR_PRIO_I3C; __asm__ volatile ("fence");
    for (uint8_t undef = CSS_MCU0_VEER_INTR_EXT_LSB; undef <= CSS_MCU0_RV_PIC_TOTAL_INT; undef++) {
        meipls[undef] = 0; __asm__ volatile ("fence"); // Set to 0 meaning NEVER interrupt
    }

    // MEICIDPL - Initialize the Claim ID priority level to 0
    //            to allow nesting interrupts (Per PRM 6.5.1)
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (VEER_CSR_MEICIDPL), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    // MEICURPL - Initialize the current priority level to 0
    //            to allow all ext intr to preempt
    __asm__ volatile ("csrwi    %0, %1" \
                      : /* output: none */        \
                      : "i" (VEER_CSR_MEICURPL), "i" (0x00)  /* input : immediate  */ \
                      : /* clobbers: none */);

    for (uint8_t vec = 1; vec <= CSS_MCU0_RV_PIC_TOTAL_INT; vec++) {
        // MEIGWCTRL_S
        meigwctrls[vec] = VEER_MEIGWCTRL_ACTIVE_HI_LEVEL;  __asm__ volatile ("fence");

        // MEIGWCLRS - Ensure all pending bits are clear in the gateway
        //             NOTE: Any write value clears the pending bit
        meigwclrs[vec]  = 0; __asm__ volatile ("fence");

        // MEIE_S - Enable implemented interrupt sources
        meies[vec]  = (vec < CSS_MCU0_VEER_INTR_EXT_LSB); __asm__ volatile ("fence");
    }

    /* -- Re-enable global interrupts -- */

    // Enable Interrupts for each component
    // MCI
    mci_reg[MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R /sizeof(uint32_t)] = MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_INTERNAL_EN_MASK                   |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_MASK              |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_MASK              |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK         |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK;
    mci_reg[MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R /sizeof(uint32_t)] = MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL31_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL30_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL29_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL28_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL27_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL26_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL25_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL24_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL23_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL22_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL21_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL20_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL19_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL18_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL17_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL16_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL15_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL14_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL13_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL12_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL11_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL10_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL9_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL8_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL7_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL6_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL5_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL4_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL3_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL2_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL1_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R_ERROR_AGG_ERROR_FATAL0_EN_MASK;
    mci_reg[MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R /sizeof(uint32_t)] = MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK     |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MCU_RESET_REQ_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK        |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_TARGET_DONE_EN_MASK    |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_TARGET_DONE_EN_MASK    |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_MASK      |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_MASK      |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_MASK        |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_MASK        |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK         |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK            |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_MASK   |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_MASK   |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_OTP_OPERATION_DONE_EN_MASK;
    mci_reg[MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R /sizeof(uint32_t)] = MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL31_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL30_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL29_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL28_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL27_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL26_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL25_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL24_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL23_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL22_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL21_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL20_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL19_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL18_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL17_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL16_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL15_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL14_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL13_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL12_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL11_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL10_EN_MASK |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL9_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL8_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL7_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL6_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL5_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL4_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL3_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL2_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL1_EN_MASK  |
                                                                        MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_NOTIF_AGG_ERROR_NON_FATAL0_EN_MASK;
    mci_reg[MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R/sizeof(uint32_t)] = MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK |
                                                                       MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;

    // I3C
    i3c_reg[I3CCSR_I3CBASE_INTR_STATUS_ENABLE /sizeof(uint32_t)] = I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_INTERNAL_ERR_STAT_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_SEQ_CANCEL_STAT_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_WARN_CMD_SEQ_STALL_STAT_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_STATUS_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_STAT_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_STATUS_ENABLE_SCHED_CMD_MISSED_TICK_STAT_EN_MASK;
    i3c_reg[I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE /sizeof(uint32_t)] = I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_INTERNAL_ERR_SIGNAL_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_SEQ_CANCEL_SIGNAL_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_WARN_CMD_SEQ_STALL_SIGNAL_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_HC_ERR_CMD_SEQ_TIMEOUT_SIGNAL_EN_MASK |
                                                                   I3CCSR_I3CBASE_INTR_SIGNAL_ENABLE_SCHED_CMD_MISSED_TICK_SIGNAL_EN_MASK;
    i3c_reg[I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE /sizeof(uint32_t)] = I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TX_THLD_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RX_THLD_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_IBI_STATUS_THLD_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_CMD_QUEUE_READY_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_RESP_READY_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ABORT_STAT_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_STATUS_ENABLE_TRANSFER_ERR_STAT_EN_MASK;
    i3c_reg[I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE /sizeof(uint32_t)] = I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TX_THLD_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RX_THLD_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_IBI_STATUS_THLD_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_CMD_QUEUE_READY_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_RESP_READY_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ABORT_SIGNAL_EN_MASK |
                                                                          I3CCSR_PIOCONTROL_PIO_INTR_SIGNAL_ENABLE_TRANSFER_ERR_SIGNAL_EN_MASK;
    i3c_reg[I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE /sizeof(uint32_t)] = I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_REMAIN_SIGNAL_EN_MASK |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_OK_PRIMED_SIGNAL_EN_MASK |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_FAIL_SIGNAL_EN_MASK  |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_ACR_HANDOFF_ERR_M3_SIGNAL_EN_MASK    |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CRR_RESPONSE_SIGNAL_EN_MASK          |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_DYN_ADDR_SIGNAL_EN_MASK      |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_NACKED_SIGNAL_EN_MASK |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_OK_SIGNAL_EN_MASK     |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_ACCEPT_ERR_SIGNAL_EN_MASK    |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_STBY_CR_OP_RSTACT_SIGNAL_EN_MASK     |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_PARAM_MODIFIED_SIGNAL_EN_MASK    |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_UNHANDLED_NACK_SIGNAL_EN_MASK    |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_FATAL_RSTDAA_ERR_SIGNAL_EN_LOW   |
                                                                                        I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_INTR_SIGNAL_ENABLE_CCC_FATAL_RSTDAA_ERR_SIGNAL_EN_MASK;
    i3c_reg[I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE /sizeof(uint32_t)] = I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_TIMEOUT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_TIMEOUT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DATA_THLD_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DATA_THLD_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TX_DESC_THLD_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_RX_DESC_THLD_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_THLD_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_IBI_DONE_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ABORT_STAT_EN_MASK |
                                                                    I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE_TRANSFER_ERR_STAT_EN_MASK;

    // Set mtimecmp to max value to avoid spurious timer interrupts
    *mtimecmp_l = 0xFFFFFFFF;
    *mtimecmp_h = 0xFFFFFFFF;

    // Set threshold for Correctable Error Local Interrupts
    value = 0xd0000000;
    __asm__ volatile ("csrw    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MICECT),   "r" (value) /* input : immediate, register */
                      : /* clobbers: none */);
    __asm__ volatile ("csrw    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MICCMECT), "r" (value) /* input : immediate, register */
                      : /* clobbers: none */);
    __asm__ volatile ("csrw    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MDCCMECT), "r" (value) /* input : immediate, register */
                      : /* clobbers: none */);

    // MIE
    // Enable MIE.MEI (External Interrupts)
    // Enable MIE.MTI (Timer Interrupts)
    // Enable MIE.MCEI (Correctable Error Interrupt)
    // Do not enable SW Interrupts
    csr_set_bits_mie(MIE_MEI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MCEI_BIT_MASK);

    // Global interrupt enable
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

}

void std_rv_nop_machine(void)  {
    // Nop machine mode interrupt.
    VPRINTF(HIGH,"mcause:%x\n", csr_read_mcause());
    return;
}

void std_rv_mtvec_mti(void) {
    volatile uint32_t * const mtimecmp_l     = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L;
    volatile uint32_t * const mtimecmp_h     = (uint32_t*) SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H;

    // Set mtimecmp to max value to avoid further timer interrupts
    *mtimecmp_l = 0xFFFFFFFF;
    *mtimecmp_h = 0xFFFFFFFF;

    VPRINTF(MEDIUM, "Done handling machine-mode TIMER interrupt\n");
}

void nonstd_veer_mtvec_miti0(void) {
    uint_xlen_t value;
    //Disable internal timer 0 count en to service intr
    __asm__ volatile ("csrwi %0, %1" \
                      : /* output : none */ \
                      : "i" (VEER_CSR_MITCTL0), "i" (0x00) /* input : immediate */ \
                      : /* clobbers : none */);

}

void nonstd_veer_mtvec_mcei(void) {
    uint32_t mask = 0x07FFFFFF;
    VPRINTF(HIGH,"Cor Error Local ISR\n");
    __asm__ volatile ("csrc    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MICECT),   "r" (mask) /* input : immediate, register */
                      : /* clobbers: none */);
    __asm__ volatile ("csrc    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MICCMECT), "r" (mask) /* input : immediate, register */
                      : /* clobbers: none */);
    __asm__ volatile ("csrc    %0, %1"
                      : /* output: none */
                      : "i" (VEER_CSR_MDCCMECT), "r" (mask) /* input : immediate, register */
                      : /* clobbers: none */);
}

static void std_rv_isr(void) {
    void (* isr) (void); // Function pointer to source-specific ISR
    SEND_STDOUT_CTRL(TB_CMD_INCR_INTR_ACTIVE);
    uint_xlen_t this_cause = csr_read_mcause();
    VPRINTF(LOW,"In:Std ISR\nmcause:%x\n", this_cause);
    if (this_cause &  MCAUSE_INTERRUPT_BIT_MASK) {
        this_cause &= 0xFF;
        // Known exceptions
        switch (this_cause) {
        case RISCV_INT_MASK_MTI :
            // Timer exception, keep up the one second tick.
            //mtimer_set_raw_time_cmp(MTIMER_SECONDS_TO_CLOCKS(1));
            //timestamp = mtimer_get_raw_time();
            break;
        case RISCV_INT_MASK_MEI :
            // Read MIP register - should have MEIP set
            // Read MEIPX register - should != 0
            //uint32_t * const meipx      = (uint32_t*) VEER_MM_PIC_MEIPX;      // FIXME
            // External Interrupt, branch to the VeeR handler
            // (TODO) in a loop until all interrupts at current priority level
            // are handled (aka Interrupt Chaining is supported)
            //   * NOTE: incompatible with Fast Redirect
            do {
                // Capture the priority and ID
                __asm__ volatile ("csrwi    %0, 0" \
                                  : /* output: none */        \
                                  : "i" (VEER_CSR_MEICPCT) /* input : immediate */ \
                                  : /* clobbers: none */);
                // Look up the handler address in MEIHAP
                __asm__ volatile ("csrr    %0, %1"
                                  : "=r" (isr)  /* output : register */
                                  : "i" (VEER_CSR_MEIHAP) /* input : immediate */
                                  : /* clobbers: none */);
                // Call the ID-specific handler
                isr(); // ISR here is a function pointer indexed into the meivt table
                    // For Interrupt NESTING support, the handler should:
                    //  * Save meicurpl
                    //  * Read meicidpl
                    //  * Set current Priority in meicurpl
                    //  * enable mstatus.mei
                    //  * Restore meicurpl prev. value
                    //  * disable mstatus.mei
                // Re-read MIP.MEIP
                // Check MIE.MEIE
                // Re-read MEIPX
                // Check MEIES
            } while (0); // FIXME
            break;
        }
    } else {
        switch (this_cause) {
        case RISCV_EXCP_LOAD_ACCESS_FAULT :
            // mscause
            __asm__ volatile ("csrr    %0, %1"
                              : "=r" (this_cause)  /* output : register */
                              : "i" (VEER_CSR_MSCAUSE) /* input : immediate */
                              : /* clobbers: none */);
            VPRINTF(LOW,"mscause:%x\n",this_cause);
            // mepc
            this_cause = csr_read_mepc();
            VPRINTF(LOW,"mepc:%x\n",this_cause);
            // mtval
            this_cause = csr_read_mtval();
            VPRINTF(LOW,"mtval:%x\n",this_cause);
            break;
        }
    }
    SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);
    return;
}

// This vector table (should be) only indexed into when MTVEC.MODE = Vectored
// based on the value of mcause when the trap occurs
// For MTVEC.MODE = Direct, trap events always route straight to the base value
// of MTVEC, which should be pointing at the std_rv_isr() routine above.
static void std_rv_isr_vector_table(void) {
    // see https://five-embeddev.com/baremetal/vectored_interrupts/ for example
    __asm__ volatile (
        ".org  std_rv_isr_vector_table + 0*4;"
        "jal   zero,std_rv_mtvec_exception;"  /* 0  */
        ".org  std_rv_isr_vector_table + 1*4;"
        "jal   zero,std_rv_mtvec_ssi;"  /* 1  */
        ".org  std_rv_isr_vector_table + 3*4;"
        "jal   zero,std_rv_mtvec_msi;"  /* 3  */
        ".org  std_rv_isr_vector_table + 5*4;"
        "jal   zero,std_rv_mtvec_sti;"  /* 5  */
        ".org  std_rv_isr_vector_table + 7*4;"
        "jal   zero,std_rv_mtvec_mti;"  /* 7  */
        ".org  std_rv_isr_vector_table + 9*4;"
        "jal   zero,std_rv_mtvec_sei;"  /* 9  */
        ".org  std_rv_isr_vector_table + 11*4;"
        "jal   zero,std_rv_mtvec_mei;"  /* 11 */
        ".org  std_rv_isr_vector_table + 29*4;"
        "jal   zero,nonstd_veer_mtvec_miti0;" /* 29 */
        ".org  std_rv_isr_vector_table + 30*4;"
        "jal   zero,nonstd_veer_mtvec_mcei;" /* 30 */
//        #ifndef VECTOR_TABLE_MTVEC_PLATFORM_INTS
//        ".org  std_rv_isr_vector_table + 16*4;"
//        "jal   std_rv_mtvec_platform_irq0;"
//        "jal   std_rv_mtvec_platform_irq1;"
//        "jal   std_rv_mtvec_platform_irq2;"
//        "jal   std_rv_mtvec_platform_irq3;"
//        "jal   std_rv_mtvec_platform_irq4;"
//        "jal   std_rv_mtvec_platform_irq5;"
//        "jal   std_rv_mtvec_platform_irq6;"
//        "jal   std_rv_mtvec_platform_irq7;"
//        "jal   std_rv_mtvec_platform_irq8;"
//        "jal   std_rv_mtvec_platform_irq9;"
//        "jal   std_rv_mtvec_platform_irq10;"
//        "jal   std_rv_mtvec_platform_irq11;"
//        "jal   std_rv_mtvec_platform_irq12;"
//        "jal   std_rv_mtvec_platform_irq13;"
//        "jal   std_rv_mtvec_platform_irq14;"
//        "jal   std_rv_mtvec_platform_irq15;"
//        #endif
        : /* output: none */
        : /* input : immediate */
        : /* clobbers: none */
    );
}

// Exception handler for Standard RISC-V Vectored operation
void std_rv_mtvec_exception(void) {
    SEND_STDOUT_CTRL( TB_CMD_INCR_INTR_ACTIVE);
    uint_xlen_t this_cause = csr_read_mcause();
    VPRINTF(WARNING,"In:Std Excptn\nmcause:%x\n", this_cause);
    if (this_cause &  MCAUSE_INTERRUPT_BIT_MASK) {
        VPRINTF(ERROR,"Unexpected Intr bit:%x\n", 0xFFFFFFFF);
        SEND_STDOUT_CTRL(0x1); // KILL THE SIMULATION with "ERROR"
    } else {
        uint_xlen_t tmp_reg;

        // mscause
        __asm__ volatile ("csrr    %0, %1"
                          : "=r" (tmp_reg)  /* output : register */
                          : "i" (VEER_CSR_MSCAUSE) /* input : immediate */
                          : /* clobbers: none */);
        VPRINTF(LOW,"mscause:%x\n",tmp_reg);
        #ifdef RV_EXCEPTION_STRUCT
        SEND_STDOUT_CTRL(0xe4); // Disable ECC Error injection, if enabled, to allow exc_flag writes (which may be in DCCM) without corruption
        __asm__ volatile ("fence.i");
        exc_flag.exception_hit = 1;
        exc_flag.mcause = this_cause;
        exc_flag.mscause = tmp_reg;
        #endif
        // mepc
        tmp_reg = csr_read_mepc();
        VPRINTF(LOW,"mepc:%x\n",tmp_reg);
        // mtval
        tmp_reg = csr_read_mtval();
        VPRINTF(LOW,"mtval:%x\n",tmp_reg);

        switch (this_cause) {
        case RISCV_EXCP_LOAD_ACCESS_FAULT :
            #ifdef RV_EXCEPTION_STRUCT
            if (exc_flag.mscause == RISC_EXCP_MSCAUSE_DCCM_LOAD_UNC_ECC_ERR) {
                // Increment mepc before returning, because repeating the previously
                // failing command will cause an infinite loop back to this ISR.
                tmp_reg = csr_read_mepc();
                csr_write_mepc(tmp_reg + 4); // FIXME this has no guarantee of working. E.g. Compressed instructions are 2, not 4, bytes...

                // Bail immediately instead of killing the sim.
                // Caliptra RESET is expected due to FATAL Error, but if it's
                // masked the originating test should decide what to do.
                SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);
                return;
            }
            #endif
            break;
        case RISCV_EXCP_STORE_AMO_ACCESS_FAULT :
            #ifdef RV_EXCEPTION_STRUCT
            if (exc_flag.mscause == RISC_EXCP_MSCAUSE_DCCM_STOR_UNC_ECC_ERR) {
                // Bail immediately instead of killing the sim.
                // Caliptra RESET is expected due to FATAL Error, but if it's
                // masked the originating test should decide what to do.
                SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);
                return;
            }
            #endif
            break;
        case RISCV_EXCP_INSTRUCTION_ACCESS_FAULT :
            #ifdef RV_EXCEPTION_STRUCT
            if (exc_flag.mscause == RISC_EXCP_MSCAUSE_ICCM_INST_UNC_ECC_ERR) {
                SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);

                // Reset uC instead of killing the sim.
                // Caliptra RESET is expected due to FATAL Error, but if it's
                // masked the originating test won't be able to make progress
                // after this routine returns.

                // If the FATAL Error bit for ICCM ECC Error is masked, manually trigger firmware reset
                if (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK) & SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK) {
                    VPRINTF(LOW, "ICCM ECC FATAL_ERROR bit is masked, no reset expected from TB: resetting the core manually!\n");
                    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET, SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
                // Otherwise, wait for core reset
                } else {
                    VPRINTF(LOW, "ICCM ECC FATAL_ERROR bit is not masked, waiting for reset from TB!\n");
                    while(1);
                }

            }
            #endif
            break;
        case RISCV_EXCP_ILLEGAL_INSTRUCTION :
            break;
        default :
            break;
        }
    }
    SEND_STDOUT_CTRL(0x1 ); // KILL THE SIMULATION with "ERROR"
    SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);
    return;
}

// Non-Standard Vectored Interrupt Handler (vector 0)
// ISR 0 is, by definition, not implemented and simply returns
static void nonstd_veer_isr_0 (void) {
    SEND_STDOUT_CTRL(TB_CMD_INCR_INTR_ACTIVE);
    VPRINTF(MEDIUM, "In:0\n");
    SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);
    return;
}

// Macro used to lay down mostly equivalent ISR for each of the supported
// interrupt sources.
// The only unique functionality for each ISR is provided by the service_xxx_intr
// inline function.
// Using inline functions for event-specific handling reduces the overhead from
// context switches (which is critical in an ISR) relative to regular function
// calls
#define stringify(text) #text
#define nonstd_veer_isr(name) static void nonstd_veer_isr_##name (void) {                           \
    SEND_STDOUT_CTRL(TB_CMD_INCR_INTR_ACTIVE);                                                        \
                                                                                                      \
    /* Print msg before enabling nested interrupts so it                                              \
     * completes printing and is legible                                                              \
     */                                                                                               \
    VPRINTF(MEDIUM, "In:"stringify(name)"\n");                                                        \
                                                                                                      \
    /* Save Context to Stack */                                                                       \
    uint32_t meicidpl;                                                                                \
    uint32_t prev_meicurpl;                                                                           \
    uint_xlen_t prev_mepc;                                                                            \
    uint_xlen_t prev_mstatus;                                                                         \
    uint_xlen_t prev_mie;                                                                             \
    __asm__ volatile ("csrr    %0, %1"                                                                \
                      : "=r" (meicidpl)  /* output : register */                                      \
                      : "i" (VEER_CSR_MEICIDPL) /* input : immediate */                              \
                      : /* clobbers: none */);                                                        \
    __asm__ volatile ("csrr    %0, %1"                                                                \
                      : "=r" (prev_meicurpl)  /* output : register */                                 \
                      : "i" (VEER_CSR_MEICURPL) /* input : immediate */                              \
                      : /* clobbers: none */);                                                        \
    prev_mepc    = csr_read_mepc();                                                                   \
    prev_mstatus = csr_read_mstatus();                                                                \
    prev_mie     = csr_read_mie();                                                                    \
                                                                                                      \
    /* Set the priority threshold to current priority */                                              \
    __asm__ volatile ("csrw    %0, %1"                                                                \
                      : /* output: none */                                                            \
                      : "i" (VEER_CSR_MEICURPL), "r" (meicidpl)  /* input : immediate  */             \
                      : /* clobbers: none */);                                                        \
                                                                                                      \
    /* Reenable interrupts (nesting) */                                                               \
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);                                                       \
                                                                                                      \
    /* Service the interrupt (clear the interrupt source) */                                          \
    intr_count++;                                                                                     \
    VPRINTF(MEDIUM,"cnt_"stringify(name)":%x\n",intr_count);                                          \
    /* Fill in with macro contents, e.g. "service_mci_intr" */                                        \
    /* This will match one macro from this list:                                                      \
     * service_mci_intr                                                                               \
     * service_i3c_intr                                                                               \
     */                                                                                               \
    service_##name##_intr();                                                                          \
                                                                                                      \
    /* Disable interrupts */                                                                          \
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);                                                       \
                                                                                                      \
    /* Restore Context from Stack */                                                                  \
    __asm__ volatile ("csrw    %0, %1"                                                                \
                      : /* output: none */                                                            \
                      : "i" (VEER_CSR_MEICURPL), "r" (prev_meicurpl)  /* input : immediate  */        \
                      : /* clobbers: none */);                                                        \
    csr_write_mepc(prev_mepc);                                                                        \
    csr_set_bits_mstatus(prev_mstatus & (MSTATUS_MPIE_BIT_MASK | MSTATUS_MPP_BIT_MASK));              \
    csr_set_bits_mie(prev_mie & (MIE_MSI_BIT_MASK | MIE_MTI_BIT_MASK | MIE_MEI_BIT_MASK));            \
                                                                                                      \
    /* Done */                                                                                        \
    SEND_STDOUT_CTRL(TB_CMD_DECR_INTR_ACTIVE);                                                        \
    return;                                                                                           \
}

////////////////////////////////////////////////////////////////////////////////
// Auto define ISR for each interrupt source using a macro
// Resulting defined functions are, e.g. "nonstd_veer_isr_mci" (for Vector 1)

// Non-Standard Vectored Interrupt Handler (MCI Interrupt = Vector 1)
nonstd_veer_isr(mci)
// Non-Standard Vectored Interrupt Handler (I3C Interrupt = vector 2)
nonstd_veer_isr(i3c)
