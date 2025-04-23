/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef VEER_CSR_H
#define VEER_CSR_H

// #include "caliptra_defines.h"
#include "riscv-csr.h" /* for __riscv_xlen */

//////////////////////////////////////////////////////////////////////////////
// Non-Standard VeeR CSR offset macros
//
#define VEER_CSR_MPMC     0x7C6
#define VEER_CSR_MICECT   0x7F0
#define VEER_CSR_MICCMECT 0x7F1
#define VEER_CSR_MDCCMECT 0x7F2
#define VEER_CSR_MSCAUSE  0x7FF
#define VEER_CSR_MDEAU    0xBC0
#define VEER_CSR_MEIVT    0xBC8
#define VEER_CSR_MEIPT    0xBC9
#define VEER_CSR_MEICPCT  0xBCA
#define VEER_CSR_MEICIDPL 0xBCB
#define VEER_CSR_MEICURPL 0xBCC
#define VEER_CSR_MEIHAP   0xFC8


//////////////////////////////////////////////////////////////////////////////
// VeeR MSCAUSE encoding
//
// From Table 2-10, VeeR EL2 PRM, Rev 1.4
enum {
    RISC_EXCP_MSCAUSE_ICCM_INST_UNC_ECC_ERR = 0x1,
    RISC_EXCP_MSCAUSE_DCCM_LOAD_UNC_ECC_ERR = 0x1,
    RISC_EXCP_MSCAUSE_DCCM_STOR_UNC_ECC_ERR = 0x1,
};


//////////////////////////////////////////////////////////////////////////////
// VeeR PIC Memory Mapped register offset macros
//
// Per the VeeR PRM:
//   Suffix 'S' indicates a discrete register for each unique interrupt source
//              i.e. 64 interrupts = 64 registers
//   Suffix 'X' indicates a single bit within a range of registers for each interrupt source
//              i.e. 64 interrupts = 2 registers (32-bits each)
#define VEER_MM_PIC_MEIPLS       (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIPL_OFFSET)
#define VEER_MM_PIC_MEIPL(S)     (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIPL_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MEIPX        (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIP_OFFSET)
#define VEER_MM_PIC_MEIP(X)      (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIP_OFFSET + (X>>5)*4) /* X is 1:255 */
#define VEER_MM_PIC_MEIES        (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIE_OFFSET)
#define VEER_MM_PIC_MEIE(S)      (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIE_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MPICCFG      (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MPICCFG_OFFSET)
#define VEER_MM_PIC_MEIGWCTRLS   (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIGWCTRL_OFFSET)
#define VEER_MM_PIC_MEIGWCTRL(S) (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIGWCTRL_OFFSET + S*4) /* S is 1:255 */
#define VEER_MM_PIC_MEIGWCLRS    (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIGWCLR_OFFSET)
#define VEER_MM_PIC_MEIGWCLR(S)  (MCU_RV_PIC_BASE_ADDR + MCU_RV_PIC_MEIGWCLR_OFFSET + S*4) /* S is 1:255 */


//////////////////////////////////////////////////////////////////////////////
// VeeR PIC Gateway Configuration bits
//
enum {
  VEER_MEIGWCTRL_ACTIVE_HI_LEVEL = 0x00000000,
  VEER_MEIGWCTRL_ACTIVE_LO_LEVEL = 0x00000001,
  VEER_MEIGWCTRL_ACTIVE_HI_EDGE  = 0x00000002,
  VEER_MEIGWCTRL_ACTIVE_LO_EDGE  = 0x00000003,
};


//////////////////////////////////////////////////////////////////////////////
// VeeR Core-Specific MCAUSE values
//
#define MCAUSE_NMI_BIT_MASK                     (0xFUL << ((__riscv_xlen-4)))
#define MCAUSE_NMI_CODE_DBUS_STORE_VALUE        (MCAUSE_NMI_BIT_MASK | 0x0000)
#define MCAUSE_NMI_CODE_DBUS_LOAD_VALUE         (MCAUSE_NMI_BIT_MASK | 0x0001)
#define MCAUSE_NMI_CODE_FAST_INT_ECC_VALUE      (MCAUSE_NMI_BIT_MASK | 0x1000)
#define MCAUSE_NMI_CODE_FAST_INT_DCCM_VALUE     (MCAUSE_NMI_BIT_MASK | 0x1001)
#define MCAUSE_NMI_CODE_FAST_INT_NONDCCM_VALUE  (MCAUSE_NMI_BIT_MASK | 0x1002)

/*******************************************
 * mpmc - MRW - Power Management Control Register
 */
static inline void csr_write_mpmc(uint_xlen_t value) {
    __asm__ volatile ("csrw    %0, %1" \
                : /* output: none */        \
                : "i" (VEER_CSR_MPMC), "r" (value)  /* input : immediate  */ \
                : /* clobbers: none */);
}
static inline void csr_write_mpmc_halt() {
    //Halt the core
    __asm__ volatile ("csrwi    %0, %1" \
                : /* output: none */        \
                : "i" (VEER_CSR_MPMC), "i" (0x03)  /* input : immediate  */ \
                : /* clobbers: none */);
}


/*******************************************
 * mdeau - MRW - Data base register.
 */
static inline uint_xlen_t csr_read_mdeau(void) {
    uint_xlen_t value;
    __asm__ volatile ("csrr    %0, VEER_CSR_MDEAU"
                      : "=r" (value)  /* output : register */
                      : /* input : none */
                      : /* clobbers: none */);
    return value;
}
static inline void csr_write_mdeau(uint_xlen_t value) {
    __asm__ volatile ("csrw    VEER_CSR_MDEAU, %0"
                      : /* output: none */
                      : "r" (value) /* input : from register */
                      : /* clobbers: none */);
}
static inline uint_xlen_t csr_read_write_mdeau(uint_xlen_t new_value) {
    uint_xlen_t prev_value;
    __asm__ volatile ("csrrw    %0, VEER_CSR_MDEAU, %1"
                      : "=r" (prev_value) /* output: register %0 */
                      : "r" (new_value)  /* input : register */
                      : /* clobbers: none */);
    return prev_value;
}


//////////////////////////////////////////////////////////////////////////////
// VeeR Core-Specific MIE/MIP values
//
#define MIE_MCEI_BIT_OFFSET   30
#define MIE_MCEI_BIT_WIDTH    1
#define MIE_MCEI_BIT_MASK     0x40000000
#define MIP_MCEI_BIT_OFFSET   30
#define MIP_MCEI_BIT_WIDTH    1
#define MIP_MCEI_BIT_MASK     0x40000000


#endif // #define VEER_CSR_H
