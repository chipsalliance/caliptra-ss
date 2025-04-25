# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#include "soc_address_map.h"
#define STDOUT SOC_MCI_TOP_MCI_REG_DEBUG_OUT

.set    mfdc, 0x7f9
.set    mrac, 0x7c0
.set    mcause, 0x342
.set    mscause, 0x7ff
.set    mepc, 0x341
.set    mtval, 0x343
.section .text.init
.align 4
.global _start
_start:

        la x1, _trap
        csrw mtvec, x1

        // MRAC
        // Disable Caches on all regions except...
        //  - Set cacheable for ROM to improve perf
        // Set side-effects (SE) at peripheral address regions:
        //  - [UNMAPPED] @ 0x0000_0000:    SE
        //  - [UNMAPPED] @ 0x1000_0000:    SE
        //  - MCI/I3C    @ 0x2000_0000:    SE
        //  - [UNMAPPED] @ 0x3000_0000:    SE
        //  - [UNMAPPED] @ 0x4000_0000:    SE
        //  - DCCM       @ 0x5000_0000: no SE
        //  - PIC        @ 0x6000_0000:    SE
        //  - FC/LCC     @ 0x7000_0000:    SE
        //  - imem       @ 0x8000_0000: no SE, +Cache
        //  - [UNMAPPED] @ 0x9000_0000:    SE
        //  - soc_ifc    @ 0xA000_0000:    SE
        //  - ...
        //  - [UNMAPPED] @ 0xC000_0000:    SE
        //  - [UNMAPPED] @ 0xD000_0000:    SE
        //  - [UNMAPPED] @ 0xE000_0000:    SE
        //  - [UNMAPPED] @ 0xF000_0000:    SE
        li t0, 0xAAA9A2AA
        csrw mrac, t0

        la sp, STACK

        call main

        # Map exit code of main() to command to be written to STDOUT
        snez a0, a0
        bnez a0, _finish
        li   a0, 0xFF

.global _finish
_finish:
        li t0, STDOUT
        sb a0, 0(t0)
        beq x0, x0, _finish
        .rept 10
        nop
        .endr

.macro putnibble 
    srli t1, a0, 28
    andi t2, t1, 0xf
    addi t3, t2, 0x30
    sb t3, 0(t0)
    slli a0, a0, 4
.endm
.align 4
_trap:
    la t0, STDOUT
    // sep '.'
    li a0, 0x2e
    sb a0, 0(t0)
    // mcause
    csrr a0, mcause
    fence.i
.rept 8
    putnibble
.endr
    // sep '.'
    li a0, 0x2e
    sb a0, 0(t0)
    // mscause
    csrr a0, mscause
    fence.i
.rept 8
    putnibble
.endr
    // sep '.'
    li a0, 0x2e
    sb a0, 0(t0)
    // mepc
    csrr a0, mepc
    fence.i
.rept 8
    putnibble
.endr
    // sep '.'
    li a0, 0x2e
    sb a0, 0(t0)
    // mtval
    csrr a0, mtval
    fence.i
.rept 8
    putnibble
.endr
    // Failure
    li a0, 1 # failure
    j _finish
