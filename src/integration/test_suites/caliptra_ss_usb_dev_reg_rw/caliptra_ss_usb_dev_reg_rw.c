//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
// Description: USB device-controller register read/write test for the
//  Caliptra Subsystem, exercising BOTH embedded device controllers (USBDC0 and
//  USBDC1) in a single run.
//
//  Both register banks are directly reachable from the MCU LSU AXI master with
//  no RTL change:
//    USBDC0 registers at USB_DEV0_REG_BASE_ADDR (0x2000_1000)
//    USBDC1 registers at USB_DEV1_REG_BASE_ADDR (0x2001_0000)
//  This test therefore uses the ABSOLUTE USB_DEV0_*/USB_DEV1_* macros directly
//  (not the compile-time USB_DEV_SEL selection) and walks a single shared
//  register-disposition table over both banks.
//
//  Methodology (per bit-FIELD, not per register):
//    Each register is described as a table of individual bit-fields, each with
//    an access class. This makes every failure name the EXACT field and bit
//    range, e.g. "DEV0 DEVCMDSTAT.PLL_ON [bit 9] RW mismatch: wrote 0x1 got 0x0",
//    so a mismatch is directly actionable without decoding an aggregate mask.
//    ACC_RW   Write a masked-random value confined to the field, read back,
//             and require only that field to equal what was written.
//    ACC_RO   Prove immutability: perform three DIFFERENT writes (0x00000000,
//             0xA5A5A5A5, 0x5A5A5A5A) reading after each, and require the field
//             bits to be identical across all three (the field ignored writes).
//             Reserved fields (chk_zero) must ADDITIONALLY read back 0; a
//             reserved bit that is writable or non-zero is flagged as a
//             candidate RTL bug and is NOT waived.
//    ACC_W1C  Write-1-to-clear / self-clearing bits (SETUP, *_C): listed in the
//             field tables for documentation but excluded from RW/RO compares.
//    The field tables tile all 32 bits of each register so no bit escapes a
//    check. Whole registers excluded: EPLISTSTART/DATABUFSTART (DMA pointers),
//    EPSKIP (self-clearing), INTSTAT/INTSETSTAT (W1C/W1S), and 0x3C-0x3F.
//
//  Two mandatory RTL hazards are honored by construction (see
//  claude_md/09_usb_hub_composite_migration.md and docs/usb_register_structure.md):
//    1. Write-before-read: reading a register that was never written since
//       reset drives X and fires the fatal DataKnown_A assertion on the
//       dev*_axi read response path. Every included register (RW and RO) is
//       written before it is read, so this never happens.
//    2. Address aliasing: the device register file decodes only haddr[5:2] (a
//       16-register / 4-bit window), so any offset >= 0x40 aliases back into
//       0x00-0x3C. The table contains no offset >= 0x40.
//
//  This is a STANDALONE register test: it only boots the MCU. It does not bring
//  up the USB core, does not connect the hub, and drives no USB traffic, so it
//  can freely randomize configuration registers on both controllers without
//  disturbing a live link or the DMA engine. The companion UVM sequence
//  (caliptra_ss_usb_dev_reg_rw_sequence) simply holds the run phase open long
//  enough for this firmware to finish and report its verdict.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// ---------------------------------------------------------------------------
// Field-level register model.
//
// Instead of one aggregate rw_mask/ro_mask per register, each register is
// described as a table of individual bit-fields. Every field carries its bit
// position, width, access class, and name, so a failure names the EXACT field
// (and bit range) that misbehaved, e.g.
//   ERROR: DEV0 DEVCMDSTAT.PLL_ON [bit 9] RW mismatch: wrote 0x1 got 0x0
// rather than a raw mask the reader has to decode by hand.
//
// The field tables tile all 32 bits of each register (named functional fields
// plus explicit reserved fields) so no bit escapes classification.
// ---------------------------------------------------------------------------

// Access class of one bit-field.
typedef enum {
    ACC_RW  = 0, // read/write: write a masked-random value, read back, compare
    ACC_RO  = 1, // read-only: must be immutable across the 3 write patterns
    ACC_W1C = 2  // write-1-to-clear / self-clearing: not a plain RW/RO check
} usb_acc_t;

// One bit-field of a register.
typedef struct {
    uint8_t     lsb;      // field least-significant bit
    uint8_t     width;    // field width in bits
    usb_acc_t   access;   // access class
    uint8_t     chk_zero; // 1: (reserved) field must ALSO read back 0
    const char *field;    // field name for logging
} usb_field_t;

// One register: offset, name, and its field table.
typedef struct {
    uint32_t           offset;  // byte offset from the bank base
    const char        *name;    // register name for logging
    const usb_field_t *fields;  // field table
    uint32_t           nfields; // number of fields
} usb_reg_desc_t;

// ---------------------------------------------------------------------------
// DEVCMDSTAT (0x00). SETUP[8] and the *_C change bits are W1C (writing 1 clears
// them), so they are classified ACC_W1C and excluded from the plain RW compare.
// DEV_ADDR, DEV_EN, PLL_ON, LPM_SUP, the four IntOnNAK bits, DCON, DSUS and
// LPM_SUS are all RW per spec Chapter 5 and are exercised as ACC_RW: this is a
// standalone register test with the controllers quiescent (no live link or
// DMA), so driving these bits is safe. LPM_REWP[20] and VbusDebounced[28] are
// defined RO (may be non-zero). Reserved bits (10, 18, 23:21, 27, 31:29) are
// ACC_RO + chk_zero: they must be immutable AND read back 0; a violation is a
// candidate RTL bug.
// ---------------------------------------------------------------------------
static const usb_field_t devcmdstat_fields[] = {
    { 0,  7, ACC_RW,  0, "DEV_ADDR"      }, // RW per spec Chapter 5
    { 7,  1, ACC_RW,  0, "DEV_EN"        }, // RW per spec Chapter 5
    { 8,  1, ACC_W1C, 0, "SETUP"         }, // W1C, not plain RW
    { 9,  1, ACC_RW,  0, "PLL_ON"        },
    { 10, 1, ACC_RO,  1, "RSVD10"        },
    { 11, 1, ACC_RW,  0, "LPM_SUP"       },
    { 12, 1, ACC_RW,  0, "IntOnNAK_AO"   },
    { 13, 1, ACC_RW,  0, "IntOnNAK_AI"   },
    { 14, 1, ACC_RW,  0, "IntOnNAK_CO"   },
    { 15, 1, ACC_RW,  0, "IntOnNAK_CI"   },
    { 16, 1, ACC_RW,  0, "DCON"          }, // RW per spec Chapter 5
    { 17, 1, ACC_RW,  0, "DSUS"          }, // RW per spec Chapter 5
    { 18, 1, ACC_RO,  1, "RSVD18"        },
    { 19, 1, ACC_RW,  0, "LPM_SUS"       }, // RW per spec Chapter 5
    { 20, 1, ACC_RO,  0, "LPM_REWP"      }, // defined RO (may be non-zero)
    { 21, 3, ACC_RO,  1, "RSVD23_21"     },
    { 24, 1, ACC_W1C, 0, "DCON_C"        }, // W1C, not plain RW
    { 25, 1, ACC_W1C, 0, "DSUS_C"        }, // W1C, not plain RW
    { 26, 1, ACC_W1C, 0, "DRES_C"        }, // W1C, not plain RW
    { 27, 1, ACC_RO,  1, "RSVD27"        },
    { 28, 1, ACC_RO,  0, "VbusDebounced" }, // defined RO (may be non-zero)
    { 29, 3, ACC_RO,  1, "RSVD31_29"     },
};

// INFO (0x04): FRAME_NR[10:0] RO, ERR_CODE[14:11] RW per spec, bit15 reserved,
// CHIP_ID[31:16] RO (a non-zero HW constant, so NO read-0 check).
static const usb_field_t info_fields[] = {
    { 0,  11, ACC_RO, 0, "FRAME_NR" },
    { 11,  4, ACC_RW, 0, "ERR_CODE" },
    { 15,  1, ACC_RO, 1, "RSVD15"   },
    { 16, 16, ACC_RO, 0, "CHIP_ID"  }, // defined RO constant, may be non-zero
};

// LPM (0x10): HIRD_HW[3:0] RO, HIRD_SW[7:4] RW, DataPending[8] RW, [31:9] rsvd.
static const usb_field_t lpm_fields[] = {
    { 0,  4, ACC_RO, 0, "HIRD_HW"     },
    { 4,  4, ACC_RW, 0, "HIRD_SW"     },
    { 8,  1, ACC_RW, 0, "DataPending" },
    { 9, 23, ACC_RO, 1, "RSVD31_9"    },
};

// EPINUSE (0x18): [1:0] reserved, BUF[29:2] RW, [31:30] reserved.
static const usb_field_t epinuse_fields[] = {
    { 0,   2, ACC_RO, 1, "RSVD1_0"   },
    { 2,  28, ACC_RW, 0, "BUF"       },
    { 30,  2, ACC_RO, 1, "RSVD31_30" },
};

// EPBUFCFG (0x1C): [1:0] reserved, BUF_SB[29:2] RW, [31:30] reserved.
static const usb_field_t epbufcfg_fields[] = {
    { 0,   2, ACC_RO, 1, "RSVD1_0"   },
    { 2,  28, ACC_RW, 0, "BUF_SB"    },
    { 30,  2, ACC_RO, 1, "RSVD31_30" },
};

// INTEN (0x24): all 32 bits RW.
static const usb_field_t inten_fields[] = {
    { 0, 32, ACC_RW, 0, "INT_EN" },
};

// INTROUTE (0x2C): all 32 bits RW.
static const usb_field_t introute_fields[] = {
    { 0, 32, ACC_RW, 0, "ROUTE_INT" },
};

// CONFIG (0x30): PHYSEP[4:0] RO, SB/DB/TREG RO, [31:8] reserved. All defined RO
// fields may be non-zero HW constants, so no read-0 there; only the reserved
// [31:8] range gets chk_zero.
static const usb_field_t config_fields[] = {
    { 0,  5, ACC_RO, 0, "PHYSEP"   },
    { 5,  1, ACC_RO, 0, "SB"       },
    { 6,  1, ACC_RO, 0, "DB"       },
    { 7,  1, ACC_RO, 0, "TREG"     },
    { 8, 24, ACC_RO, 1, "RSVD31_8" },
};

// EPTOGGLE (0x34): TOGGLE[29:0] RO, [31:30] reserved.
static const usb_field_t eptoggle_fields[] = {
    { 0,  30, ACC_RO, 0, "TOGGLE"    },
    { 30,  2, ACC_RO, 1, "RSVD31_30" },
};

// INTPLL (0x38): SEL_EXT_CLK[0] RW, [31:1] reserved.
static const usb_field_t intpll_fields[] = {
    { 0,  1, ACC_RW, 0, "SEL_EXT_CLK" },
    { 1, 31, ACC_RO, 1, "RSVD31_1"    },
};

#define REG_DESC(off, nm, tbl) \
    { (off), (nm), (tbl), (sizeof(tbl) / sizeof((tbl)[0])) }

// Shared register table. Layout is identical for USBDC0 and USBDC1 (same
// 16-register bank), so one table drives both. Registers deliberately excluded:
// EPLISTSTART 0x08 / DATABUFSTART 0x0C (DMA pointers), EPSKIP 0x14 (self-
// clearing), INTSTAT 0x20 / INTSETSTAT 0x28 (W1C / W1S), and the 0x3C-0x3F
// reserved word (removed by request).
static const usb_reg_desc_t usb_reg_table[] = {
    REG_DESC(0x00u, "DEVCMDSTAT", devcmdstat_fields),
    REG_DESC(0x04u, "INFO",       info_fields),
    REG_DESC(0x10u, "LPM",        lpm_fields),
    REG_DESC(0x18u, "EPINUSE",    epinuse_fields),
    REG_DESC(0x1Cu, "EPBUFCFG",   epbufcfg_fields),
    REG_DESC(0x24u, "INTEN",      inten_fields),
    REG_DESC(0x2Cu, "INTROUTE",   introute_fields),
    REG_DESC(0x30u, "CONFIG",     config_fields),
    REG_DESC(0x34u, "EPTOGGLE",   eptoggle_fields),
    REG_DESC(0x38u, "INTPLL",     intpll_fields),
};

#define USB_REG_TABLE_LEN (sizeof(usb_reg_table) / sizeof(usb_reg_table[0]))

// RO-immutability probe patterns. Three distinct values so a bit that happens
// to match one pattern cannot pass by coincidence.
static const uint32_t ro_probe[3] = { 0x00000000u, 0xA5A5A5A5u, 0x5A5A5A5Au };

// Build a contiguous bit-field mask for a field of the given lsb/width.
static inline uint32_t field_mask(uint8_t lsb, uint8_t width) {
    uint32_t m = (width >= 32u) ? 0xFFFFFFFFu : ((1u << width) - 1u);
    return m << lsb;
}

// Print "[bit N]" for a 1-bit field or "[bits msb:lsb]" for a wider field.
static void print_field_bits(uint8_t lsb, uint8_t width) {
    if (width == 1u) {
        VPRINTF(LOW, "[bit %d]", lsb);
    } else {
        VPRINTF(LOW, "[bits %d:%d]", lsb + width - 1, lsb);
    }
}

// Check one RW field: write a masked-random value confined to this field's
// bits, read back, and compare only this field. All other bits of the register
// are written 0 in the same access (harmless for the RW config registers, all
// of which are exercised while the controller is quiescent). Returns 1 on
// mismatch, 0 on match.
static int check_field_rw(uint32_t addr, const usb_field_t *f,
                          const char *bank, const char *reg) {
    uint32_t mask = field_mask(f->lsb, f->width);
    uint32_t wr   = xorshift32() & mask;
    lsu_write_32(addr, wr);
    uint32_t rd = lsu_read_32(addr) & mask;
    if (rd != wr) {
        VPRINTF(LOW, "ERROR: %s %s.%s ", bank, reg, f->field);
        print_field_bits(f->lsb, f->width);
        VPRINTF(LOW, " RW mismatch: wrote 0x%x got 0x%x\n",
                (wr >> f->lsb), (rd >> f->lsb));
        return 1;
    }
    return 0;
}

// Check one RO field: write the three probe patterns, reading after each, and
// require the field bits to be immutable across all three. The first write also
// satisfies write-before-read so the reads never return X. Reserved fields
// (chk_zero) must ADDITIONALLY read back 0. Returns 1 on any violation.
static int check_field_ro(uint32_t addr, const usb_field_t *f,
                          const char *bank, const char *reg) {
    uint32_t mask = field_mask(f->lsb, f->width);
    uint32_t ref  = 0u;
    for (int i = 0; i < 3; i++) {
        lsu_write_32(addr, ro_probe[i]);
        uint32_t rd = lsu_read_32(addr) & mask;
        if (i == 0) {
            ref = rd;
        } else if (rd != ref) {
            VPRINTF(LOW, "ERROR: %s %s.%s ", bank, reg, f->field);
            print_field_bits(f->lsb, f->width);
            VPRINTF(LOW, " %s not immutable: was 0x%x now 0x%x after writing "
                    "0x%x  <-- possible RTL bug\n",
                    (f->chk_zero ? "reserved" : "RO"),
                    (ref >> f->lsb), (rd >> f->lsb), ro_probe[i]);
            return 1;
        }
    }
    if (f->chk_zero && ref != 0u) {
        VPRINTF(LOW, "ERROR: %s %s.%s ", bank, reg, f->field);
        print_field_bits(f->lsb, f->width);
        VPRINTF(LOW, " reserved not read-as-0: got 0x%x  <-- possible RTL bug\n",
                (ref >> f->lsb));
        return 1;
    }
    return 0;
}

// Walk the shared register table over one device bank, checking every field.
// Emits a per-field line ONLY on failure, plus a concise per-register summary.
// Returns the number of failing fields found.
static int check_reg_bank(uint32_t base, const char *bank) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB register check: bank %s (base 0x%x) ---\n",
            bank, base);
    for (uint32_t i = 0; i < USB_REG_TABLE_LEN; i++) {
        const usb_reg_desc_t *r = &usb_reg_table[i];
        uint32_t addr = base + r->offset;
        int reg_errors = 0;
        for (uint32_t j = 0; j < r->nfields; j++) {
            const usb_field_t *f = &r->fields[j];
            switch (f->access) {
                case ACC_RW:
                    reg_errors += check_field_rw(addr, f, bank, r->name);
                    break;
                case ACC_RO:
                    reg_errors += check_field_ro(addr, f, bank, r->name);
                    break;
                case ACC_W1C:
                default:
                    // W1C / self-clearing: not a plain RW or RO check. Listed
                    // in the field table for documentation only; skipped here.
                    break;
            }
        }
        if (reg_errors == 0) {
            VPRINTF(LOW, "%s %s (0x%x) ok\n", bank, r->name, addr);
        }
        errors += reg_errors;
    }
    return errors;
}

void main(void) {

    int error_count = 0;

    VPRINTF(LOW, "=================\nMCU: USB dev0/dev1 register RW test\n=================\n\n");

    // Standard MCU boot sequence. No USB core bring-up and no hub connect: this
    // is a standalone register-access test, so the controllers stay quiescent
    // and we can safely randomize their configuration registers.
    boot_mcu();

    // Exercise both embedded device controllers with the shared table.
    error_count += check_reg_bank(USB_DEV0_REG_BASE_ADDR, "DEV0");
    error_count += check_reg_bank(USB_DEV1_REG_BASE_ADDR, "DEV1");

    VPRINTF(LOW, "\nMCU: USB register RW test complete, error_count = %d\n",
            error_count);

    if (error_count == 0) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
