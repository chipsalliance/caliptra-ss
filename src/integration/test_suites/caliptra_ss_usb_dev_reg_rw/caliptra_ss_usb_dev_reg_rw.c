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
// Description: USB compound register read/write test for the Caliptra
//  Subsystem, exercising BOTH embedded device controllers (USBDC0 and USBDC1)
//  AND the virtual-hub register set in a single run.
//
//  All three register banks are directly reachable from the MCU LSU AXI master
//  with no RTL change:
//    USBDC0 registers at SOC_USB_COMBO_DEV0_CSR_BASE_ADDR (0x2000_0000)
//    USBDC1 registers at SOC_USB_DEV1_CSR_BASE_ADDR       (0x2000_2000)
//    HUB    registers at SOC_USB_COMBO_HUB_BASE_ADDR      (0x2000_1000)
//  This test therefore uses the ABSOLUTE upstream CSR base macros directly
//  (not the compile-time USB_DEV_SEL selection), walks one shared
//  register-disposition table over the two identical device banks, and a
//  second, separate table over the hub bank.
//
//  COMPOUND REGISTER SPLIT (current register specification).
//  The compound structure instantiates both device CSR banks with the VHDL
//  generic C_USB_HUB => TRUE (ip_xxx_3511_hs_mem_compound_structure.a.vhdl
//  lines 1481 and 1583). That generic gates several device fields out of the
//  read and write decode of usb_reg_if.m.vhdl, and the corresponding controls
//  were MOVED into the hub register set:
//    - DEVCMDSTAT.OTG_C[27]              gated at line 367 -> device bit now
//                                        reserved / reads 0
//    - LPM[0x10] bits 16/17/18 (VBus_Comp_OFF, CHRG_VBUS, DISCHRG_VBUS) and
//      bits 20/21 (ADPPROBE, SESSION_END)
//                                        gated at lines 409 (read) and 682
//                                        (write) -> device bits now reserved
//    - PHYDEBUG[0x3C] (UTMI+/ULPI debug) whole register gated at line 496 and
//                                        in the write decode -> device word
//                                        reads 0; the register now lives in
//                                        the HUB aperture at 0x2000_103C
//  The hub set correspondingly has three register words inside its 0x2000_1000
//  aperture: HUB_CONTROL 0x30 (C_HUB_CS), HUB_LPM 0x34 (C_HUB_LPM, a NEW
//  register) and HUB_ULPIDEBUG 0x3C (C_HUB_PHY, the moved PHY debug register).
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
//    check. EPLISTSTART/DATABUFSTART are included field-by-field (their
//    writable address bits are RW; the low bits below the programmable field
//    are hardwired 0 and checked read-as-0 - EPLISTSTART [7:0], DATABUFSTART
//    [16:0] since this integration sets the C_DALB generic to 17).
//    A few bits are marked ACC_SKIP (documented in the field table but not
//    driven in the RW walk): DEVCMDSTAT DEV_ADDR/DEV_EN and
//    CONFIG.RSVD31_11 by request, plus DEVCMDSTAT DSUS/LPM_SUS because a write
//    there triggers a remote-wakeup action instead of storing the value.
//    EPSKIP (0x14) SKIP bits are ACC_SKIP: hardware self-clears them on its
//    own (see the EPSKIP field table comment), so they have no stable storage
//    to read back. The DEVICE PHYDEBUG word (0x3C) is NO LONGER a functional
//    register on this compound (see the register-split note above): it is
//    checked as a reserved read-as-0 word, and the real UTMI+/ULPI debug
//    register is exercised on the HUB bank instead. Whole registers excluded:
//    INTSTAT/INTSETSTAT (W1C/W1S).
//
//  HUB-BANK RESERVED-BIT RULE (important, differs from the device banks).
//  The hub register words are NOT a decoded register file; they are entries of
//  the writable ep0_mem word array in usb_ep0_hub_descr.m.vhdl, whose write
//  path is the unconditional "ep0_mem(reg_waddr) <= reg_wdata" at line 501.
//  A spec-reserved hub bit therefore DOES store whatever firmware writes, and
//  classifying it ACC_RO + chk_zero would report a false RTL bug on every run.
//  Hub reserved fields are consequently ACC_SKIP, and only the bits hardware
//  actually drives (Speed, VbusDebounced, HIRD_HW, PHY_RDATA/PHY_ACCESS) are
//  classified RO/skip on hardware grounds.
//
//  Test structure (both phases run over DEV0, DEV1 then HUB):
//    Phase 1 - reset-value check: read each register ONCE, before any write,
//              and compare against its documented post-reset value (see the
//              rst_val/rst_mask columns of the shared table). This observes the
//              true reset state.
//    Phase 2 - RW/RO access-class walk: exercise every field per its access
//              class as described above.
//
//  Address-aliasing RTL hazard honored by construction (see
//  claude_md/09_usb_hub_composite_migration.md and docs/usb_register_structure.md):
//  the device register file decodes only haddr[5:2] (a 16-register / 4-bit
//  window), so any offset >= 0x40 aliases back into 0x00-0x3C; the table
//  contains no offset >= 0x40.
//
//  The former DataKnown_A write-before-read hazard (reading a dev*_axi register
//  never written since reset used to drive X and fire the fatal DataKnown_A
//  assertion in u_dev0_axi2ahb.u_r_resp_fifo) has been fixed in the RTL: the
//  dev*_axi read path no longer returns X for never-written registers. The
//  Phase-1 reset-value reads are therefore legal with no hub bring-up and no
//  per-register write-before-read workaround, so the two hub enable/connect
//  writes that used to precede them have been removed. This is a register-only
//  test: it drives no USB traffic, so it can freely randomize the configuration
//  registers on both controllers. The companion UVM sequence
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

// ---------------------------------------------------------------------------
// Number of physical endpoints excluding the default control endpoint. This
// MUST track USB_C_DEV0_NBPHYSEP / USB_C_DEV1_NBPHYSEP in caliptra_ss_top.sv
// (both 28), which override the ip_xxx_3511_hs_mem_compound.e.vhdl default of
// 14 and are also what caliptra_ss_top_tb.sv passes down.
//
// The RTL sizes EPSKIP, EPINUSE, EPBUFCFG, INTEN, INTROUTE and EPTOGGLE as
// (C_NBPHYSEP+1 downto 0), so the implemented per-endpoint field is
// bits [USB_EP_MSB:0] and only the bits above it are reserved. Deriving the
// table bounds from this one constant keeps the field tables correct if the
// generic changes again; a hard-coded width silently turns every per-endpoint
// bit above the stale bound into a bogus "reserved not immutable" failure.
//
// CONFIG.PHYSEP[4:0] reads C_NBPHYSEP back from hardware, so the reset-value
// phase checks it against USB_C_NBPHYSEP as a tripwire: if the generic moves,
// the test reports a single clear CONFIG mismatch instead of a handful of
// confusing per-register "possible RTL bug" lines.
// ---------------------------------------------------------------------------
#define USB_C_NBPHYSEP    28
#define USB_EP_MSB        (USB_C_NBPHYSEP + 1)   // 29: top implemented EP bit
#define USB_EP_WIDTH      (USB_EP_MSB + 1)       // 30: implemented EP field width
#define USB_EP_RSVD_LSB   USB_EP_WIDTH           // 30: first reserved bit
#define USB_EP_RSVD_WIDTH (32 - USB_EP_WIDTH)    //  2: reserved field width

// Access class of one bit-field.
typedef enum {
    ACC_RW   = 0, // read/write: write a masked-random value, read back, compare
    ACC_RO   = 1, // read-only: must be immutable across the 3 write patterns
    ACC_W1C  = 2, // write-1-to-clear / self-clearing: not a plain RW/RO check
    ACC_SKIP = 3  // present for documentation only: not driven in the RW walk
} usb_acc_t;


// One bit-field of a register.
typedef struct {
    uint8_t     lsb;      // field least-significant bit
    uint8_t     width;    // field width in bits
    usb_acc_t   access;   // access class
    uint8_t     chk_zero; // 1: (reserved) field must ALSO read back 0
    const char *field;    // field name for logging
} usb_field_t;

// One register: offset, name, its field table, and its reset expectation.
// rst_mask selects which bits are checked at reset (rst_mask == 0 means the
// register is skipped by the reset-value phase). The reset check compares
// (read & rst_mask) against (rst_val & rst_mask).
typedef struct {
    uint32_t           offset;   // byte offset from the bank base
    const char        *name;     // register name for logging
    const usb_field_t *fields;   // field table
    uint32_t           nfields;  // number of fields
    uint32_t           rst_val;  // expected reset value (masked by rst_mask)
    uint32_t           rst_mask; // bits checked at reset (0 => skip register)
} usb_reg_desc_t;


// ---------------------------------------------------------------------------
// DEVCMDSTAT (0x00). Classification below is RTL-verified against the register
// "0000" read and write decode in usb_reg_if.m.vhdl, cross-checked with the USB
// Device Software Interface spec section 6.2.1.
//
// SETUP[8] and the three remaining *_C change bits (DCON_C[24], DSUS_C[25],
// DRES_C[26]) are W1C: the RTL write branch only clears the stored bit when a 1
// is written, so they are ACC_W1C and excluded from the plain RW compare.
//
// OTG_C[27] is NO LONGER a device bit on this compound. Both device banks are
// elaborated with C_USB_HUB => TRUE, and the OTG-change read decode is wrapped
// in "if not(C_USB_HUB)" (usb_reg_if.m.vhdl line 367), so bit 27 is never
// driven and reads 0. It is therefore reclassified from ACC_W1C to
// ACC_RO + chk_zero (RSVD27) and IS now included in the reset-value mask,
// which also removes the historical OTG_C reset-mask waiver: the AValid /
// SessEnd power-up edges can no longer latch anything into this bit.
//
// Plain RW (storage element written from reg_wdata and read back from the same
// register): PLL_ON[9], FORCE_VBUS[10] (reg_dev_force_vbus), LPM_SUP[11], the
// four IntOnNAK bits [15:12], DCON[16], PFSC[21] (reg_dev_force_fullspeed) and
// PHY_TEST_MODE[31:29] (reg_dev_phy_test_mode, the USB2.0 PHY test-mode
// selector). This is a standalone register test with the controllers quiescent
// (no live link or DMA), so driving these bits is safe. FORCE_VBUS does feed
// usbreg_dev_connect_int alongside DCON[16], so a random pattern that sets both
// momentarily asserts the internal connect; nothing samples it here.
//
// ACC_SKIP (documented in the table but not driven in the RW walk) splits into
// two reasons:
//   - RW per spec, excluded by request: DEV_ADDR[6:0], DEV_EN[7].
//   - Action bits with NO storage behind the write, so an RW compare can never
//     pass: DSUS[17] and LPM_SUS[19]. Writing 0 to either only pulses a remote
//     wakeup request (usbreg_remotewakeup / usbreg_lpmremotewakeup); the value
//     read back comes from the HW-maintained suspend state
//     (reg_dev_suspend / reg_dev_lpm_suspend), which stays 0 while the link is
//     down. Driving them as ACC_RW would fail intermittently whenever the
//     random pattern happened to set the bit.
//
// Defined RO fields that may legally read non-zero (so no read-as-0 check):
// LPM_REWP[20] (HW-set from the LPM token), Speed[23:22] (pie_speed: 01b
// full-speed / 10b high-speed) and VbusDebounced[28] (live VBus status).
//
// Reserved bits of this register on the compound: bit 18 (never driven by the
// read decode in any configuration) and bit 27 (undriven because
// C_USB_HUB = TRUE, see above). Both are ACC_RO + chk_zero (must be immutable
// AND read back 0; a violation is a candidate RTL bug).
// ---------------------------------------------------------------------------
static const usb_field_t devcmdstat_fields[] = {
    { 0,  7, ACC_SKIP, 0, "DEV_ADDR"      }, // RW per spec, excluded from the RW walk by request
    { 7,  1, ACC_SKIP, 0, "DEV_EN"        }, // RW per spec, excluded from the RW walk by request
    { 8,  1, ACC_W1C, 0, "SETUP"          }, // W1C, not plain RW
    { 9,  1, ACC_RW,  0, "PLL_ON"         },
    { 10, 1, ACC_RW,  0, "FORCE_VBUS"     }, // reg_dev_force_vbus: real RW storage, reset 0
    { 11, 1, ACC_RW,  0, "LPM_SUP"        },
    { 12, 1, ACC_RW,  0, "IntOnNAK_AO"    },
    { 13, 1, ACC_RW,  0, "IntOnNAK_AI"    },
    { 14, 1, ACC_RW,  0, "IntOnNAK_CO"    },
    { 15, 1, ACC_RW,  0, "IntOnNAK_CI"    },
    { 16, 1, ACC_RW,  0, "DCON"           }, // RW per spec Chapter 5
    { 17, 1, ACC_SKIP, 0, "DSUS"          }, // write-0 pulses a remote wakeup; no storage to read back
    { 18, 1, ACC_RO,  1, "RSVD18"         }, // only bit the RTL read decode leaves undriven
    { 19, 1, ACC_SKIP, 0, "LPM_SUS"       }, // write-0 pulses an LPM remote wakeup; read-back is HW suspend state
    { 20, 1, ACC_RO,  0, "LPM_REWP"       }, // defined RO (may be non-zero)
    { 21, 1, ACC_RW,  0, "PFSC"           }, // reg_dev_force_fullspeed: real RW storage
    { 22, 2, ACC_RO,  0, "Speed"          }, // pie_speed: RO status, legally non-zero (01b FS / 10b HS)
    { 24, 1, ACC_W1C, 0, "DCON_C"         }, // W1C, not plain RW
    { 25, 1, ACC_W1C, 0, "DSUS_C"         }, // W1C, not plain RW
    { 26, 1, ACC_W1C, 0, "DRES_C"         }, // W1C, not plain RW
    { 27, 1, ACC_RO,  1, "RSVD27"         }, // was OTG_C; undriven because C_USB_HUB=TRUE
    { 28, 1, ACC_RO,  0, "VbusDebounced"  }, // defined RO (may be non-zero)
    { 29, 3, ACC_RW,  0, "PHY_TEST_MODE"  }, // RW per spec (USB2.0 PHY test modes)
};

// INFO (0x04): FRAME_NR[10:0] RO, ERR_CODE[14:11] RW per spec, bit15 reserved,
// CHIP_ID[31:16] RO (a non-zero HW constant, so NO read-0 check).
static const usb_field_t info_fields[] = {
    { 0,  11, ACC_RO, 0, "FRAME_NR" },
    { 11,  4, ACC_RW, 0, "ERR_CODE" },
    { 15,  1, ACC_RO, 1, "RSVD15"   },
    { 16, 16, ACC_RO, 0, "CHIP_ID"  }, // defined RO constant, may be non-zero
};

// EPLISTSTART (0x08): EP Command/Status List base address. The list is
// 256-byte aligned, so the low 8 bits are hardwired 0 (reserved, read-as-0);
// the base address bits [31:8] are RW. No DMA runs in this standalone test, so
// exercising the writable bits is safe.
static const usb_field_t epliststart_fields[] = {
    { 0,   8, ACC_RO, 1, "RSVD7_0" }, // 256-byte aligned, hardwired 0
    { 8,  24, ACC_RW, 0, "EP_LIST" }, // list base address bits [31:8]
};

// DATABUFSTART (0x0C): data buffer page pointer. The programmable field width
// is set by the C_DALB generic. In THIS integration the top level overrides
// C_DALB=17 (see usb_reg_if.m.vhdl register "0011"; C_DALB defaults to 22 in
// the module but ip_xxx_3511_hs_mem_compound.e.vhdl sets it to 17), so the
// writable DA_BUF field is reg_wdata(31 downto 17) = bits [31:17]. The low
// bits (C_DALB-1 downto 0) = [16:0] are hardwired 0 (read-as-0). RW on the high
// bits only; safe to exercise since no DMA runs in this standalone test.
static const usb_field_t databufstart_fields[] = {
    { 0,  17, ACC_RO, 1, "RSVD16_0" }, // bits (C_DALB-1 downto 0), hardwired 0
    { 17, 15, ACC_RW, 0, "DA_BUF"   }, // data buffer page pointer bits [31:C_DALB]=[31:17]
};

// LPM (0x10) per the current compound register specification:
//   HIRD_HW[3:0]    RO  (loaded by HW from the last received LPM token)
//   HIRD_SW[7:4]    RW  (reg_lpm_hird_sw)
//   DataPending[8]  RW  (reg_lpm_nyet)
//   [31:9]          reserved, read-as-0
//
// The ENTIRE upper half of this register was removed from the device view by
// the compound split. usb_reg_if.m.vhdl guards the VBus/charger/ADP group with
// "if not(C_USB_HUB)" on both the read side (line 409: bits 16/17/18 plus the
// sync_avalid ADPPROBE bit 20 and sync_sessend ADP_SENSE bit 21) and the write
// side (line 682: reg_vbuscomp_off / reg_chrg_vbus / reg_dischrg_vbus), and
// both device banks are elaborated with C_USB_HUB => TRUE. Those bits are
// therefore undriven and unwritable here, so they are folded into a single
// reserved RSVD31_9 field with chk_zero set. This also makes the whole 32-bit
// word a valid reset expectation (previously bits 20/21 had to be waived from
// the reset mask because they tracked the live AValid / SessEnd pins).
static const usb_field_t lpm_fields[] = {
    { 0,   4, ACC_RO, 0, "HIRD_HW"     }, // HW-loaded from the LPM token
    { 4,   4, ACC_RW, 0, "HIRD_SW"     },
    { 8,   1, ACC_RW, 0, "DataPending" }, // reg_lpm_nyet
    { 9,  23, ACC_RO, 1, "RSVD31_9"    }, // VBus/charger/ADP group gated out by C_USB_HUB
};

// EPSKIP (0x14): per-endpoint skip vector, width tracked by the C_NBPHYSEP
// generic (usb_reg_if.m.vhdl register "0101": reg_ep_skip <=
// reg_wdata(C_NBPHYSEP+1 downto 0)). With C_NBPHYSEP=28 the implemented field
// is bits [29:0]. Only the bits above USB_EP_MSB (here [31:30]) do not exist
// (read-as-0).
//
// SKIP is ACC_SKIP (documented but NOT driven in the RW walk) because hardware
// clears these bits on its own with no USB traffic required. The DMA state
// machine in usb_dma.m.vhdl polls the vector unconditionally from its IDLE
// state with a free-running round-robin index:
//   when IDLE =>
//     if usbreg_ep_skip(skip_ep) = '1' then clear_active := TRUE;
//     else skip_ep <= skip_ep + 1 (wrapping at C_NBPHYSEP+1); end if;
// and the skip-service path asserts dma_clear_skip, which in usb_reg_if.m.vhdl
// does "if dma_clear_skip = '1' then reg_ep_skip(dma_skip_ep) <= '0'".
// So any bit firmware sets is cleared as soon as the scan reaches it. In the
// few hundred ns between the write and the read-back roughly one bit is
// cleared, which showed up as an intermittent one-bit RW mismatch (e.g. wrote
// 0x0AD1BD64, read 0x0AD1B964: XOR 0x400, bit 10 only) whose position varies
// with where skip_ep happened to be. There is no stable storage to compare
// against, so an RW check here can never be deterministic. Asserting the
// self-clear itself belongs in a directed DMA/EP test, not in this
// access-class walk.
static const usb_field_t epskip_fields[] = {
    { 0, USB_EP_WIDTH,      ACC_SKIP, 0, "SKIP"    }, // per-EP skip bits [C_NBPHYSEP+1:0]
    { USB_EP_RSVD_LSB, USB_EP_RSVD_WIDTH,
                            ACC_RO, 1, "RSVD_HI" }, // above C_NBPHYSEP+1, read-as-0
};


// EPINUSE (0x18): per-endpoint buffer-in-use vector. The register width tracks
// the C_NBPHYSEP generic (number of physical EPs excluding the default control
// EP): the RTL exposes reg_ep_bufinuse(C_NBPHYSEP+1 downto 0). This integration
// sets C_NBPHYSEP=28 (USB_C_DEV0_NBPHYSEP / USB_C_DEV1_NBPHYSEP in
// caliptra_ss_top.sv), so the register spans bits [29:0]. Bits [1:0] are EP0
// (single-buffer, hardwired 0). The writable buffer-select field is
// reg_wdata(C_NBPHYSEP+1 downto 2) = bits [29:2] (usb_reg_if.m.vhdl register
// "0110"). Only the bits above C_NBPHYSEP+1 ([31:30]) do not exist (read-as-0).
static const usb_field_t epinuse_fields[] = {
    { 0, 2,                 ACC_RO, 1, "RSVD1_0" }, // EP0 single-buffer, hardwired 0
    { 2, USB_EP_WIDTH - 2,  ACC_RW, 0, "BUF"     }, // buffer-select bits [C_NBPHYSEP+1:2]
    { USB_EP_RSVD_LSB, USB_EP_RSVD_WIDTH,
                            ACC_RO, 1, "RSVD_HI" }, // above C_NBPHYSEP+1, read-as-0
};

// EPBUFCFG (0x1C): per-endpoint single/double buffer config. Same C_NBPHYSEP
// width as EPINUSE: reg_ep_doublebuffer(C_NBPHYSEP+1 downto 2) <=
// reg_wdata(C_NBPHYSEP+1 downto 2) (usb_reg_if.m.vhdl register "0111"), so with
// C_NBPHYSEP=28 the writable field is bits [29:2]. Bits [1:0] are EP0
// (hardwired 0) and the bits above C_NBPHYSEP+1 ([31:30]) do not exist
// (read-as-0).
static const usb_field_t epbufcfg_fields[] = {
    { 0, 2,                 ACC_RO, 1, "RSVD1_0" }, // EP0, hardwired 0
    { 2, USB_EP_WIDTH - 2,  ACC_RW, 0, "BUF_SB"  }, // config bits [C_NBPHYSEP+1:2]
    { USB_EP_RSVD_LSB, USB_EP_RSVD_WIDTH,
                            ACC_RO, 1, "RSVD_HI" }, // above C_NBPHYSEP+1, read-as-0
};

// INTEN (0x24): interrupt enable. The per-endpoint enable field tracks
// C_NBPHYSEP: reg_ep_int_enable <= reg_wdata(C_NBPHYSEP+1 downto 0)
// (usb_reg_if.m.vhdl register "1001"), plus the frame interrupt enable [30] and
// device interrupt enable [31]. With C_NBPHYSEP=28 the per-EP field is [29:0],
// so it meets the frame/dev bits directly and the register has NO reserved
// field left.
static const usb_field_t inten_fields[] = {
    { 0, USB_EP_WIDTH, ACC_RW, 0, "INT_EN_EP"   }, // per-EP enables [C_NBPHYSEP+1:0]
    { 30, 2,           ACC_RW, 0, "INT_EN_FRDV" }, // frame [30] and device [31] enables
};

// INTROUTE (0x2C): interrupt routing. Same layout as INTEN:
// reg_ep_int_route <= reg_wdata(C_NBPHYSEP+1 downto 0) = bits [29:0] with
// C_NBPHYSEP=28, plus frame [30] and device [31] route bits (usb_reg_if.m.vhdl
// register "1011"). No reserved field remains at this generic value.
static const usb_field_t introute_fields[] = {
    { 0, USB_EP_WIDTH, ACC_RW, 0, "ROUTE_EP"   }, // per-EP route [C_NBPHYSEP+1:0]
    { 30, 2,           ACC_RW, 0, "ROUTE_FRDV" }, // frame [30] and device [31] route
};


// CONFIG (0x30): PHYSEP[4:0] RO, SB/DB/TREG RO, UTMI[9]/ULPI[10] RO,
// [31:11] reserved. All defined RO fields may be non-zero HW constants, so no
// read-0 there. RSVD31_11 is classified ACC_SKIP (excluded from the RW walk by
// request); it is present in the table for documentation only. PHYSEP reads
// back the C_NBPHYSEP generic and the reset phase checks it against
// USB_C_NBPHYSEP (see the rst_val / rst_mask columns of the shared table) as a
// tripwire on the generic.
//
// Bits 9 and 10 are PHY-support build flags: usb_reg_if.m.vhdl register "1100"
// sets bit 9 when C_UTMI_SUPPORT and bit 10 when C_ULPI_SUPPORT. Bit 8 remains
// unused - the C_PLL_ENABLE leg that used to drive it is commented out in the
// same decode, alongside the removal of the 0x38 PLL register (see
// intpll_fields).
static const usb_field_t config_fields[] = {
    { 0,  5, ACC_RO,   0, "PHYSEP"    }, // reads back C_NBPHYSEP
    { 5,  1, ACC_RO,   0, "SB"        },
    { 6,  1, ACC_RO,   0, "DB"        },
    { 7,  1, ACC_RO,   0, "TREG"      },
    { 8,  1, ACC_RO,   0, "RSVD8"     }, // former PLL flag, decode leg commented out
    { 9,  1, ACC_RO,   0, "UTMI"      }, // set when C_UTMI_SUPPORT
    { 10, 1, ACC_RO,   0, "ULPI"      }, // set when C_ULPI_SUPPORT
    { 11, 21, ACC_SKIP, 0, "RSVD31_11" }, // excluded from the RW walk by request
};

// EPTOGGLE (0x34): per-endpoint data-toggle status, usbreg_epinfo_toggle is
// declared (C_NBPHYSEP+1 downto 0) in usb_reg_if.m.vhdl, so the implemented RO
// field is bits [USB_EP_MSB:0] = [29:0] with C_NBPHYSEP=28 and only the bits
// above it ([31:30]) are reserved.
static const usb_field_t eptoggle_fields[] = {
    { 0, USB_EP_WIDTH,      ACC_RO, 0, "TOGGLE"  }, // toggle status [C_NBPHYSEP+1:0]
    { USB_EP_RSVD_LSB, USB_EP_RSVD_WIDTH,
                            ACC_RO, 1, "RSVD_HI" }, // above C_NBPHYSEP+1, read-as-0
};

// INTPLL (0x38): the PLL / external-clock register was REMOVED in this RTL
// revision. In usb_reg_if.m.vhdl the "1110" read decode and the
// usbreg_select_ext_clk / reg_ext_clk_enable path are all commented out, so the
// 0x38 address falls through to the default reg_rdata <= (others => '0') and
// reads 0. The test therefore only checks that the whole 0x38 word is a
// read-only location that reads back 0 (ACC_RO + chk_zero across all 32 bits).
static const usb_field_t intpll_fields[] = {
    { 0, 32, ACC_RO, 1, "RSVD" }, // register removed; whole word RO, reads 0
};

// PHYDEBUG (0x3C) on a DEVICE bank: the "UTMI+/ULPI debug" register MOVED to
// the hub by the compound register split, so there is no functional register
// behind this device address any more.
//
// The whole register select "1111" read decode is wrapped in
// "if not(C_USB_HUB)" (usb_reg_if.m.vhdl line 496) and the matching write
// decode is gated the same way (line 747), while every usbreg_phy_* output is
// forced to zero at lines 269-276. Both device banks are elaborated with
// C_USB_HUB => TRUE, so the address falls through to the default
// reg_rdata <= (others => '0') and reads 0, exactly like the removed 0x38 PLL
// register. The device-side check is therefore the same shape as INTPLL: the
// whole word must be read-only and read back 0.
//
// The real PHY debug register IS exercised, on the hub bank: see
// hub_phydebug_fields below.
static const usb_field_t phydebug_fields[] = {
    { 0, 32, ACC_RO, 1, "RSVD" }, // moved to the hub; device word RO, reads 0
};

#define REG_DESC(off, nm, tbl, rv, rm) \
    { (off), (nm), (tbl), (sizeof(tbl) / sizeof((tbl)[0])), (rv), (rm) }


// Shared register table. Layout is identical for USBDC0 and USBDC1 (same
// 16-register bank), so one table drives both. EPLISTSTART 0x08 and
// DATABUFSTART 0x0C are included field-by-field (their writable address bits
// are RW; the low bits below the programmable field are hardwired 0 and
// checked read-as-0 - EPLISTSTART [7:0], DATABUFSTART [16:0] with C_DALB=17).
// EPSKIP 0x14 SKIP bits are ACC_SKIP: the DMA skip scanner clears them with no
// USB traffic required, so they have no stable storage to read back (see the
// EPSKIP field table comment). The device PHYDEBUG word 0x3C is checked as a
// reserved read-as-0 location because the UTMI+/ULPI debug register MOVED to
// the hub bank. Registers deliberately excluded:
// INTSTAT 0x20 / INTSETSTAT 0x28 (W1C / W1S).
//
// Reset-value expectation (rst_val / rst_mask) per docs/usb_register_structure.md
// section 1.1:
//   DEVCMDSTAT : expected 0x00000800 (the spec reset value, LPM_SUP[11] set).
//                Five bits are EXCLUDED from the reset mask because they are
//                live or sticky HW status rather than fixed reset constants,
//                so they are not reliable reset expectations:
//                  Speed[23:22]      - pie_speed, the negotiated link speed
//                  VbusDebounced[28]  - VBus present
//                  DCON_C[24], DSUS_C[25], DRES_C[26] - the W1C
//                    status-change flags. These are HW-set and can only be
//                    cleared by firmware writing 1, so any environment event
//                    before the first read latches them.
//                That gives rst_mask 0xE83FFFFF. Bit 27 is NO LONGER waived:
//                it used to be the OTG_C flag that ANY power-up edge on avalid
//                (ADPPROBE) or sessend (ADPSENSE) could latch, but the OTG
//                read decode is compiled out by C_USB_HUB => TRUE, so bit 27
//                is now a plain reserved-0 bit and IS checked. All other 26
//                bits ARE checked, so a set reserved bit (18 or 27) is
//                reported as a candidate RTL issue.
//   INFO       : reset depends on CHIP_ID[31:16], so only the low 16 bits
//                (FRAME_NR / ERR_CODE / RSVD15) are checked against 0.
//   LPM        : reset 0x0 with ALL 32 bits checked (mask 0xFFFFFFFF). The
//                previous 0xFFCFFFFF mask waived bits 20/21 because they
//                tracked the live ADPPROBE / ADP_SENSE pins; those bits are
//                compiled out by C_USB_HUB => TRUE and now read a stable 0.
//   EPINUSE, EPBUFCFG, INTEN, INTROUTE, EPTOGGLE, INTPLL, PHYDEBUG : reset
//                0x0, all 32 bits checked.
//   CONFIG     : per-build RO constants. Only PHYSEP[4:0] is checked (mask
//                0x1F), against USB_C_NBPHYSEP: it is a direct read-back of the
//                C_NBPHYSEP generic and acts as a tripwire if the generic moves
//                away from the value the EP field tables are sized for. SB/DB/
//                TREG and the UTMI/ULPI PHY-support flags are left unchecked
//                because they depend on other build options.
static const usb_reg_desc_t usb_reg_table[] = {
    REG_DESC(0x00u, "DEVCMDSTAT",   devcmdstat_fields,   0x00000800u, 0xE83FFFFFu),
    REG_DESC(0x04u, "INFO",         info_fields,         0x00000000u, 0x0000FFFFu),
    REG_DESC(0x08u, "EPLISTSTART",  epliststart_fields,  0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x0Cu, "DATABUFSTART", databufstart_fields, 0x00000000u, 0xFFFE0000u),
    REG_DESC(0x10u, "LPM",        lpm_fields,        0x00000000u, 0xFFFFFFFFu),

    REG_DESC(0x14u, "EPSKIP",     epskip_fields,     0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x18u, "EPINUSE",    epinuse_fields,    0x00000000u, 0xFFFFFFFFu),

    REG_DESC(0x1Cu, "EPBUFCFG",   epbufcfg_fields,   0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x24u, "INTEN",      inten_fields,      0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x2Cu, "INTROUTE",   introute_fields,   0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x30u, "CONFIG",     config_fields,     USB_C_NBPHYSEP, 0x0000001Fu),
    REG_DESC(0x34u, "EPTOGGLE",   eptoggle_fields,   0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x38u, "INTPLL",     intpll_fields,     0x00000000u, 0xFFFFFFFFu),

    REG_DESC(0x3Cu, "PHYDEBUG",   phydebug_fields,   0x00000000u, 0xFFFFFFFFu),
};


#define USB_REG_TABLE_LEN (sizeof(usb_reg_table) / sizeof(usb_reg_table[0]))


// ===========================================================================
// HUB register bank (SOC_USB_COMBO_HUB_BASE_ADDR = 0x2000_1000).
//
// The hub aperture is NOT a decoded register file. It is the ep0_mem word
// array of usb_ep0_hub_descr.m.vhdl: most words hold the hub descriptors and
// the SETUP match table, and exactly THREE words are register words (the hub
// constants in that file at lines 82-84):
//   C_HUB_CS  = word 12 -> byte offset 0x30, hub Command/Status
//   C_HUB_LPM = word 13 -> byte offset 0x34, hub LPM (NEW in this spec)
//   C_HUB_PHY = word 15 -> byte offset 0x3C, hub UTMI+/ULPI debug (MOVED here
//                          from the device banks)
// Only those three offsets are in the hub table below. The surrounding words
// MUST NOT be walked: writing them would corrupt the descriptor ROM shadow /
// SETUP match table that every other USB test depends on. Word 14 (0x38) is
// not a register and is deliberately absent.
//
// IMPORTANT ACCESS-CLASS CAVEAT, repeated from the file header because it is
// easy to get wrong: these words are plain writable storage
// ("ep0_mem(reg_waddr) <= reg_wdata", line 501), guarded only by
// hub_write_lock - and lines 497-499 EXEMPT exactly these three register words
// from that lock, so they are always writable. Spec-reserved hub bits
// therefore DO retain written data. They are classified ACC_SKIP, never
// ACC_RO + chk_zero, so the walk does not manufacture false RTL-bug reports.
// Only the fields hardware itself drives are RO.
// ===========================================================================

// HUB_CONTROL (0x30, C_HUB_CS). Reset value 0x00000800: the ROM initialiser at
// lines 434-437 clears HUB_EN[0], HUB_DCON[16] and SELF_POWERED[18] and sets
// LPM_SUP[11].
//
// HW-driven (ACC_RO, legally non-zero so no read-as-0 check):
//   Speed[23:22]       <- pie_speed              (line 511)
//   VbusDebounced[28]  <- hub_vbusdebounced      (line 512)
//
// ACC_SKIP for a FUNCTIONAL reason, not a storage reason:
//   HUB_EN[0] and HUB_DCON[16]. Writing both sets hub_write_lock (line 528,
//   "ep0_mem(C_HUB_CS)(0) and ep0_mem(C_HUB_CS)(16)"), which freezes the
//   descriptor array, and it also signals a USB connect upstream. Driving
//   them in a register walk would change hub state mid-test, so they are
//   documented but not exercised here; the connect path is covered by the
//   enumeration tests.
//
// Plain RW storage: PLL_ON[9], FORCE_VBUS[10], LPM_SUP[11], SELF_POWERED[18],
// PFSC[21] (hub_force_fs, line 527).
static const usb_field_t hub_ctrl_fields[] = {
    { 0,  1, ACC_SKIP, 0, "HUB_EN"        }, // asserts hub_write_lock with HUB_DCON; not driven
    { 1,  8, ACC_SKIP, 0, "RSVD8_1"       }, // spec-reserved, but writable hub storage
    { 9,  1, ACC_RW,   0, "PLL_ON"        }, // hub_pll_on
    { 10, 1, ACC_RW,   0, "FORCE_VBUS"    }, // hub_force_vbus
    { 11, 1, ACC_RW,   0, "LPM_SUP"       }, // hub_lpm_sup, reset 1
    { 12, 4, ACC_SKIP, 0, "RSVD15_12"     }, // spec-reserved, writable hub storage
    { 16, 1, ACC_SKIP, 0, "HUB_DCON"      }, // signals connect / asserts hub_write_lock
    { 17, 1, ACC_SKIP, 0, "RSVD17"        }, // spec-reserved, writable hub storage
    { 18, 1, ACC_RW,   0, "SELF_POWERED"  }, // hub_self_powered
    { 19, 2, ACC_SKIP, 0, "RSVD20_19"     }, // spec-reserved, writable hub storage
    { 21, 1, ACC_RW,   0, "PFSC"          }, // hub_force_fs
    { 22, 2, ACC_RO,   0, "Speed"         }, // HW-loaded from pie_speed
    { 24, 4, ACC_SKIP, 0, "RSVD27_24"     }, // spec-reserved, writable hub storage
    { 28, 1, ACC_RO,   0, "VbusDebounced" }, // HW-loaded from hub_vbusdebounced
    { 29, 3, ACC_SKIP, 0, "RSVD31_29"     }, // spec-reserved, writable hub storage
};

// HUB_LPM (0x34, C_HUB_LPM) - the NEW register of this specification revision.
// Reset value 0x00000000.
//
//   HIRD_HW[3:0] ACC_RO : hardware reloads ep0_mem(C_HUB_LPM)(3 downto 0) from
//                         hub_lpm_hird_hw on EVERY clock (line 513), so a
//                         firmware write cannot stick. Not chk_zero - the field
//                         legally reflects the last received LPM token.
//   HIRD_SW[7:4] ACC_RW : drives hub_lpm_hird_sw (line 530).
//   [31:8]              : spec-reserved but writable hub storage -> ACC_SKIP.
static const usb_field_t hub_lpm_fields[] = {
    { 0,  4, ACC_RO,   0, "HIRD_HW"   }, // continuously reloaded from hub_lpm_hird_hw
    { 4,  4, ACC_RW,   0, "HIRD_SW"   }, // hub_lpm_hird_sw
    { 8, 24, ACC_SKIP, 0, "RSVD31_8"  }, // spec-reserved, writable hub storage
};

// HUB_ULPIDEBUG (0x3C, C_HUB_PHY) - the UTMI+/ULPI debug register MOVED here
// from the device banks. Reset value 0x00000000.
//
// Field drives (usb_ep0_hub_descr.m.vhdl lines 532-536):
//   PHY_ADDR[7:0]   -> hub_phy_addr      RW
//   PHY_WDATA[15:8] -> hub_phy_wdata     RW
//   PHY_RDATA[23:16]                     RW storage, but ALSO loaded by HW
//                     from hub_phy_rdata when hub_phy_endtoggle asserts
//                     (line 508). No access is launched in this test
//                     (PHY_ACCESS stays 0), so it is treated as plain RW.
//   PHY_RW[24]      -> hub_phy_write     RW
//   PHY_ACCESS[25]  -> hub_phy_start     ACC_SKIP: writing 1 launches a live
//                     PHY transaction and HW then clears the bit and
//                     overwrites PHY_RDATA (lines 508-509), so it has no
//                     plain RW behaviour.
//   PHY_MODE[31]    -> hub_phy_mode      RW
//   [30:26]                              spec-reserved, writable hub storage
static const usb_field_t hub_phydebug_fields[] = {
    { 0,   8, ACC_RW,   0, "PHY_ADDR"   },
    { 8,   8, ACC_RW,   0, "PHY_WDATA"  },
    { 16,  8, ACC_RW,   0, "PHY_RDATA"  }, // RW here; HW overwrites it only on a real access
    { 24,  1, ACC_RW,   0, "PHY_RW"     },
    { 25,  1, ACC_SKIP, 0, "PHY_ACCESS" }, // self-clearing start bit; launches a live access
    { 26,  5, ACC_SKIP, 0, "RSVD30_26"  }, // spec-reserved, writable hub storage
    { 31,  1, ACC_RW,   0, "PHY_MODE"   },
};

// Hub register table. Reset expectations:
//   HUB_CONTROL : 0x00000800 (LPM_SUP set by the ROM initialiser). Speed[23:22]
//                 and VbusDebounced[28] are EXCLUDED because they are live HW
//                 status, exactly as on the device DEVCMDSTAT. Excluding bits
//                 22, 23 and 28 means clearing 0x00C00000 | 0x10000000 =
//                 0x10C00000, so the mask is ~0x10C00000 = 0xEF3FFFFF.
//   HUB_LPM     : 0x0 with HIRD_HW[3:0] excluded (mask 0xFFFFFFF0) - it tracks
//                 the last LPM token rather than a reset constant.
//   HUB_PHY     : 0x0, all 32 bits checked.
//
// The offsets are BANK-RELATIVE (the walker adds the base), which is why they
// are written as literals rather than as the SOC_USB_COMBO_HUB_* macros - those
// are absolute addresses. The per-entry comments give the absolute equivalent
// so the mapping to soc_address_map.h is explicit.
static const usb_reg_desc_t usb_hub_reg_table[] = {
    // SOC_USB_COMBO_HUB_CONTROL   = 0x2000_1030
    REG_DESC(0x30u, "HUB_CONTROL",   hub_ctrl_fields,     0x00000800u, 0xEF3FFFFFu),
    // SOC_USB_COMBO_HUB_LPM       = 0x2000_1034
    REG_DESC(0x34u, "HUB_LPM",       hub_lpm_fields,      0x00000000u, 0xFFFFFFF0u),
    // SOC_USB_COMBO_HUB_ULPIDEBUG = 0x2000_103C
    REG_DESC(0x3Cu, "HUB_ULPIDEBUG", hub_phydebug_fields, 0x00000000u, 0xFFFFFFFFu),
};

#define USB_HUB_REG_TABLE_LEN \
    (sizeof(usb_hub_reg_table) / sizeof(usb_hub_reg_table[0]))


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

// Read every register of the supplied table ONCE (before any write) and
// compare its post-reset value against the expected reset value in the table.
// Only the bits selected by rst_mask are compared; a register with
// rst_mask == 0 is skipped. This phase runs before check_reg_bank() so the
// reads observe the true reset state rather than values left by the RW/RO walk.
//
// The table is a parameter so the SAME walker serves the two device banks
// (usb_reg_table) and the hub bank (usb_hub_reg_table), which have different
// register sets since the compound register split.
//
// NOTE: these reset reads are performed with NO write-before-read workaround
// for the former DataKnown_A hazard. This is safe because the improved RTL no
// longer drives X on the dev*_axi read path for never-written registers, so the
// reads observe the true reset state without any hub bring-up.
static int check_reset_values(uint32_t base, const char *bank,
                              const usb_reg_desc_t *table, uint32_t ntable) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB reset-value check: bank %s (base 0x%x) ---\n",
            bank, base);
    for (uint32_t i = 0; i < ntable; i++) {
        const usb_reg_desc_t *r = &table[i];
        if (r->rst_mask == 0u) {
            // Per-build RO-constant register with no fixed reset expectation:
            // skipped by the reset-value phase.
            continue;
        }
        uint32_t addr = base + r->offset;
        uint32_t rd   = lsu_read_32(addr) & r->rst_mask;
        uint32_t exp  = r->rst_val & r->rst_mask;
        if (rd != exp) {
            VPRINTF(LOW, "ERROR: %s %s (0x%x) reset value mismatch: "
                    "expected 0x%x got 0x%x (mask 0x%x)\n",
                    bank, r->name, addr, exp, rd, r->rst_mask);
            errors++;
        } else {
            VPRINTF(LOW, "%s %s (0x%x) reset value ok (0x%x)\n",
                    bank, r->name, addr, rd);
        }
    }
    return errors;
}

// Walk the supplied register table over one bank, checking every field. Emits
// a per-field line ONLY on failure, plus a concise per-register summary.
// Returns the number of failing fields found. The table is a parameter so the
// same walker drives both the device banks and the hub bank.
static int check_reg_bank(uint32_t base, const char *bank,
                          const usb_reg_desc_t *table, uint32_t ntable) {

    int errors = 0;
    VPRINTF(LOW, "\n--- USB register check: bank %s (base 0x%x) ---\n",
            bank, base);
    for (uint32_t i = 0; i < ntable; i++) {
        const usb_reg_desc_t *r = &table[i];
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

    VPRINTF(LOW, "=================\nMCU: USB dev0/dev1/hub register RW test\n=================\n\n");

    // Standard MCU boot sequence. This is a standalone register-access test, so
    // no USB core bring-up and no USB traffic is generated; the controllers
    // stay quiescent and we can safely randomize their configuration registers.
    //
    // No usb_hub_init_and_connect() either: the hub register words must be
    // walked while hub_write_lock is DEASSERTED, which is exactly the
    // post-reset state (HUB_EN and HUB_DCON both 0). The walk also leaves both
    // of those bits untouched (ACC_SKIP), so the lock never engages.
    boot_mcu();

    // Phase 1: verify the post-reset values of all three banks BEFORE any
    // write disturbs them. The hub bank is read first-to-last in the same way,
    // using its own three-register table.
    error_count += check_reset_values(SOC_USB_COMBO_DEV0_CSR_BASE_ADDR, "DEV0",
                                      usb_reg_table, USB_REG_TABLE_LEN);
    error_count += check_reset_values(SOC_USB_DEV1_CSR_BASE_ADDR, "DEV1",
                                      usb_reg_table, USB_REG_TABLE_LEN);
    error_count += check_reset_values(SOC_USB_COMBO_HUB_BASE_ADDR, "HUB",
                                      usb_hub_reg_table, USB_HUB_REG_TABLE_LEN);

    // Phase 2: exercise the RW/RO access classes. The two device banks share
    // one table; the hub bank has its own.
    error_count += check_reg_bank(SOC_USB_COMBO_DEV0_CSR_BASE_ADDR, "DEV0",
                                  usb_reg_table, USB_REG_TABLE_LEN);
    error_count += check_reg_bank(SOC_USB_DEV1_CSR_BASE_ADDR, "DEV1",
                                  usb_reg_table, USB_REG_TABLE_LEN);
    error_count += check_reg_bank(SOC_USB_COMBO_HUB_BASE_ADDR, "HUB",
                                  usb_hub_reg_table, USB_HUB_REG_TABLE_LEN);


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
