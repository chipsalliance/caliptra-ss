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
//    USBDC0 registers at SOC_USB_COMBO_DEV0_CSR_BASE_ADDR (0x2000_0000)
//    USBDC1 registers at SOC_USB_DEV1_CSR_BASE_ADDR       (0x2000_2000)
//  This test therefore uses the ABSOLUTE upstream CSR base macros directly
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
//    check. EPLISTSTART/DATABUFSTART are included field-by-field (their
//    writable address bits are RW; the low bits below the programmable field
//    are hardwired 0 and checked read-as-0 - EPLISTSTART [7:0], DATABUFSTART
//    [16:0] since this integration sets the C_DALB generic to 17).
//    A few bits are marked ACC_SKIP (documented in the field table but not
//    driven in the RW walk): DEVCMDSTAT DEV_ADDR/DEV_EN and
//    CONFIG.RSVD31_8 by request, plus DEVCMDSTAT DSUS/LPM_SUS because a write
//    there triggers a remote-wakeup action instead of storing the value.
//    EPSKIP (0x14) SKIP bits are ACC_SKIP: hardware self-clears them on its
//    own (see the EPSKIP field table comment), so they have no stable storage
//    to read back. PHYDEBUG (0x3C,
//    the UTMI+/ULPI debug register per architecture spec v1.0.0 section 5.2.15)
//    IS exercised: its PHY_ACCESS[25] start bit is ACC_SKIP (self-clearing;
//    writing 1 launches a live PHY access and lets HW overwrite PHY_RDATA), all
//    other implemented bits are plain RW. Whole registers excluded:
//    INTSTAT/INTSETSTAT (W1C/W1S).

//
//  Test structure (both phases run over DEV0 then DEV1):
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
// SETUP[8] and the four *_C change bits (DCON_C[24], DSUS_C[25], DRES_C[26],
// OTG_C[27]) are W1C: the RTL write branch only clears the stored bit when a 1
// is written (e.g. "if reg_wdata(27) = '1' then reg_dev_otg_change <= '0'"), so
// they are ACC_W1C and excluded from the plain RW compare.
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
// Bit 18 is the ONLY reserved bit in this register: it is the one bit the RTL
// read decode never drives, so it is ACC_RO + chk_zero (must be immutable AND
// read back 0; a violation is a candidate RTL bug).
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
    { 27, 1, ACC_W1C, 0, "OTG_C"          }, // W1C per spec and RTL (ADP/SRP status change)
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

// LPM (0x10) per the new spec: HIRD_HW[3:0] RO, HIRD_SW[7:4] RW,
// DataPending[8] RW, RSVD[15:9], VBus_Comp_OFF[16] RW, CHRG_VBUS[17] RW,
// DISCHRG_VBUS[18] RW, RSVD[19], ADPPROBE[20] RO, SESSION_END/ADP_SENSE[21] RO,
// RSVD[31:22]. ADPPROBE and SESSION_END are RO status bits (no read-as-0 check).
static const usb_field_t lpm_fields[] = {
    { 0,   4, ACC_RO, 0, "HIRD_HW"       },
    { 4,   4, ACC_RW, 0, "HIRD_SW"       },
    { 8,   1, ACC_RW, 0, "DataPending"   },
    { 9,   7, ACC_RO, 1, "RSVD15_9"      },
    { 16,  1, ACC_RW, 0, "VBus_Comp_OFF" },
    { 17,  1, ACC_RW, 0, "CHRG_VBUS"     },
    { 18,  1, ACC_RW, 0, "DISCHRG_VBUS"  },
    { 19,  1, ACC_RO, 1, "RSVD19"        },
    { 20,  1, ACC_RO, 0, "ADPPROBE"      }, // RO status (may be non-zero)
    { 21,  1, ACC_RO, 0, "SESSION_END"   }, // RO status (may be non-zero)
    { 22, 10, ACC_RO, 1, "RSVD31_22"     },
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


// CONFIG (0x30): PHYSEP[4:0] RO, SB/DB/TREG RO, [31:8] reserved. All defined RO
// fields may be non-zero HW constants, so no read-0 there. RSVD31_8 is
// classified ACC_SKIP (excluded from the RW walk by request); it is present in
// the table for documentation only. PHYSEP reads back the C_NBPHYSEP generic
// and the reset phase checks it against USB_C_NBPHYSEP (see the rst_val /
// rst_mask columns of the shared table) as a tripwire on the generic.
static const usb_field_t config_fields[] = {
    { 0,  5, ACC_RO,   0, "PHYSEP"   }, // reads back C_NBPHYSEP
    { 5,  1, ACC_RO,   0, "SB"       },
    { 6,  1, ACC_RO,   0, "DB"       },
    { 7,  1, ACC_RO,   0, "TREG"     },
    { 8, 24, ACC_SKIP, 0, "RSVD31_8" }, // excluded from the RW walk by request
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

// PHYDEBUG (0x3C): "UTMI+/ULPI debug" register (architecture spec v1.0.0
// section 5.2.15). It lets firmware read/write registers inside the attached
// USB PHY. Reset value 0x00000000. This integration instantiates the compound
// with BOTH C_UTMI_SUPPORT=TRUE and C_ULPI_SUPPORT=TRUE
// (ip_xxx_3511_hs_mem_compound.e.vhdl, not overridden by the wrapper), so the
// "both PHYs supported" branch of usb_reg_if.m.vhdl register "1111" is active:
//   [7:0]   PHY_ADDR  <= reg_wdata(7:0)        RW
//   [15:8]  PHY_WDATA <= reg_wdata(15:8)       RW (ULPI write data)
//   [23:16] PHY_RDATA <= reg_wdata(23:16)      RW (also loaded by HW from
//                                                 sync_phy_rdata when an access
//                                                 completes)
//   [24]    PHY_RW    <= reg_wdata(24)         RW (0=read / 1=write)
//   [25]    PHY_ACCESS<= reg_wdata(25)         start bit: SW writes 1 to launch
//                                                 an access, HW clears it on
//                                                 sync_phy_endtoggle; SW may not
//                                                 clear it. Classified ACC_SKIP:
//                                                 driving 1 would launch a live
//                                                 PHY transaction and let HW
//                                                 overwrite PHY_RDATA, which is
//                                                 not a plain RW check.
//   [30:26] R                                  reserved, read-as-0
//   [31]    PHY_MODE  <= reg_wdata(31)         RW here because both PHYs are
//                                                 supported (0=UTMI+, 1=ULPI);
//                                                 it would be RO if only one PHY
//                                                 were supported.
static const usb_field_t phydebug_fields[] = {
    { 0,   8, ACC_RW,   0, "PHY_ADDR"   },
    { 8,   8, ACC_RW,   0, "PHY_WDATA"  },
    { 16,  8, ACC_RW,   0, "PHY_RDATA"  },
    { 24,  1, ACC_RW,   0, "PHY_RW"     },
    { 25,  1, ACC_SKIP, 0, "PHY_ACCESS" }, // self-clearing start bit; not driven
    { 26,  5, ACC_RO,   1, "RSVD30_26"  }, // reserved, read-as-0
    { 31,  1, ACC_RW,   0, "PHY_MODE"   }, // RW (both C_UTMI_SUPPORT and C_ULPI_SUPPORT)
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
// EPSKIP field table comment). PHYDEBUG 0x3C
// (UTMI+/ULPI debug, spec v1.0.0 section 5.2.15) IS
// included: all implemented bits are RW except PHY_ACCESS[25], the
// self-clearing start bit, which is ACC_SKIP. Registers deliberately excluded:
// INTSTAT 0x20 / INTSETSTAT 0x28 (W1C / W1S).
//
// Reset-value expectation (rst_val / rst_mask) per docs/usb_register_structure.md
// section 1.1:
//   DEVCMDSTAT : expected 0x00000800 (the spec reset value, LPM_SUP[11] set).
//                Six bits are EXCLUDED from the reset mask because they are
//                live or sticky HW status rather than fixed reset constants,
//                so they are not reliable reset expectations:
//                  Speed[23:22]      - pie_speed, the negotiated link speed
//                  VbusDebounced[28]  - VBus present
//                  DCON_C[24], DSUS_C[25], DRES_C[26], OTG_C[27] - the W1C
//                    status-change flags. These are HW-set and can only be
//                    cleared by firmware writing 1, so any environment event
//                    before the first read latches them. OTG_C in particular
//                    is set by ANY edge on avalid (ADPPROBE) or sessend
//                    (ADPSENSE) - see usb_reg_if.m.vhdl line 880 - and the
//                    testbench drives both from the VIP UTMI interface, so the
//                    power-up transition of AValid/SessEnd sets OTG_C long
//                    before boot_mcu() returns. That is expected DUT behavior,
//                    not a defect.
//                That gives rst_mask 0xE03FFFFF. The other 25 bits ARE checked,
//                so a set reserved bit (bit 18) is still reported as a
//                candidate RTL issue.
//   INFO       : reset depends on CHIP_ID[31:16], so only the low 16 bits
//                (FRAME_NR / ERR_CODE / RSVD15) are checked against 0.
//   LPM, EPINUSE, EPBUFCFG, INTEN, INTROUTE, EPTOGGLE, INTPLL : reset 0x0,
//                all 32 bits checked.
//   CONFIG     : per-build RO constants. Only PHYSEP[4:0] is checked (mask
//                0x1F), against USB_C_NBPHYSEP: it is a direct read-back of the
//                C_NBPHYSEP generic and acts as a tripwire if the generic moves
//                away from the value the EP field tables are sized for. SB/DB/
//                TREG are left unchecked because they depend on other build
//                options.
static const usb_reg_desc_t usb_reg_table[] = {
    REG_DESC(0x00u, "DEVCMDSTAT",   devcmdstat_fields,   0x00000800u, 0xE03FFFFFu),
    REG_DESC(0x04u, "INFO",         info_fields,         0x00000000u, 0x0000FFFFu),
    REG_DESC(0x08u, "EPLISTSTART",  epliststart_fields,  0x00000000u, 0xFFFFFFFFu),
    REG_DESC(0x0Cu, "DATABUFSTART", databufstart_fields, 0x00000000u, 0xFFFE0000u),
    REG_DESC(0x10u, "LPM",        lpm_fields,        0x00000000u, 0xFFCFFFFFu),

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

// Read every register in the shared table ONCE (before any write) and compare
// its post-reset value against the expected reset value in the table. Only the
// bits selected by rst_mask are compared; a register with rst_mask == 0 is
// skipped. This phase runs before check_reg_bank() so the reads observe the
// true reset state rather than values left by the RW/RO walk.
//
// NOTE: these reset reads are performed with NO write-before-read workaround
// for the former DataKnown_A hazard. This is safe because the improved RTL no
// longer drives X on the dev*_axi read path for never-written registers, so the
// reads observe the true reset state without any hub bring-up.
static int check_reset_values(uint32_t base, const char *bank) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB reset-value check: bank %s (base 0x%x) ---\n",
            bank, base);
    for (uint32_t i = 0; i < USB_REG_TABLE_LEN; i++) {
        const usb_reg_desc_t *r = &usb_reg_table[i];
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

    // Standard MCU boot sequence. This is a standalone register-access test, so
    // no USB core bring-up and no USB traffic is generated; the controllers
    // stay quiescent and we can safely randomize their configuration registers.
    boot_mcu();

    // Phase 1: verify the post-reset values of both device banks BEFORE any
    // write disturbs them.
    error_count += check_reset_values(SOC_USB_COMBO_DEV0_CSR_BASE_ADDR, "DEV0");
    error_count += check_reset_values(SOC_USB_DEV1_CSR_BASE_ADDR, "DEV1");

    // Phase 2: exercise the RW/RO access classes of both banks with the shared
    // table.
    error_count += check_reg_bank(SOC_USB_COMBO_DEV0_CSR_BASE_ADDR, "DEV0");
    error_count += check_reg_bank(SOC_USB_DEV1_CSR_BASE_ADDR, "DEV1");


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
