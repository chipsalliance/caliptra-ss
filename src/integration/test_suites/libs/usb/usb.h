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

#ifndef USB_DRV_H
#define USB_DRV_H

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "stdint.h"
#include <stdbool.h>

// -------------------------------------------------------------------------
// USB Hub composite IP (ip_xxx_3511_hs_mem_compound_wrapper) entity address
// map.
//
// The composite wrapper exposes three independent AXI subordinate ports:
//   hub_axi  - HUB control/status registers (2 regs) + HUB RAM
//   dev0_axi - USBDC0 registers (MCU-owned device controller)
//   dev1_axi - USBDC1 registers (SoC-uC-owned device controller)
//
// Per the NIC400 address map (see asib_cptra_ss_mcu_lsu_m0.xml), from the
// MCU LSU master:
//   cptra_usb_host_s5   (0x2000_1000 - 0x2000_1FFF) -> dev0_axi (MCU-owned)
//   cptra_usb_device_s6 (0x2000_0000 - 0x2000_0FFF) -> hub_axi
//   cptra_usb_dma_s7    (0x2001_0000 - 0x2001_FFFF) -> dev1_axi (SoC-uC-owned)
//
// The legacy SOC_USBHSD_*/SOC_USBHSH_* macros in soc_address_map.h were
// generated for the previous single-device USB IP and do NOT reflect this
// new entity mapping:
//   - SOC_USBHSD_* (base 0x2000_0000) lands on the HUB's 2-register bank,
//     not on a full USBDC register bank.
//   - SOC_USBHSH_* (base 0x2000_1000) was generated with legacy EHCI-style
//     host register names (CAPLENGTH_CHIPID, HCSPARAMS, USBCMD, PORTSC1,
//     etc.) and does not match the USBDC register layout either, even
//     though 0x2000_1000 is the address range that now correctly reaches
//     the MCU's own USBDC0 device controller (dev0_axi) per the NIC map.
//
// USB_DEV0_REG_BASE_ADDR below is therefore the correct base address for
// the MCU-owned USBDC0 register bank. The wrapper splits each entity's
// AXI aperture into a register region (offset < DEV0_REG_ADDR_TOP) and a
// DMA/SRAM region (offset >= DEV0_REG_ADDR_TOP); DEV0_REG_ADDR_TOP is
// currently 0x100 (see ip_xxx_3511_hs_mem_compound_wrapper.sv, pending
// USB2-PRG-001), so USB_DEV0_DMA_BASE_ADDR is set to
// USB_DEV0_REG_BASE_ADDR + 0x100. This still fits comfortably within the
// 4KB s5 NIC window (0x2000_1000-0x2000_1FFF).
// -------------------------------------------------------------------------
#define USB_DEV0_REG_BASE_ADDR       0x20001000u
#define USB_DEV0_DMA_BASE_ADDR       0x20001100u

// -------------------------------------------------------------------------
// USBDC1 (dev1_axi) base addresses.
//
// dev1_axi is the second embedded device controller of the compound IP. It
// maps to the NIC400 slave port cptra_usb_dma_s7 (0x2001_0000 -
// 0x2001_FFFF). The MCU LSU master decodes this window (see
// nic400_asib_cptra_ss_mcu_lsu_m0_decode_cptra_64.v: decode_int[12] covers
// 0x2001_0000..0x2001_FFFF), and caliptra_ss_top.sv wires dev1_axi fully,
// so MCU test firmware can drive USBDC1 with no RTL change. The
// "SoC-uC-owned" wording above is a fabric access-control policy statement,
// not a hardware restriction of this testbench.
//
// The wrapper splits the dev1 aperture the same way as dev0, with
// DEV1_REG_ADDR_TOP = 0x100 (ip_xxx_3511_hs_mem_compound_wrapper.sv), so
// the dev1 register bank sits at 0x2001_0000 and the dev1 DMA/SRAM region
// at 0x2001_0100 - a structural mirror of dev0.
//
// CAVEAT: some host-side tests reuse 0x2001_0000 as scratch PTD/SRAM space
// (for example caliptra_ss_usb_hs_host_bulk_out.c). Those host tests and
// the dev1 device tests therefore must not be run against this window at
// the same time within one test.
// -------------------------------------------------------------------------
#define USB_DEV1_REG_BASE_ADDR       0x20010000u
#define USB_DEV1_DMA_BASE_ADDR       0x20010100u

// -------------------------------------------------------------------------
// Device selection for the shared USB test library.
//
// usb.c is compiled per test into that test's own build directory, so the
// device under test is selected at compile time with -DUSB_DEV_SEL=<0|1>
// passed through BUILD_CFLAGS from the test yml, e.g.
//   BUILD_CFLAGS="-DUSB_DEV_SEL=1"
// Default is 0 (USBDC0) so every pre-existing test keeps its behaviour
// without any yml change.
//
// All library code and all device-agnostic test code must use the neutral
// USB_DEV_* macros below. The absolute USB_DEV0_*/USB_DEV1_* macros remain
// available for code that must address one specific controller regardless
// of the selection.
// -------------------------------------------------------------------------
#ifndef USB_DEV_SEL
#define USB_DEV_SEL 0
#endif

#if (USB_DEV_SEL == 1)
#define USB_DEV_REG_BASE_ADDR        USB_DEV1_REG_BASE_ADDR
#define USB_DEV_DMA_BASE_ADDR        USB_DEV1_DMA_BASE_ADDR
#elif (USB_DEV_SEL == 0)
#define USB_DEV_REG_BASE_ADDR        USB_DEV0_REG_BASE_ADDR
#define USB_DEV_DMA_BASE_ADDR        USB_DEV0_DMA_BASE_ADDR
#else
#error "USB_DEV_SEL must be 0 (USBDC0) or 1 (USBDC1)"
#endif


// -------------------------------------------------------------------------
// HUB control/status register (hub_axi aperture).
//
// hub_axi maps to cptra_usb_device_s6 (0x2000_0000 - 0x2000_0FFF).
//
// IMPORTANT - descriptor store migration (IP branch usb_hub_ram):
// The hub descriptor store used to be an external 64-bit SRAM reached
// through a dedicated descriptor DMA AHB port, which firmware had to
// program (descriptors + SETUP-match table + dev-link pointer) before
// enabling the hub. That whole path no longer exists. The descriptor
// store is now an internal flip-flop array inside the compound IP that
// self-initializes from a ROM constant at reset, so firmware has nothing
// to program: the only firmware action left is the two-phase enable of
// the hub control register below.
//
// Consequently every USB_HUB_RAM_* offset macro and every SETUP-match
// entry field macro that used to live here has been removed. The hub
// status register was never implemented and is removed as well.
//
// The hub control/status register is word 15 of the hub register file
// (C_HUB_CS), i.e. AHB byte offset 0x3C in the hub aperture:
//   bit  0 = HUB_EN       (structural mux select; hub entity enabled and
//                          presents USBDC0/USBDC1 as embedded downstream
//                          devices)
//   bit 16 = HUB_CONNECT  (hub connects to the upstream port, ANDed with
//                          VBus valid inside the IP)
//
// HUB_EN bit position: the RTL samples bit 0, but the IP's own reference
// BFM still writes bit 7 (its legacy position). Until the IP owner
// confirms which is authoritative, USBHUB_CTRL_HUB_EN_MASK sets BOTH
// bits so the sequence works either way. Bit 7 is a don't-care for the
// current RTL.
//
// Note also that the IP asserts hub_write_lock once HUB_EN and
// HUB_CONNECT are both set, and word 15 is itself inside the locked
// array, so firmware cannot clear HUB_CONNECT afterwards. The only
// disconnect stimulus available is VBus removal.
// -------------------------------------------------------------------------
#define USB_HUB_REG_BASE_ADDR        0x20000000u
#define USB_HUB_CTRL                 (USB_HUB_REG_BASE_ADDR + 0x03Cu)

#define USBHUB_CTRL_HUB_EN_MASK      ((1u << 0) | (1u << 7))
#define USBHUB_CTRL_HUB_CONNECT_MASK (1u << 16)

// -------------------------------------------------------------------------
// Hub DEVICE descriptor override (DataPhase_Buffer_0 of the hub_axi aperture).
//
// The hub descriptor store is an internal flip-flop array that self-inits
// from a ROM constant at reset (see docs/usb_hub_ram_to_flipflop_migration.md
// and claude_md/19_hub_descriptor_write_map.md). It is still writable through
// the hub_axi aperture as long as the write-lock is not yet asserted. The
// lock (hub_write_lock <= ep0_mem(15)(0) and ep0_mem(15)(16)) engages only
// once BOTH HUB_EN (bit 0) AND HUB_CONNECT (bit 16) are set, so any descriptor
// override MUST be written before usb_hub_connect() - HUB_EN alone does not
// lock the array.
//
// The 18-byte device descriptor is packed 32-bit LSB-first in
// DataPhase_Buffer_0 (base 0x2000_0000):
//   word2 @ 0x08 = idVendor  | idProduct<<16
//   word3 @ 0x0C = bcdDevice | iManufacturer<<16 | iProduct<<24
//   word4 @ 0x10 = iSerialNumber(byte0) | bNumConfigurations(byte1)<<8 | ...
// word2 and word3 are clean full-word fields (no neighbor clobber). word4
// shares its low byte (iSerialNumber) with bNumConfigurations and trailing
// buffer bytes, so iSerialNumber must be changed with a read-modify-write of
// only the low byte.
//
// These override the ROM defaults (idProduct 0xBE00, bcdDevice 0x0100,
// iManufacturer 0x00, iProduct 0x00, iSerialNumber 0x00) to non-default
// values so a scoreboard can confirm the firmware override took effect.
// idVendor is kept at 0x1FC9 and bNumConfigurations at 0x01.
// -------------------------------------------------------------------------
#define USB_HUB_DESC_DEVICE_BASE     (USB_HUB_REG_BASE_ADDR + 0x000u)
#define USB_HUB_DESC_DEV_WORD2       (USB_HUB_DESC_DEVICE_BASE + 0x08u)
#define USB_HUB_DESC_DEV_WORD3       (USB_HUB_DESC_DEVICE_BASE + 0x0Cu)
#define USB_HUB_DESC_DEV_WORD4       (USB_HUB_DESC_DEVICE_BASE + 0x10u)
#define USB_HUB_DESC_DEV_WORD2_VAL   0xBE011FC9u
#define USB_HUB_DESC_DEV_WORD3_VAL   0x02010200u
#define USB_HUB_DESC_DEV_ISERIAL_VAL 0x03u

// -------------------------------------------------------------------------
// Hub DEVICE QUALIFIER descriptor override (DataPhase_Buffer_3 of the
// hub_axi aperture, base 0x2000_00C0).
//
// Same write-lock rule as the DEVICE descriptor above: the qualifier lives
// in the same flip-flop array, so any override MUST be written before
// usb_hub_connect() while the array is still unlocked.
//
// The 10-byte device qualifier is packed 32-bit LSB-first in
// DataPhase_Buffer_3 (base 0x2000_00C0):
//   qw0 @ 0xC0 = bLength(0x0A) | bDescriptorType(0x06)<<8 | bcdUSB<<16
//   qw1 @ 0xC4 = bDeviceClass | bDeviceSubClass<<8 | bDeviceProtocol<<16
//                | bMaxPacketSize0<<24
//   qw2 @ 0xC8 = bNumConfigurations | bReserved<<8 | ...
// qw1 is a clean full word (all four of its bytes are qualifier fields), so
// it is written whole with no neighbor clobber. qw0 and qw2 share bytes with
// bLength/type/bcdUSB and bNumConfigurations/reserved, so they are left at
// the ROM defaults.
//
// This overrides the ROM defaults bDeviceSubClass 0x00 -> 0x02,
// bDeviceProtocol 0x00 -> 0x01, and bMaxPacketSize0 0x40 -> 0x08, keeping
// bDeviceClass at 0x00. bMaxPacketSize0 here reports the EP0 max packet size
// for the OTHER operating speed (USB 2.0 section 9.6.2), not the live control
// endpoint, so changing it does not disturb the negotiated EP0 size from the
// DEVICE descriptor; 0x08 is a spec-legal EP0 size. The override lets the
// scoreboard confirm the firmware write took effect.
// -------------------------------------------------------------------------
#define USB_HUB_DESC_QUAL_BASE       (USB_HUB_REG_BASE_ADDR + 0x0C0u)
#define USB_HUB_DESC_QUAL_WORD1      (USB_HUB_DESC_QUAL_BASE + 0x04u)
#define USB_HUB_DESC_QUAL_WORD1_VAL  0x08010200u

// -------------------------------------------------------------------------
// Hub CONFIGURATION and OTHER_SPEED_CONFIGURATION descriptor override.
//
// The CONFIGURATION descriptor is DataPhase_Buffer_1 (base 0x2000_0040) and
// the OTHER_SPEED_CONFIGURATION descriptor is at base 0x2000_0100. Both live
// in the same flip-flop array as the DEVICE descriptor, so the same write-lock
// rule applies: any override MUST be written before usb_hub_connect() while
// the array is still unlocked. All 172 hub descriptor words are reachable on
// the hub_axi port (the AHB slave address width is log2(172)=8 bits, i.e.
// haddr[9:2]); the 0x100 aperture cap documented for USBDC0/USBDC1 does NOT
// apply to the hub port.
//
// Both descriptors share the identical 9-byte header layout (USB 2.0 sections
// 9.6.3 / 9.6.4), packed 32-bit LSB-first from their base:
//   word0 @ +0x00 = bLength(0x09) | bDescriptorType<<8 | wTotalLength<<16
//   word1 @ +0x04 = bNumInterfaces | bConfigurationValue<<8 | iConfiguration<<16
//                   | bmAttributes<<24
//   word2 @ +0x08 = bMaxPower | interface-descriptor bytes...
// The only informational, safely-overridable header field is iConfiguration,
// which is byte 2 of word1. word1 also holds bmAttributes (byte 3, whose
// runtime self-powered bit must be preserved), so iConfiguration is changed
// with a read-modify-write of only that byte. bMaxPower is deliberately left
// at the RTL default (0xFA in the current ROM). Per USB 2.0 section 9.6.4 the
// OTHER_SPEED_CONFIGURATION fields mirror the CONFIGURATION descriptor, so the
// same iConfiguration value is written to both.
// -------------------------------------------------------------------------
#define USB_HUB_DESC_CFG_BASE        (USB_HUB_REG_BASE_ADDR + 0x040u)
#define USB_HUB_DESC_CFG_WORD1       (USB_HUB_DESC_CFG_BASE + 0x04u)
#define USB_HUB_DESC_OSC_BASE        (USB_HUB_REG_BASE_ADDR + 0x100u)
#define USB_HUB_DESC_OSC_WORD1       (USB_HUB_DESC_OSC_BASE + 0x04u)
#define USB_HUB_DESC_ICONFIG_VAL     0x04u

// Hub CLASS descriptor override (DataPhase_Buffer_2, base 0x080). Word1 @ 0x84
// packs wHubCharacteristics.hi | bPwrOn2PwrGood<<8 | bHubContrCurrent<<16 |
// DeviceRemovable<<24 - all four bytes are hub-descriptor fields, so it is a
// clean full-word override (no structural bLength/bDescriptorType/bNbrPorts or
// wHubCharacteristics.lo clobber, those live in word0 @ 0x80). Override values:
// wHubCharacteristics.hi 0x00 (kept), bPwrOn2PwrGood 0x00 -> 0x32 (100 ms),
// bHubContrCurrent 0x00 -> 0x64 (100 mA), DeviceRemovable 0x06 -> 0x0A.
#define USB_HUB_DESC_HUB_BASE        (USB_HUB_REG_BASE_ADDR + 0x080u)
#define USB_HUB_DESC_HUB_WORD1       (USB_HUB_DESC_HUB_BASE + 0x04u)
#define USB_HUB_DESC_HUB_WORD1_VAL   0x0A643200u


// NOTE: the former USB_HUB_RAM_* layout offsets, the SETUP-match table
// dword-address / descriptor-slot-base helpers, and the SETUP-match entry
// field byte offsets used to live here. They all described the external
// descriptor SRAM that firmware had to program, which no longer exists
// (see the migration note above), so they have been deleted rather than
// re-derived: the internal ROM constant owns that layout now and its
// byte offsets differ from the previous firmware-chosen ones.

// USBDC0 register offsets from USB_DEV0_REG_BASE_ADDR (same 16-register
// layout as the legacy SOC_USBHSD_* bank; the *_MASK/*_SHIFT bitfield
// macros from soc_address_map.h are offset-independent and remain valid).
#define USB_DEV0_DEVCMDSTAT   (USB_DEV0_REG_BASE_ADDR + 0x00u)
#define USB_DEV0_INFO         (USB_DEV0_REG_BASE_ADDR + 0x04u)
#define USB_DEV0_EPLISTSTART  (USB_DEV0_REG_BASE_ADDR + 0x08u)
#define USB_DEV0_DATABUFSTART (USB_DEV0_REG_BASE_ADDR + 0x0cu)
#define USB_DEV0_LPM          (USB_DEV0_REG_BASE_ADDR + 0x10u)
#define USB_DEV0_EPSKIP       (USB_DEV0_REG_BASE_ADDR + 0x14u)
#define USB_DEV0_EPINUSE      (USB_DEV0_REG_BASE_ADDR + 0x18u)
#define USB_DEV0_EPBUFCFG     (USB_DEV0_REG_BASE_ADDR + 0x1cu)
#define USB_DEV0_INTSTAT      (USB_DEV0_REG_BASE_ADDR + 0x20u)
#define USB_DEV0_INTEN        (USB_DEV0_REG_BASE_ADDR + 0x24u)
#define USB_DEV0_INTSETSTAT   (USB_DEV0_REG_BASE_ADDR + 0x28u)
#define USB_DEV0_EPTOGGLE     (USB_DEV0_REG_BASE_ADDR + 0x34u)
#define USB_DEV0_ULPIDEBUG    (USB_DEV0_REG_BASE_ADDR + 0x3cu)

// USBDC1 register offsets from USB_DEV1_REG_BASE_ADDR. The register layout
// is identical to USBDC0 - only the aperture base differs.
#define USB_DEV1_DEVCMDSTAT   (USB_DEV1_REG_BASE_ADDR + 0x00u)
#define USB_DEV1_INFO         (USB_DEV1_REG_BASE_ADDR + 0x04u)
#define USB_DEV1_EPLISTSTART  (USB_DEV1_REG_BASE_ADDR + 0x08u)
#define USB_DEV1_DATABUFSTART (USB_DEV1_REG_BASE_ADDR + 0x0cu)
#define USB_DEV1_LPM          (USB_DEV1_REG_BASE_ADDR + 0x10u)
#define USB_DEV1_EPSKIP       (USB_DEV1_REG_BASE_ADDR + 0x14u)
#define USB_DEV1_EPINUSE      (USB_DEV1_REG_BASE_ADDR + 0x18u)
#define USB_DEV1_EPBUFCFG     (USB_DEV1_REG_BASE_ADDR + 0x1cu)
#define USB_DEV1_INTSTAT      (USB_DEV1_REG_BASE_ADDR + 0x20u)
#define USB_DEV1_INTEN        (USB_DEV1_REG_BASE_ADDR + 0x24u)
#define USB_DEV1_INTSETSTAT   (USB_DEV1_REG_BASE_ADDR + 0x28u)
#define USB_DEV1_EPTOGGLE     (USB_DEV1_REG_BASE_ADDR + 0x34u)
#define USB_DEV1_ULPIDEBUG    (USB_DEV1_REG_BASE_ADDR + 0x3cu)

// Device-neutral register macros. These resolve to the USBDC selected by
// USB_DEV_SEL and are what the shared library (usb.c) and all replicated
// test firmware use.
#define USB_DEV_DEVCMDSTAT    (USB_DEV_REG_BASE_ADDR + 0x00u)
#define USB_DEV_INFO          (USB_DEV_REG_BASE_ADDR + 0x04u)
#define USB_DEV_EPLISTSTART   (USB_DEV_REG_BASE_ADDR + 0x08u)
#define USB_DEV_DATABUFSTART  (USB_DEV_REG_BASE_ADDR + 0x0cu)
#define USB_DEV_LPM           (USB_DEV_REG_BASE_ADDR + 0x10u)
#define USB_DEV_EPSKIP        (USB_DEV_REG_BASE_ADDR + 0x14u)
#define USB_DEV_EPINUSE       (USB_DEV_REG_BASE_ADDR + 0x18u)
#define USB_DEV_EPBUFCFG      (USB_DEV_REG_BASE_ADDR + 0x1cu)
#define USB_DEV_INTSTAT       (USB_DEV_REG_BASE_ADDR + 0x20u)
#define USB_DEV_INTEN         (USB_DEV_REG_BASE_ADDR + 0x24u)
#define USB_DEV_INTSETSTAT    (USB_DEV_REG_BASE_ADDR + 0x28u)
#define USB_DEV_EPTOGGLE      (USB_DEV_REG_BASE_ADDR + 0x34u)
#define USB_DEV_ULPIDEBUG     (USB_DEV_REG_BASE_ADDR + 0x3cu)


// -------------------------------------------------------------------------
// DMA slave base address and SRAM buffer layout constants.
// These are not RDL-specified and therefore not present in any generated
// header. USB_DMA_BASE_ADDR is kept as an alias of USB_DEV0_DMA_BASE_ADDR
// for source compatibility with existing test firmware; new code should
// prefer USB_DEV0_DMA_BASE_ADDR directly.
// -------------------------------------------------------------------------
#define USB_DMA_BASE_ADDR            USB_DEV0_DMA_BASE_ADDR

#define USB_SRAM_EP_LIST_OFFSET      0x000u
#define USB_SRAM_SETUP_BUF_OFFSET    0x100u
#define USB_SRAM_EP0_OUT_BUF_OFFSET  0x140u
#define USB_SRAM_EP0_IN_BUF_OFFSET   0x180u

// EP command/status list entry bit fields (from RTL usb_dma.m.vhdl line 420:
//   "epinfo_nbytes <= dma_rdata(25 downto 11);" and line 421:
//   "epinfo_addr_offset <= dma_rdata(C_DALB-7 downto 0);" with C_DALB=17
//   in our integration → addr_offset at bits [10:0]).
//   [31]    = Active
//   [29]    = Stall
//   [25:11] = NBytes (15-bit transfer length)
//   [10:0]  = AddrOffset (buffer byte address >> 6)
#define USB_EP_ENTRY_ACTIVE       (1u << 31)
#define USB_EP_ENTRY_DISABLED     (1u << 30)
#define USB_EP_ENTRY_STALL        (1u << 29)
// T bit (bit 26) - Endpoint Type:
//   0 = Generic (bulk / rate-feedback interrupt)
//   1 = Periodic. The RF bit then selects isochronous vs interrupt.
// RF bit (bit 27) - Rate Feedback / Toggle Value:
//   When T=1: 0 = Isochronous (max packet <= 1024 bytes in HS)
//             1 = Interrupt
// To arm an isochronous endpoint set USB_EP_ENTRY_TYPE_PERIODIC and
// leave USB_EP_ENTRY_RF_ISO (0) - i.e. do not set the RF bit.
// Without T=1 the hardware treats the EP as generic (bulk) and sends
// ACK/NAK handshakes, which is wrong for isochronous per USB 2.0 spec
// and the NXP IP Integration Guide (section 4.2.3).
#define USB_EP_ENTRY_TYPE_PERIODIC (1u << 26)
#define USB_EP_ENTRY_RF_ISO        (0u)
#define USB_EP_ENTRY_RF_INT        (1u << 27)
#define USB_EP_ENTRY_NBYTES(n)    (((uint32_t)(n) & 0x7FFFu) << 11)
// USB_EP_ENTRY_ADDR(off) - legacy macro that takes a raw offset value >> 6.
// NOTE: use USB_EP_ENTRY_ABS_ADDR(abs) instead for all data-buffer EP entries.
// See USB_EP_ENTRY_ABS_ADDR below.
#define USB_EP_ENTRY_ADDR(off)    (((uint32_t)(off) >> 6) & 0x7FFu)
// USB_EP_ENTRY_ABS_ADDR(abs_addr) - computes the AddrOffset field [10:0] of
// an EP command/status list entry from the ABSOLUTE AXI byte address of the
// data buffer. This is the correct formula for this design:
//   DATABUFSTART only contributes bits[31:22] to the DMA address (C_DALB=22).
//   The DMA engine reconstructs the buffer address as:
//     {DATABUFSTART[31:22], addr_offset[10:0], word[3:0], 2'b00}
//   so addr_offset must equal bits[16:6] of the absolute AXI buffer address.
//   Passing (USB_DEV0_DMA_BASE_ADDR + SRAM_offset) gives the correct result:
//     e.g. SETUP buf: (0x20001100+0x100)>>6 & 0x7FF = 0x20001200>>6 & 0x7FF
//                   = 0x800048 & 0x7FF = 0x048
//   This makes the DMA-written address 0x20000000|(0x48<<6)=0x20001200 match
//   the MCU's AXI read address 0x20001200, so SRAM word indices agree.
#define USB_EP_ENTRY_ABS_ADDR(abs_addr) (((uint32_t)(abs_addr) >> 6) & 0x7FFu)

// -------------------------------------------------------------------------
// USB 2.0 standard request codes (bRequest field of SETUP packet)
// -------------------------------------------------------------------------
#define USB_REQ_GET_STATUS          0x00u
#define USB_REQ_CLEAR_FEATURE       0x01u
#define USB_REQ_SET_FEATURE         0x03u
#define USB_REQ_SET_ADDRESS         0x05u
#define USB_REQ_GET_DESCRIPTOR      0x06u
#define USB_REQ_SET_DESCRIPTOR      0x07u
#define USB_REQ_GET_CONFIGURATION   0x08u
#define USB_REQ_SET_CONFIGURATION   0x09u
#define USB_REQ_GET_INTERFACE       0x0Au
#define USB_REQ_SET_INTERFACE       0x0Bu
#define USB_REQ_SYNCH_FRAME         0x0Cu

// -------------------------------------------------------------------------
// USB 2.0 standard feature selectors (wValue for SET/CLEAR_FEATURE)
// -------------------------------------------------------------------------
#define USB_FEATURE_ENDPOINT_HALT        0x00u
#define USB_FEATURE_DEVICE_REMOTE_WAKEUP 0x01u
#define USB_FEATURE_TEST_MODE            0x02u

// -------------------------------------------------------------------------
// USB descriptor types (wValue high byte for GET/SET_DESCRIPTOR)
// -------------------------------------------------------------------------

#define USB_DESC_DEVICE                    0x01u
#define USB_DESC_CONFIGURATION             0x02u
#define USB_DESC_STRING                    0x03u
#define USB_DESC_INTERFACE                 0x04u
#define USB_DESC_ENDPOINT                  0x05u
#define USB_DESC_DEVICE_QUALIFIER          0x06u
#define USB_DESC_OTHER_SPEED_CONFIGURATION 0x07u
#define USB_DESC_INTERFACE_POWER           0x08u

// -------------------------------------------------------------------------
// bmRequestType field decode macros
// -------------------------------------------------------------------------
#define USB_BMREQTYPE_DIR(x)       (((uint8_t)(x) >> 7) & 0x1u)
#define USB_BMREQTYPE_TYPE(x)      (((uint8_t)(x) >> 5) & 0x3u)
#define USB_BMREQTYPE_RECIPIENT(x) ((uint8_t)(x) & 0x1Fu)

// Direction (bit 7)
#define USB_DIR_HOST_TO_DEVICE  0u
#define USB_DIR_DEVICE_TO_HOST  1u

// Type (bits [6:5])
#define USB_TYPE_STANDARD  0u
#define USB_TYPE_CLASS     1u
#define USB_TYPE_VENDOR    2u
#define USB_TYPE_RESERVED  3u

// Recipient (bits [4:0])
#define USB_RECIP_DEVICE    0u
#define USB_RECIP_INTERFACE 1u
#define USB_RECIP_ENDPOINT  2u
#define USB_RECIP_OTHER     3u

// -------------------------------------------------------------------------
// Parsed SETUP packet structure
// -------------------------------------------------------------------------
typedef struct {
    uint8_t  bmRequestType;
    uint8_t  bRequest;
    uint16_t wValue;
    uint16_t wIndex;
    uint16_t wLength;
} usb_setup_pkt_t;

// -------------------------------------------------------------------------
// USB 2.0 standard device descriptor (18 bytes, wire layout).
//
// This struct is packed so its byte layout maps 1:1 onto the EP0 IN SRAM
// buffer that the device controller DMA serves to the host on a
// GET_DESCRIPTOR(DEVICE) request. Multi-byte fields (bcdUSB, idVendor,
// idProduct, bcdDevice) are little-endian, matching the USB wire order and
// the RISC-V little-endian byte order, so no swapping is needed when the
// struct is copied word-by-word into SRAM.
// -------------------------------------------------------------------------
typedef struct __attribute__((packed)) {
    uint8_t  bLength;            // Descriptor size in bytes (18)
    uint8_t  bDescriptorType;    // DEVICE descriptor type (1)
    uint16_t bcdUSB;             // USB spec release number (0x0200 = USB 2.0)
    uint8_t  bDeviceClass;       // Class code
    uint8_t  bDeviceSubClass;    // Subclass code
    uint8_t  bDeviceProtocol;    // Protocol code
    uint8_t  bMaxPacketSize0;    // Max packet size for EP0 (64)
    uint16_t idVendor;           // Vendor ID
    uint16_t idProduct;          // Product ID
    uint16_t bcdDevice;          // Device release number
    uint8_t  iManufacturer;      // Index of manufacturer string descriptor
    uint8_t  iProduct;           // Index of product string descriptor
    uint8_t  iSerialNumber;      // Index of serial-number string descriptor
    uint8_t  bNumConfigurations; // Number of possible configurations (1)
} usb_device_descriptor_t;

// Fixed device descriptors for the two embedded controllers. DEV0 and DEV1
// differ in idProduct and bcdDevice so a scoreboard can tell which
// controller answered the host. Defined in usb.c. The controller actually
// served is selected at compile time by USB_DEV_SEL (see
// usb_ep0_send_device_descriptor()).
extern const usb_device_descriptor_t usb_dev0_device_descriptor;
extern const usb_device_descriptor_t usb_dev1_device_descriptor;

// -------------------------------------------------------------------------
// USB driver API
// -------------------------------------------------------------------------

// Initialize the USB device controller: configure the OTG PHY mux, set up
// the EP command/status list and SRAM buffers, enable device mode and
// interrupts.
void boot_usb_core(void);

// Initialize the USB device controller in FS-only mode: identical to
// boot_usb_core() but sets DEVCMDSTAT bit 21 (PFSC) to suppress device-side
// K-chirp. Use in tests with a FS-only host VIP (high_speed_capable=0) so
// the UTMI TX is ready immediately after bus reset instead of waiting ~2.2ms
// for the chirp timeout. Do NOT use when HS operation is required.
void boot_usb_core_fs(void);

// Re-arm EP0 OUT, SETUP, and IN buffer address entries in the EP list.
// Must be called after any bus reset to restore hardware-cleared entries.
void usb_ep0_reinit(void);

// Handle a USB bus reset: if DRES_C is set, clear it (W1C), reinitialize
// EP0, and reset the device address to 0.
void usb_handle_bus_reset(void);

// Read the 8-byte SETUP packet from the SRAM SETUP buffer into pkt.
void usb_read_setup_packet(usb_setup_pkt_t *pkt);

// Write data[] to the EP0 IN SRAM buffer and arm EP0 IN to transmit nbytes.
void usb_ep0_send_data(const uint32_t *data, uint32_t nbytes);

// Write the fixed device descriptor of the compile-time-selected controller
// (usb_dev1_device_descriptor when USB_DEV_SEL==1, else
// usb_dev0_device_descriptor) into the EP0 IN SRAM buffer and arm EP0 IN to
// transmit nbytes. Called from the GET_DESCRIPTOR(DEVICE) handler when the
// host requests the device descriptor.
void usb_ep0_send_device_descriptor(uint32_t nbytes);

// Arm EP0 IN with a zero-length packet (status phase for host-to-device
// control transfers).
void usb_ep0_send_zlp(void);

// Stall EP0 IN and OUT to indicate an unsupported or erroneous request.
void usb_ep0_stall(void);

// Re-arm EP0 OUT (Active=1, NBytes=0) for the next OUT or status-phase
// transaction.
void usb_ep0_arm_out(void);

// Clear the SETUP bit in DEVCMDSTAT (W1C). Must be called last after
// responding to a SETUP packet, per USB Integration Guide section 4.2.4.1.1.
void usb_clear_setup_bit(void);

// Dispatch the current SETUP packet: decode bmRequestType and bRequest,
// call the appropriate response helper, and stall EP0 with a log message
// for any request not yet implemented. Always calls usb_clear_setup_bit()
// before returning. Returns true if the request was fully handled, false
// if EP0 was stalled.
bool usb_handle_control_transfer(void);

// Update the USB device address field in DEVCMDSTAT.
void usb_set_device_address(uint8_t addr);

// Clear DEVCMDSTAT.FORCE_NEEDCLK so the device controller stops requesting
// the UTMI clock unconditionally and can actually enter suspend.
//
// boot_usb_core() / boot_usb_core_fs() set FORCE_NEEDCLK during bring-up.
// While it is set, usbreg_pll_on holds the compound-structure clock_on term
// high, which keeps reloading clk_off_counter to CLOCKOFF_CYCLE, which in
// turn holds utmi_suspendm high - so no suspend edge is ever visible to a
// UTMI-level suspend/resume checker.
//
// Call after enumeration completes and before host-side suspend stimulus is
// armed. Suspend-oriented tests only; leave FORCE_NEEDCLK set elsewhere.
// FORCE_VBUS is not modified.
void usb_allow_clock_stop(void);

// Drive a device-initiated remote wakeup: resume K signalling on the
// upstream port, requested by firmware rather than by the host.
//
// On this SoC the device controllers are AXI slaves and this firmware IS
// the device function, so firmware is the only possible initiator of a
// remote wakeup. The hardware trigger is NOT a set-a-bit operation: per
// usb_reg_if.m.vhdl, usbreg_remotewakeup is raised when a DEVCMDSTAT write
// presents bit 17 (DSUS) as 0 while the controller is currently suspended.
// A read-modify-write that only ORs bits in therefore never triggers it,
// because DSUS reads back as 1 while suspended. This helper masks bit 17
// off explicitly.
//
// Call only from a suspended state, typically on the DSUS_C event. Returns
// false and does nothing if the controller is not suspended. Acknowledges
// DSUS_C in the same write; leaves DRES_C, SETUP and DCON_C untouched so a
// caller polling for resume still sees its event.
//
// Note: the hub does not enforce the host's SetFeature(DEVICE_REMOTE_WAKEUP)
// permission grant (ep0_remote_wake_enabled is left unconnected in the IP
// structure), so this succeeds whether or not the host enabled the feature.
// See docs/usb_hub_port_suspend_not_wired_report.md.
bool usb_request_remote_wakeup(void);

// Device-initiated exit from L1 (LPM Sleep). Requires the controller to be in
// L1 (DEVCMDSTAT.LPM_SUS) with host-granted remote wake (DEVCMDSTAT.LPM_REWP);
// returns false and does nothing otherwise.
bool usb_request_lpm_remote_wakeup(void);



// Program the HUB RAM (descriptors + SETUP-match table), validate via
// readback, then set HUB_EN in the HUB Control register. HUB_CONNECT is
// NOT set here - call usb_hub_connect() separately afterward, per the
// reference janus_hub_ctrl_bfm.sv two-phase sequencing (HUB_EN alone
// first, then HUB_EN|HUB_CONNECT together after a settling delay). Must
// be called before the host can ever see USBDC0 or USBDC1, per USB Hub
// Composite Device User Guide section 3.2.7.
void usb_hub_init_and_connect(void);

// Set HUB_CONNECT (together with HUB_EN, which must already be set by a
// prior usb_hub_init_and_connect() call) in the HUB Control register,
// connecting the hub entity to the upstream port. Call this after
// usb_hub_init_and_connect() and after USBDC0 is ready (boot_usb_core()),
// since the host begins enumerating hub port 0 (and thus USBDC0) as soon
// as the hub connects upstream.
void usb_hub_connect(void);


#endif // USB_DRV_H

// File contains AI-generated response based on internal company sources
