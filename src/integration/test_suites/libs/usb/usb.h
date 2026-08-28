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
// HUB control/status registers and HUB RAM (hub_axi aperture).
//
// hub_axi maps to cptra_usb_device_s6 (0x2000_0000 - 0x2000_0FFF). Per the
// USB Hub Composite Device User Guide section 3.1.1/3.2.2:
//   offset 0x000: HUB Control register
//     bit  7  = HUB_EN       (1 = hub entity enabled, presents USBDC0/
//                              USBDC1 as embedded downstream devices)
//     bit 16  = HUB_CONNECT  (1 = hub connects to upstream port; set only
//                              after VBUS is valid and HUB RAM is
//                              programmed/validated and HUB_EN=1)
//   offset 0x004: HUB Status register (reserved/TBD)
//   offset 0x200-0x3FF: 512-byte HUB RAM (descriptors + SETUP-match table)
// -------------------------------------------------------------------------
#define USB_HUB_REG_BASE_ADDR        0x20000000u
#define USB_HUB_CTRL                 (USB_HUB_REG_BASE_ADDR + 0x000u)
#define USB_HUB_STATUS               (USB_HUB_REG_BASE_ADDR + 0x004u)
#define USB_HUB_RAM_BASE_ADDR        (USB_HUB_REG_BASE_ADDR + 0x200u)
// NOTE: the underlying hub_desc_mem RAM (accessed by the RTL's
// usb_ep0_handler.m.vhdl SETUP-decode FSM via ep0_mem_addr/hub_desc_dma_addr)
// is sized by the RAM_ADDRWIDTH=9 generic (see
// ip_xxx_3511_hs_mem_compound_cmp_pkg.p.vhdl), i.e. 2^9 = 512 DWORDs =
// 2048 bytes (0x000-0x7FF). The previous USB_HUB_RAM_SIZE=0x200 (512 bytes)
// was simply too small/conservative - it only reflected the descriptor +
// SETUP-match table region, not the true addressable RAM window that also
// contains the per-device "dev link" pointer slot read by the RTL FSM.
#define USB_HUB_RAM_SIZE             0x800u  /* 2048 bytes (RAM_ADDRWIDTH=9 -> 512 DWORDs) */

#define USBHUB_CTRL_HUB_EN_MASK      (1u << 7)
#define USBHUB_CTRL_HUB_CONNECT_MASK (1u << 16)

// HUB RAM layout offsets (relative to USB_HUB_RAM_BASE_ADDR), per User
// Guide section 3.2.2 recommended layout.
//
// IMPORTANT - address unit mismatch (root cause of ep0_request glitches):
// The RTL's usb_ep0_handler.m.vhdl PROC_SETUP_DECODE FSM does NOT read the
// ptrSetupTable pointer from a fixed firmware-chosen byte offset. Instead,
// on every new SETUP it first reads a per-device "dev link" pointer word at
// a FIXED RTL address, C_DEV_LINK_START = 12'h0F0 (usb_ep_config_hub_pkg.p.vhdl),
// which is a DWORD address 
//
// 
// The hub_desc descriptor-RAM AHB
// DMA port (hub_desc_ahbs_dma) is driven directly from the RAW, un-offset
// absolute AXI address bits coming out of the hub_axi -> AHB converter:
//   .hub_desc_ahbs_dma_haddr (hub_ahb_haddr[DMA_AHB_ADDR_W-1:0])
// There is NO subtraction of HUB_REG_ADDR_TOP (0x100) or of the RAM's own
// base offset (0x200) anywhere in this path - hub_ahb_haddr is the full
// absolute AXI byte address (masked only to DMA_AHB_ADDR_W bits). This
// means the RTL FSM's dword-address space (ep0_mem_addr /
// hub_desc_dma_addr, used directly as C_DEV_LINK_START=0x0F0 and as
// setup_mem_addr) is anchored at absolute byte 0x2000_0000
// (USB_HUB_REG_BASE_ADDR) Concretely: dword 0x0F0 = absolute byte
// 0x2000_0000 + 0x0F0*4 = 0x2000_03C0.
//
// All USB_HUB_RAM_*_OFFSET macros remain relative to
// USB_HUB_RAM_BASE_ADDR as before (so descriptor/table byte layout is
// unchanged), EXCEPT USB_HUB_RAM_PTR_SETUP_OFFSET, which must be placed so
// that USB_HUB_RAM_BASE_ADDR + USB_HUB_RAM_PTR_SETUP_OFFSET lands on the
// SAME absolute dword that the RTL reads at C_DEV_LINK_START (0x0F0
// dwords from USB_HUB_REG_BASE_ADDR). Since USB_HUB_RAM_BASE_ADDR is
// itself 0x200 bytes (0x80 dwords) above USB_HUB_REG_BASE_ADDR, the
// RAM-relative byte offset that aligns with absolute dword 0x0F0 is
// (0x0F0 - 0x80) * 4 = 0x1C0. USB_HUB_RAM_SETUP_TABLE_OFFSET is moved to
// 0x0200 (just past the existing descriptor slots) so it no longer
// overlaps the relocated pointer slot at 0x1C0.
#define USB_HUB_RAM_DESC0_OFFSET        0x0000u /* Hub Device Descriptor */
#define USB_HUB_RAM_DESC1_OFFSET        0x0040u /* Configuration Descriptor */
#define USB_HUB_RAM_DESC2_OFFSET        0x0080u /* Hub Class Descriptor */
#define USB_HUB_RAM_DESC3_OFFSET        0x00C0u /* Device Qualifier Descriptor */
#define USB_HUB_RAM_DESC4_OFFSET        0x0100u /* Other Speed Config Descriptor */
#define USB_HUB_RAM_SETUP_TABLE_OFFSET  0x0200u /* SETUP-match entries, 16B each (byte offset, relocated - see fix note above) */
#define USB_HUB_RAM_SETUP_ENTRY_SIZE    0x10u
// Dev-link pointer slot: RAM-relative byte offset 0x1C0 so that
// USB_HUB_RAM_BASE_ADDR + 0x1C0 (= absolute byte 0x2000_03C0) matches the
// RTL FSM's fixed read address at C_DEV_LINK_START (dword 0x0F0 from
// USB_HUB_REG_BASE_ADDR = absolute byte 0x2000_03C0). See fix note above.
#define USB_HUB_RAM_PTR_SETUP_OFFSET    0x01C0u /* dev-link ptr slot (RAM-relative byte addr, aligned to RTL C_DEV_LINK_START) */

// ((USB_HUB_RAM_BASE_ADDR - USB_HUB_REG_BASE_ADDR)/4 = 0x80 dwords),
// giving the correct absolute dword address 0x100 for the SETUP table
// at RAM-relative byte 0x200.
#define USB_HUB_RAM_SETUP_TABLE_DWORD_ADDR \
    (((USB_HUB_RAM_BASE_ADDR - USB_HUB_REG_BASE_ADDR) + USB_HUB_RAM_SETUP_TABLE_OFFSET) / 4u)

// The GET_DESCRIPTOR SETUP-match table entries' DPBUF field (bits[6:0] of
// the DPBUF byte when bit7=1) selects a descriptor "slot" that is consumed
// by the EP0-IN streaming DMA path (usb_ep_config_hub_pkg.p.vhdl places
// DPBUF directly into the EP0-IN list entry's AddrOffset field, i.e. the
// slot number * 64 bytes = the absolute upd_dma_addr-space byte address
// streamed for the IN data phase). This address space is anchored at
// USB_HUB_REG_BASE_ADDR (absolute, aperture byte 0 = slot 0), per the
// same RTL addressing convention established for the dev-link pointer
// and SETUP-table dword address above. Firmware's descriptor writes
// target USB_HUB_RAM_BASE_ADDR + USB_HUB_RAM_DESCn_OFFSET, i.e. absolute
// aperture byte (USB_HUB_RAM_BASE_ADDR - USB_HUB_REG_BASE_ADDR) + offset.
// Bias every DPBUF slot number used for GET_DESCRIPTOR entries by this
// constant (in units of 64-byte slots) so the slot's implied aperture
// address matches the actual descriptor write address.
#define USB_HUB_DESC_SLOT_BASE \
    (((USB_HUB_RAM_BASE_ADDR - USB_HUB_REG_BASE_ADDR)) / 64u)



// SETUP-match entry field byte offsets (within a 16-byte entry)
#define USB_HUB_SETUP_ENTRY_BMREQTYPE   0x00u
#define USB_HUB_SETUP_ENTRY_BREQUEST    0x01u
#define USB_HUB_SETUP_ENTRY_WVALUE      0x02u
#define USB_HUB_SETUP_ENTRY_REQ_L       0x04u /* Request[6:0] + L[7] */
#define USB_HUB_SETUP_ENTRY_DPBUF       0x05u /* DataPhase_Buffer selector */
#define USB_HUB_SETUP_ENTRY_WVALUE_MASK 0x06u
#define USB_HUB_SETUP_ENTRY_WINDEX      0x08u
#define USB_HUB_SETUP_ENTRY_DPLEN       0x0Au /* DataPhase_Length */
#define USB_HUB_SETUP_ENTRY_WINDEX_MASK 0x0Cu
#define USB_HUB_SETUP_ENTRY_L_MASK      0x80u /* bit7 of REQ_L byte */


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
// Default minimal USB 2.0 device descriptor (18 bytes, packed as uint32_t[5]).
// Defined in usb.c. Tests that need a custom descriptor may define their own
// array and pass it directly to usb_ep0_send_data().
// -------------------------------------------------------------------------
extern const uint32_t usb_default_device_descriptor[5];

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
