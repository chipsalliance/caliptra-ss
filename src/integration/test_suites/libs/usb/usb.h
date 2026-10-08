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

#ifndef USB_EVENT_LOOP_DIAG_PERIOD
#define USB_EVENT_LOOP_DIAG_PERIOD 10000u
#endif

// -------------------------------------------------------------------------
// Device selection for the shared USB test library (USB_DEV_SEL).
//
// usb.c is compiled per test into that test's own build directory, so the
// controller under test is selected at compile time with -DUSB_DEV_SEL=<0|1>
// passed through BUILD_CFLAGS from the test yml, e.g.
//   BUILD_CFLAGS="-DUSB_DEV_SEL=1"
// Default is 0 (USBDC0) so every pre-existing test keeps its behaviour with
// no yml change.
//
// The compound USB IP (ip_xxx_3511_hs_mem_compound_wrapper) exposes two
// embedded device controllers behind an on-chip 2-port hub:
//   DEV0 (USBDC0) - CSR bank at SOC_USB_COMBO_DEV0_CSR_BASE_ADDR (0x2000_0000),
//                   packet SRAM at SOC_USB_DEV0_MEM_BASE_ADDR   (0x3000_0000)
//   DEV1 (USBDC1) - CSR bank at SOC_USB_DEV1_CSR_BASE_ADDR      (0x2000_2000),
//                   packet SRAM at SOC_USB_DEV1_MEM_BASE_ADDR   (0x3001_0000)
//
// IMPORTANT: soc_address_map.h only generates the DEV0_CSR_* bitfield MASK/
// SHIFT macros. Those masks are OFFSET-INDEPENDENT within a CSR bank, so they
// apply verbatim to BOTH controllers. USB_DEV_SEL therefore parametrizes only
// the register/SRAM ADDRESSES, never the bitfield masks. All library code and
// all device-agnostic test code must use the neutral USB_DEV_* register macros
// and USB_DEV_MEM_BASE_ADDR below.
// -------------------------------------------------------------------------
#ifndef USB_DEV_SEL
#define USB_DEV_SEL 0
#endif

#if (USB_DEV_SEL == 1)
#define USB_DEV_CSR_BASE_ADDR        SOC_USB_DEV1_CSR_BASE_ADDR
#define USB_DEV_MEM_BASE_ADDR        SOC_USB_DEV1_MEM_BASE_ADDR
#elif (USB_DEV_SEL == 0)
#define USB_DEV_CSR_BASE_ADDR        SOC_USB_COMBO_DEV0_CSR_BASE_ADDR
#define USB_DEV_MEM_BASE_ADDR        SOC_USB_DEV0_MEM_BASE_ADDR
#else
#error "USB_DEV_SEL must be 0 (USBDC0) or 1 (USBDC1)"
#endif

// Device-neutral CSR register addresses. These resolve to the controller
// selected by USB_DEV_SEL and are what the shared library (usb.c) uses so a
// single compiled image can drive either USBDC0 or USBDC1. The register offset
// layout is identical for both banks (see soc_address_map.h); only the base
// differs. For USB_DEV_SEL==0 these are byte-for-byte the same addresses the
// upstream driver hardcoded as SOC_USB_COMBO_DEV0_CSR_*, so DEV0/OCP behaviour
// is unchanged.
#define USB_DEV_DEVCMDSTAT    (USB_DEV_CSR_BASE_ADDR + 0x00u)
#define USB_DEV_INFO          (USB_DEV_CSR_BASE_ADDR + 0x04u)
#define USB_DEV_EPLISTSTART   (USB_DEV_CSR_BASE_ADDR + 0x08u)
#define USB_DEV_DATABUFSTART  (USB_DEV_CSR_BASE_ADDR + 0x0cu)
#define USB_DEV_LPM           (USB_DEV_CSR_BASE_ADDR + 0x10u)
#define USB_DEV_EPSKIP        (USB_DEV_CSR_BASE_ADDR + 0x14u)
#define USB_DEV_EPINUSE       (USB_DEV_CSR_BASE_ADDR + 0x18u)
#define USB_DEV_EPBUFCFG      (USB_DEV_CSR_BASE_ADDR + 0x1cu)
#define USB_DEV_INTSTAT       (USB_DEV_CSR_BASE_ADDR + 0x20u)
#define USB_DEV_INTEN         (USB_DEV_CSR_BASE_ADDR + 0x24u)
#define USB_DEV_INTSETSTAT    (USB_DEV_CSR_BASE_ADDR + 0x28u)
#define USB_DEV_EPTOGGLE      (USB_DEV_CSR_BASE_ADDR + 0x34u)
#define USB_DEV_ULPIDEBUG     (USB_DEV_CSR_BASE_ADDR + 0x3cu)

// -------------------------------------------------------------------------
// DEV packet SRAM buffer layout.
//
// On this compound IP the EP command/status list and data buffers live in a
// DEDICATED dense memory (SOC_USB_DEV0/1_MEM_BASE_ADDR, 0x3000_0000 /
// 0x3001_0000), separate from the 0x2000_xxxx register window. EPLISTSTART and
// DATABUFSTART are therefore set to 0 and all EP-entry AddrOffset fields are
// OFFSET-RELATIVE to the MEM base (see USB_EP_ENTRY_ADDR / USB_EP_ENTRY_ABS_ADDR
// below). USB_DMA_BASE_ADDR is the device-neutral MEM base and is kept as the
// name existing test firmware uses.
// -------------------------------------------------------------------------
#define USB_DMA_BASE_ADDR            USB_DEV_MEM_BASE_ADDR

// USB_DEV_DMA_BASE_ADDR - legacy alias of USB_DMA_BASE_ADDR kept for the many
// device tests that reference the device-selected DMA/MEM base by this name
// (e.g. "dma_base = USB_DEV_DMA_BASE_ADDR;" and
// "USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + off)"). Both resolve to the
// same compile-time-selected MEM base (USB_DEV_MEM_BASE_ADDR), so this is a
// pure name alias with no behaviour change.
#define USB_DEV_DMA_BASE_ADDR        USB_DMA_BASE_ADDR


#define USB_SRAM_EP_LIST_OFFSET      0x000u
#define USB_SRAM_SETUP_BUF_OFFSET    0x100u
#define USB_SRAM_EP0_OUT_BUF_OFFSET  0x140u
#define USB_SRAM_EP0_IN_BUF_OFFSET   0x180u

// -------------------------------------------------------------------------
// HUB control/status register and descriptor-override window (hub aperture).
//
// On the compound IP the hub CSR/descriptor aperture is at
// SOC_USB_COMBO_HUB_BASE_ADDR (0x2000_1000); the hub control/status word
// (C_HUB_CS) is SOC_USB_COMBO_HUB_CONTROL (0x2000_103C):
//   bit  0 = HUB_EN       (structural mux select; hub entity enabled and
//                          presents USBDC0/USBDC1 as embedded downstream
//                          devices)
//   bit 16 = HUB_CONNECT  (hub connects to the upstream port, ANDed with
//                          VBus valid inside the IP)
//
// USB_EnableHub is tied 1'b0 at top level (caliptra_ss_top.sv:1190), so
// hub_enable_q is driven by the register bit ep0_mem(C_HUB_CS)(0) and firmware
// MUST set HUB_EN to enter hub mode. The migrated device tests all target the
// HUB+DEVICE (hub-composite) configuration, so the two-phase bring-up
// (usb_hub_init_and_connect() then usb_hub_connect()) is retained.
//
// HUB_EN bit position: the RTL samples bit 0, but the IP's own reference BFM
// still writes bit 7 (its legacy position). USBHUB_CTRL_HUB_EN_MASK sets BOTH
// so the sequence works either way; bit 7 is a don't-care for the current RTL.
//
// The IP asserts hub_write_lock once HUB_EN and HUB_CONNECT are both set, and
// the descriptor array freezes with it, so any descriptor override MUST be
// written before usb_hub_connect() while the array is still unlocked (HUB_EN
// alone does not lock it).
//
// NOTE (this RTL): the current EP0 response path reads C_EP0_ROM directly, so
// the descriptor shadow writes may no longer change the descriptor RESPONSE.
// They are retained for parity with legacy; any scoreboard effect must be
// re-validated on this RTL.
// -------------------------------------------------------------------------
#define USB_HUB_CTRL                 SOC_USB_COMBO_HUB_CONTROL

#define USBHUB_CTRL_HUB_EN_MASK      ((1u << 0) | (1u << 7))
#define USBHUB_CTRL_HUB_CONNECT_MASK (1u << 16)

// Hub DEVICE descriptor override (DataPhase_Buffer_0 of the hub aperture,
// base SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR = 0x2000_1000). The 18-byte
// device descriptor is packed 32-bit LSB-first:
//   word2 @ 0x08 = idVendor  | idProduct<<16
//   word3 @ 0x0C = bcdDevice | iManufacturer<<16 | iProduct<<24
//   word4 @ 0x10 = iSerialNumber(byte0) | bNumConfigurations(byte1)<<8 | ...
// word2/word3 are clean full-word fields; word4 shares its low byte
// (iSerialNumber) with bNumConfigurations, so iSerialNumber is changed with a
// read-modify-write of only the low byte.
#define USB_HUB_DESC_DEVICE_BASE     SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR
#define USB_HUB_DESC_DEV_WORD2       (USB_HUB_DESC_DEVICE_BASE + 0x08u)
#define USB_HUB_DESC_DEV_WORD3       (USB_HUB_DESC_DEVICE_BASE + 0x0Cu)
#define USB_HUB_DESC_DEV_WORD4       (USB_HUB_DESC_DEVICE_BASE + 0x10u)
#define USB_HUB_DESC_DEV_WORD2_VAL   0xBE011FC9u
#define USB_HUB_DESC_DEV_WORD3_VAL   0x02010200u
#define USB_HUB_DESC_DEV_ISERIAL_VAL 0x03u

// Hub DEVICE QUALIFIER descriptor override (DataPhase_Buffer_3, base +0xC0).
// qw1 @ +0xC4 packs bDeviceClass | bDeviceSubClass<<8 | bDeviceProtocol<<16 |
// bMaxPacketSize0<<24 - a clean full word. Sets bDeviceSubClass 0x02,
// bDeviceProtocol 0x01, bMaxPacketSize0 0x08 (other-speed EP0 size, spec-legal)
// while keeping bDeviceClass 0x00.
#define USB_HUB_DESC_QUAL_BASE       (USB_HUB_DESC_DEVICE_BASE + 0x0C0u)
#define USB_HUB_DESC_QUAL_WORD1      (USB_HUB_DESC_QUAL_BASE + 0x04u)
#define USB_HUB_DESC_QUAL_WORD1_VAL  0x08010200u

// Hub CONFIGURATION (DataPhase_Buffer_1, base +0x40) and
// OTHER_SPEED_CONFIGURATION (base +0x100) descriptor override. Both share the
// 9-byte header layout; the only safely-overridable informational field is
// iConfiguration (byte 2 of word1), changed with a read-modify-write of only
// that byte to preserve bmAttributes. bMaxPower is left at the RTL default.
#define USB_HUB_DESC_CFG_BASE        (USB_HUB_DESC_DEVICE_BASE + 0x040u)
#define USB_HUB_DESC_CFG_WORD1       (USB_HUB_DESC_CFG_BASE + 0x04u)
#define USB_HUB_DESC_OSC_BASE        (USB_HUB_DESC_DEVICE_BASE + 0x100u)
#define USB_HUB_DESC_OSC_WORD1       (USB_HUB_DESC_OSC_BASE + 0x04u)
#define USB_HUB_DESC_ICONFIG_VAL     0x04u

// Hub CLASS descriptor override (DataPhase_Buffer_2, base +0x080). word1 @
// +0x84 packs wHubCharacteristics.hi | bPwrOn2PwrGood<<8 | bHubContrCurrent<<16
// | DeviceRemovable<<24 - a clean full-word override. Sets bPwrOn2PwrGood 0x32
// (100 ms), bHubContrCurrent 0x64 (100 mA), DeviceRemovable 0x0A while keeping
// wHubCharacteristics.hi 0x00.
#define USB_HUB_DESC_HUB_BASE        (USB_HUB_DESC_DEVICE_BASE + 0x080u)
#define USB_HUB_DESC_HUB_WORD1       (USB_HUB_DESC_HUB_BASE + 0x04u)
#define USB_HUB_DESC_HUB_WORD1_VAL   0x0A643200u

// -------------------------------------------------------------------------
// Legacy EP0 observer telemetry (MCI generic-wire handshake). Retained from
// upstream; used by the legacy-EP0 observation tests.
// -------------------------------------------------------------------------
#define USB_LEGACY_EP0_SNAPSHOT_VERSION 1u
#define USB_LEGACY_EP0_DATA_MAGIC       0xA5u
#define USB_LEGACY_EP0_READY_MAGIC      0x5Au
#define USB_LEGACY_EP0_ACK_MAGIC        0xC3u
#define USB_LEGACY_EP0_READY_FIELD      0x1Fu
#define USB_LEGACY_EP0_SNAPSHOT_FIELDS  18u

// MCU generic input wire 1 carries one generation-qualified observer command.
// The 32-bit format is magic[31:24], opcode[23:20], expected legacy SETUP
// dispatch delta[19:16], and generation[15:0].
#define USB_LEGACY_EP0_COMMAND_MAGIC             0xB7u
#define USB_LEGACY_EP0_COMMAND_ACK_MAGIC         0xD6u
#define USB_LEGACY_EP0_COMMAND_PUBLISH_BASELINE  0x1u
#define USB_LEGACY_EP0_COMMAND_PUBLISH_POST      0x2u
#define USB_LEGACY_EP0_COMMAND_RELEASE_CALIPTRA  0x3u
#define USB_LEGACY_EP0_COMMAND_PUBLISH_RESET_POST 0x4u
#define USB_LEGACY_EP0_COMMAND_CLEAR_DCON        0x5u
#define USB_LEGACY_EP0_COMMAND_SET_DCON          0x6u
#define USB_LEGACY_EP0_COMMAND_MAGIC_SHIFT       24u
#define USB_LEGACY_EP0_COMMAND_OPCODE_SHIFT      20u
#define USB_LEGACY_EP0_COMMAND_DELTA_SHIFT       16u
#define USB_LEGACY_EP0_COMMAND_NIBBLE_MASK       0xFu
#define USB_LEGACY_EP0_COMMAND_GENERATION_MASK   0xFFFFu

typedef enum {
    USB_LEGACY_EP0_SNAPSHOT_BASELINE = 1u,
    USB_LEGACY_EP0_SNAPSHOT_POST     = 2u
} usb_legacy_ep0_snapshot_state_t;

typedef struct {
    uint32_t publish_sequence;
    uint32_t setup_word0;
    uint32_t setup_word1;
    uint32_t ep0_out_descriptor;
    uint32_t ep0_setup_descriptor;
    uint32_t ep0_in_descriptor;
    uint32_t ep0_reserved_descriptor;
    uint32_t devcmdstat;
    uint32_t intstat;
    uint32_t inten;
    uint32_t configuration;
    uint32_t transfers_handled;
    uint32_t bus_reset_count;
    uint32_t ep0_irq_count;
    uint32_t ep0_out_irq_count;
    uint32_t ep0_in_irq_count;
    uint32_t setup_dispatch_count;
    uint32_t snapshot_version;
} usb_legacy_ep0_snapshot_t;

// EP command/status list entry bit fields (from RTL usb_dma.m.vhdl line 420:
//   "epinfo_nbytes <= dma_rdata(25 downto 11);" and line 421:
//   "epinfo_addr_offset <= dma_rdata(C_DALB-7 downto 0);" with C_DALB=17
//   in our integration -> addr_offset at bits [10:0]).
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
// USB_EP_ENTRY_ADDR(off) - AddrOffset field [10:0] from a MEM-base-relative
// byte offset. This is the correct form on this RTL: the SRAM is a dedicated
// dense memory (USB_DMA_BASE_ADDR) and EPLISTSTART/DATABUFSTART are 0, so the
// DMA engine reconstructs buffer addresses from (offset>>6).
#define USB_EP_ENTRY_ADDR(off)    (((uint32_t)(off) >> 6) & 0x7FFu)
// USB_EP_ENTRY_ABS_ADDR(abs_addr) - AddrOffset field [10:0] from an ABSOLUTE
// AXI byte address of the data buffer. Retained for the many device tests that
// pass (USB_DMA_BASE_ADDR + SRAM_offset). The AddrOffset field the DMA engine
// programs is RELATIVE to the controller's own MEM base (EPLISTSTART/
// DATABUFSTART are 0), so the MEM base MUST be subtracted before the >>6 shift.
//
// DEV0 MEM base is 0x3000_0000 (bit16=0), so for DEV0 the subtraction is a
// no-op and this matches the historical behaviour byte-for-byte. DEV1 MEM base
// is 0x3001_0000 (bit16=1); WITHOUT the subtraction, bit16 of the absolute
// address leaks into AddrOffset bit10 (adds 0x400) and the EP buffers point
// outside the DEV1 SRAM window, so the host times out on every DEV1 EP0 control
// transfer. Subtracting USB_DEV_MEM_BASE_ADDR makes both controllers correct
// and makes this macro identical to USB_EP_ENTRY_ADDR(off) for any
// off = abs_addr - USB_DEV_MEM_BASE_ADDR:
//   USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + off) == USB_EP_ENTRY_ADDR(off).
#define USB_EP_ENTRY_ABS_ADDR(abs_addr) \
    ((((uint32_t)(abs_addr) - (uint32_t)USB_DEV_MEM_BASE_ADDR) >> 6) & 0x7FFu)


#define USB_DEV0_ENDPOINT_INTERRUPT_MASK \
    (DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK | \
     DEV0_CSR_INTSTAT_EP1OUT_MASK | DEV0_CSR_INTSTAT_EP1IN_MASK | \
     DEV0_CSR_INTSTAT_EP2OUT_MASK | DEV0_CSR_INTSTAT_EP2IN_MASK | \
     DEV0_CSR_INTSTAT_EP3OUT_MASK | DEV0_CSR_INTSTAT_EP3IN_MASK | \
     DEV0_CSR_INTSTAT_EP4OUT_MASK | DEV0_CSR_INTSTAT_EP4IN_MASK | \
     DEV0_CSR_INTSTAT_EP5OUT_MASK | DEV0_CSR_INTSTAT_EP5IN_MASK | \
     DEV0_CSR_INTSTAT_EP_UPPER_MASK)
#define USB_DEV0_IMPLEMENTED_INTERRUPT_MASK \
    (USB_DEV0_ENDPOINT_INTERRUPT_MASK | DEV0_CSR_INTSTAT_FRAME_INT_MASK | \
     DEV0_CSR_INTSTAT_DEV_INT_MASK)

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

// Application hook typedefs (PR #1299 seam). The config-descriptor provider
// returns a pointer to the device's full configuration descriptor and writes
// its length to *len; the class-request handler services a class-typed SETUP
// packet and returns true once fully serviced.
typedef const uint8_t *(*usb_config_descriptor_provider_t)(uint16_t *len);
typedef bool (*usb_class_request_handler_t)(const usb_setup_pkt_t *setup);

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
// differ in idProduct and bcdDevice so a scoreboard can tell which controller
// answered the host. Defined in usb.c. The controller actually served on a
// GET_DESCRIPTOR(DEVICE) is selected at compile time by USB_DEV_SEL (see
// usb_ep0_send_device_descriptor()).
extern const usb_device_descriptor_t usb_dev0_device_descriptor;
extern const usb_device_descriptor_t usb_dev1_device_descriptor;

// -------------------------------------------------------------------------
// USB driver API
// -------------------------------------------------------------------------

// Runtime active-device selector for the shared USB library.
//
// usb.c normally binds every CSR/MEM access to the controller chosen at
// compile time by USB_DEV_SEL (default 0 = USBDC0). usb_select_device() lets a
// single compiled image retarget the shared enumeration / control-transfer
// helpers to USBDC0 (dev=0) or USBDC1 (dev=1) at run time, which the
// usb_hib_compound dual-device test uses to bring up BOTH controllers in
// parallel. Per-device shadow state (device address, current configuration,
// remote-wakeup, EP0 IN pending) is kept in private arrays inside usb.c so the
// two controllers do not corrupt each other's enumeration state.
//
// The initial value is USB_DEV_SEL, so any test that never calls
// usb_select_device() behaves byte-for-byte as before. Pass 0 for USBDC0 or 1
// for USBDC1; any other value is treated as 0.
void usb_select_device(int dev);

// Returns the currently selected active device (0 = USBDC0, 1 = USBDC1).
int usb_get_active_device(void);

// Runtime base-address accessors for the currently selected active device.
//
// usb.c re-defines the device-neutral USB_DEV_* register macros and
// USB_DMA_BASE_ADDR to resolve against usb_select_device()'s runtime choice,
// but that #undef/#define retargeting is scoped to usb.c's translation unit.
// A test that includes usb.h and accesses USB_DEV_* directly in its OWN
// functions still gets the compile-time USB_DEV_SEL-fixed base and cannot
// follow usb_select_device(). These accessors expose usb.c's selection logic so
// such a test can build its own runtime-selected addresses (see the dual-device
// test's USB_DEV_* re-definition). usb_active_dev_csr_base() returns the active
// controller's CSR bank base; usb_active_dev_mem_base() its packet SRAM base.
uint32_t usb_active_dev_csr_base(void);
uint32_t usb_active_dev_mem_base(void);




// Initialize the USB device controller (STANDALONE DEV0, no hub bring-up):
// set up the EP command/status list and SRAM buffers, enable device mode and
// interrupts. config_desc_fn / class_req_fn install the application's
// config-descriptor and class-request hooks BEFORE enumeration can begin; pass
// 0 for either to use the built-in default (no config descriptor / STALL class
// requests). This is the OCP-recovery / host enumeration entry point.
void boot_usb_core(usb_config_descriptor_provider_t config_desc_fn,
                   usb_class_request_handler_t class_req_fn);

// Initialize the USB device controller in HUB+DEVICE (hub-composite) mode:
// bring the on-chip hub up (usb_hub_init_and_connect(): HUB_EN + descriptor
// overrides), configure the EP list/SRAM buffers, force LPM_SUP and
// FORCE_NEEDCLK during bring-up, and enable device mode and interrupts. This
// is the entry point for the migrated device tests that target the hub-composite
// configuration. HUB_CONNECT is NOT asserted here - the test calls
// usb_hub_connect() once the device controller is fully programmed.
void boot_usb_core_hub(void);

// Initialize the USB device controller in HUB+DEVICE FS-only mode: identical
// to boot_usb_core_hub() but also sets DEVCMDSTAT bit 21 (FORCE_FULLSPEED, the
// legacy PFSC bit) to suppress device-side K-chirp. Use in tests with a FS-only
// host VIP (high_speed_capable=0) so the UTMI TX is ready immediately after bus
// reset instead of waiting ~2.2ms for the chirp timeout. Do NOT use when HS
// operation is required.
void boot_usb_core_fs(void);

// Program HUB descriptor overrides then set HUB_EN in the HUB control register.
// HUB_CONNECT is NOT set here - call usb_hub_connect() separately afterward,
// per the reference two-phase sequencing (HUB_EN alone first, then
// HUB_EN|HUB_CONNECT together after a settling delay). Must be called before
// the host can ever see USBDC0 or USBDC1.
void usb_hub_init_and_connect(void);

// Set HUB_CONNECT (together with HUB_EN, which must already be set by a prior
// usb_hub_init_and_connect() call) in the HUB control register, connecting the
// hub entity to the upstream port. Call after usb_hub_init_and_connect() and
// after the device controller is ready, since the host begins enumerating hub
// port 0 as soon as the hub connects upstream.
void usb_hub_connect(void);

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
// transmit nbytes. Called from the GET_DESCRIPTOR(DEVICE) handler.
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

// Dump a snapshot of key USB controller state with a caller-provided tag.
void usb_dump_state(const char *tag);

// Poll DEV_INT and EP0OUT and dispatch USB events. Returns when max_iters
// or expected_transfers is reached. max_iters==0 means loop indefinitely.
// expected_transfers==0 means loop indefinitely.
uint32_t usb_event_loop(uint32_t max_iters, uint32_t expected_transfers);

// Returns the device's full configuration descriptor blob and writes its
// length in bytes to *len. The default weak implementation returns NULL and
// sets *len=0 so GET_DESCRIPTOR(CONFIGURATION) falls through to STALL.
__attribute__((weak))
const uint8_t *usb_get_config_descriptor(uint16_t *len);

// Handles a class-typed SETUP packet. Return true once the request has been
// fully serviced; return false to let the dispatcher STALL the request. The
// default weak implementation returns false.
__attribute__((weak))
bool usb_handle_class_request(const usb_setup_pkt_t *setup);

// Update the USB device address field in DEVCMDSTAT.
void usb_set_device_address(uint8_t addr);

// Update the device-connect bit while preserving the staged device address.
void usb_set_device_connect(uint8_t connected);

// Returns 1 once the device has reached the USB Configured state (a
// SET_CONFIGURATION with a non-zero value has been accepted), else 0.
// USB 2.0 sec 9.4.7 / 9.1.1.5. Used to gate the MCU->Caliptra recovery
// handoff until USB enumeration is complete.
uint8_t usb_is_configured(void);

// Clear DEVCMDSTAT.FORCE_NEEDCLK so the device controller stops requesting the
// UTMI clock unconditionally and can actually enter suspend. boot_usb_core_hub()
// / boot_usb_core_fs() set FORCE_NEEDCLK during bring-up. Call after enumeration
// completes and before host-side suspend stimulus is armed. Suspend-oriented
// tests only. FORCE_VBUS is not modified.
void usb_allow_clock_stop(void);

// Drive a device-initiated remote wakeup: resume K signalling on the upstream
// port, requested by firmware rather than by the host. The hardware trigger is
// a DEVCMDSTAT write presenting bit 17 (DSUS) as 0 while suspended, so a plain
// OR-in RMW never triggers it; this helper masks bit 17 off explicitly. Call
// only from a suspended state; returns false and does nothing otherwise.
// Acknowledges DSUS_C in the same write; leaves DRES_C, SETUP and DCON_C
// untouched so a caller polling for resume still sees its event.
bool usb_request_remote_wakeup(void);

// Device-initiated exit from L1 (LPM Sleep). Requires the controller to be in
// L1 (DEVCMDSTAT.LPM_SUS) with host-granted remote wake (DEVCMDSTAT.LPM_REWP);
// returns false and does nothing otherwise.
bool usb_request_lpm_remote_wakeup(void);

// Capture the complete legacy baseline and publish it field-by-field over the
// MCI generic-wire handshake. UVM starts SRAM observation only after firmware
// publishes the matching generation-qualified ready header.
void usb_legacy_ep0_publish_baseline(uint16_t generation);

// Capture legacy state after firmware has observed the target command's
// semantic completion condition, then publish the matching generation over the
// same generic-wire handshake.
void usb_legacy_ep0_publish_post_snapshot(uint16_t generation);

void usb_legacy_ep0_capture_snapshot(
    usb_legacy_ep0_snapshot_t *snapshot);

uint32_t usb_legacy_ep0_get_setup_dispatch_count(void);
uint32_t usb_legacy_ep0_get_bus_reset_count(void);

#endif // USB_DRV_H

// File contains AI-generated response based on internal company sources
