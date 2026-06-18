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
// DMA slave base address and SRAM buffer layout constants.
// These are not RDL-specified and therefore not present in any generated
// header. All USB register addresses and field masks are in soc_address_map.h
// under the USBHSD_* / USBHSH_* naming convention; use those directly.
// -------------------------------------------------------------------------
#define USB_DMA_BASE_ADDR            0x20010000u

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
#define USB_EP_ENTRY_STALL        (1u << 29)
#define USB_EP_ENTRY_NBYTES(n)    (((uint32_t)(n) & 0x7FFFu) << 11)
#define USB_EP_ENTRY_ADDR(off)    (((uint32_t)(off) >> 6) & 0x7FFu)

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

// Dump a snapshot of key USB controller state with a caller-provided tag.
void usb_dump_state(const char *tag);

// Poll DEV_INT and EP0OUT and dispatch USB events. Returns when max_iters is
// reached. max_iters==0 means loop indefinitely.
void usb_event_loop(uint32_t max_iters);

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

// Returns 1 once the device has reached the USB Configured state (a
// SET_CONFIGURATION with a non-zero value has been accepted), else 0.
// USB 2.0 sec 9.4.7 / 9.1.1.5. Used to gate the MCU->Caliptra recovery
// handoff until USB enumeration is complete.
uint8_t usb_is_configured(void);

#endif // USB_DRV_H
