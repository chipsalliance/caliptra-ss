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

#include "usb.h"

// Minimal USB 2.0 device descriptor (18 bytes, packed as uint32_t for SRAM writes)
const uint32_t usb_default_device_descriptor[5] = {
    0x00020112,  // bLength=18, bDescType=1(DEVICE), bcdUSB=0x0200 (LE)
    0x40000000,  // bDevClass=0, bDevSubClass=0, bDevProto=0, bMaxPktSz0=64
    0x00000000,  // idVendor=0x0000, idProduct=0x0000
    0x00000100,  // bcdDevice=0x0100, iManufacturer=0
    0x01000000   // iProduct=0, iSerialNumber=0, bNumConfigurations=1
};

// -------------------------------------------------------------------------
// boot_usb_core - Initialize the USB device controller
//
// Sets up the EP command/status list and data buffers in SRAM, then
// configures EPLISTSTART, DATABUFSTART, DEVCMDSTAT, and interrupt enables
// so the USB device is ready to respond to host enumeration.
//
// SRAM layout:
//   0x000-0x00F: EP0 command/status list (4 words)
//   0x010-0x0FF: Other EP entries (zeroed/disabled)
//   0x100-0x107: SETUP data buffer (8 bytes)
//   0x140-0x17F: EP0 OUT data buffer (64 bytes)
//   0x180-0x1BF: EP0 IN data buffer (64 bytes)
// -------------------------------------------------------------------------
void boot_usb_core(void) {
    uint32_t reg_data;

    VPRINTF(LOW, "MCU: boot_usb_core - initializing USB device controller\n");

    // --- Step 0a: Enable device-mode in the OTG PHY mux ---
    // PORTMODE.PORT_MODE (bit 16) drives the VHDL dev_enable signal that
    // routes UTMI signals between host and device controllers in the OTG
    // PHY mux. Must be set to 1 so the device controller sees the UTMI bus.
    // Other PORTMODE bits are reset-default; write the PORT_MODE bit directly.
    reg_data = USBHSH_PORTMODE_PORT_MODE_MASK;
    lsu_write_32(SOC_USBHSH_PORTMODE, reg_data);
    VPRINTF(LOW, "MCU: USB PORTMODE configured (dev mode, write-only) = 0x%x\n", reg_data);

    // Read DEVCMDSTAT to check initial state
    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT initial = 0x%x\n", reg_data);

    // --- Step 0: Initialize SRAM via DMA port ---

    // EP0 OUT entry: Active=1, NBytes=8 (for SETUP), addr_offset = 0x140>>6 = 5
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    // EP0 SETUP buffer address entry: addr_offset = 0x100>>6 = 4
    uint32_t ep0_setup_entry = USB_EP_ENTRY_ADDR(USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    // EP0 IN entry: Active=0, NBytes=0, addr_offset = 0x180>>6 = 6
    uint32_t ep0_in_entry = USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    lsu_write_32(SOC_USBHSD_EPLISTSTART, 0x00000000);

    // --- Step 2: Set data buffer page address ---
    lsu_write_32(SOC_USBHSD_DATABUFSTART, 0x00000000);

    // --- Step 3: Enable device ---
    // HS link-up: do NOT set FORCE_FULLSPEED. The device controller will
    // perform HS chirp at the next bus reset.
    reg_data = USBHSD_DEVCMDSTAT_DEV_EN_MASK
             | USBHSD_DEVCMDSTAT_FORCE_VBUS_MASK
             | USBHSD_DEVCMDSTAT_DCON_MASK;
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n", reg_data);

    // Read back to confirm
    reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 4: Enable interrupts ---
    lsu_write_32(SOC_USBHSD_INTEN,
        USBHSD_INTSTAT_DEV_INT_MASK |
        USBHSD_INTSTAT_EP0OUT_MASK  |
        USBHSD_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        USBHSD_INTSTAT_DEV_INT_MASK | USBHSD_INTSTAT_EP0OUT_MASK | USBHSD_INTSTAT_EP0IN_MASK);

    // --- Step 5: Clear pending interrupts ---
    lsu_write_32(SOC_USBHSD_INTSTAT, 0xC0000FFF);

    VPRINTF(LOW, "MCU: boot_usb_core - done\n");
}

void usb_ep0_reinit(void) {
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out_entry);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x004,
                 USB_EP_ENTRY_ADDR(USB_SRAM_SETUP_BUF_OFFSET));
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008,
                 USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET));
    VPRINTF(LOW, "MCU: usb_ep0_reinit - EP0 entries restored (EP0OUT=0x%x)\n", ep0_out_entry);
}

void usb_handle_bus_reset(void) {
    uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    if (!(cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK)) {
        return;
    }
    VPRINTF(LOW, "MCU: USB bus reset detected\n");
    // Clear DRES_C (W1C)
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd | USBHSD_DEVCMDSTAT_DRES_C_MASK);
    usb_ep0_reinit();
    // Reset device address to 0 per USB spec
    cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    cmd &= ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK;
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
}

void usb_read_setup_packet(usb_setup_pkt_t *pkt) {
    uint32_t w0 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    uint32_t w1 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET + 4);
    pkt->bmRequestType = (uint8_t)((w0 >>  0) & 0xFF);
    pkt->bRequest      = (uint8_t)((w0 >>  8) & 0xFF);
    pkt->wValue        = (uint16_t)((w0 >> 16) & 0xFFFF);
    pkt->wIndex        = (uint16_t)((w1 >>  0) & 0xFFFF);
    pkt->wLength       = (uint16_t)((w1 >> 16) & 0xFFFF);
    // NOTE: VPRINTF intentionally omitted from the SETUP read hot-path.
    // Logging before priming EP0 IN causes the VIP tend_to_end_delay_check
    // timer (~2.3us) to fire. Callers log AFTER priming if needed.
}

void usb_ep0_send_data(const uint32_t *data, uint32_t nbytes) {
    uint32_t nwords = (nbytes + 3) / 4;
    for (uint32_t i = 0; i < nwords; i++) {
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET + (i * 4), data[i]);
    }
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_NBYTES(nbytes)
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    VPRINTF(LOW, "MCU: EP0 IN entry (nbytes=%d) = 0x%x\n", nbytes, ep0_in);
}

void usb_ep0_send_zlp(void) {
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    VPRINTF(LOW, "MCU: EP0 IN ZLP entry = 0x%x\n", ep0_in);
}

void usb_ep0_stall(void) {
    uint32_t ep0_in  = USB_EP_ENTRY_STALL | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    uint32_t ep0_out = USB_EP_ENTRY_STALL | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
    VPRINTF(LOW, "MCU: EP0 stalled\n");
}

void usb_ep0_arm_out(void) {
    uint32_t ep0_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
}

void usb_clear_setup_bit(void) {
    uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd | USBHSD_DEVCMDSTAT_SETUP_MASK);
}

void usb_set_device_address(uint8_t addr) {
    uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    cmd = (cmd & ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK) | (addr & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK);
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
    VPRINTF(LOW, "MCU: USB device address set to %d\n", addr);
}

// -------------------------------------------------------------------------
// usb_handle_control_transfer
//
// Reads the current SETUP packet from SRAM and dispatches it by decoding
// bmRequestType (type + recipient) and bRequest. Fully implements:
//   - Standard/Device: SET_ADDRESS, GET_DESCRIPTOR(DEVICE)
// All other requests are explicitly logged and cause an EP0 stall so that
// simulation logs clearly identify unimplemented transfers.
// usb_clear_setup_bit() is always called last, per Integration Guide 4.2.4.1.1.
// Returns true if handled without stall, false otherwise.
// -------------------------------------------------------------------------
bool usb_handle_control_transfer(void) {
    usb_setup_pkt_t pkt;
    bool handled = false;

    usb_read_setup_packet(&pkt);

    uint8_t req_type  = USB_BMREQTYPE_TYPE(pkt.bmRequestType);
    uint8_t recipient = USB_BMREQTYPE_RECIPIENT(pkt.bmRequestType);

    // Clear EP0 IN interrupt before programming response
    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

    if (req_type == USB_TYPE_STANDARD) {
        if (recipient == USB_RECIP_DEVICE) {
            switch (pkt.bRequest) {
                case USB_REQ_GET_DESCRIPTOR: {
                    uint8_t desc_type = (uint8_t)((pkt.wValue >> 8) & 0xFF);
                    if (desc_type == USB_DESC_DEVICE) {
                        uint32_t nbytes = (pkt.wLength < 18u) ? pkt.wLength : 18u;
                        usb_ep0_send_data(usb_default_device_descriptor, nbytes);
                        usb_ep0_arm_out();
                        // Enable IntOnNAK_CO for status-phase detection
                        uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                        cmd |=  USBHSD_DEVCMDSTAT_INTONNAK_CO_MASK;
                        cmd &= ~USBHSD_DEVCMDSTAT_INTONNAK_CI_MASK;
                        lsu_write_32(SOC_USBHSD_DEVCMDSTAT, cmd);
                        VPRINTF(LOW, "MCU: GET_DESCRIPTOR type=0x%02x len=%d\n",
                                desc_type, pkt.wLength);
                        handled = true;
                    } else {
                        usb_ep0_stall();
                        VPRINTF(LOW, "MCU: USB Unhandled GET_DESCRIPTOR type=0x%02x"
                                " - stalling\n", desc_type);
                    }
                    break;
                }
                case USB_REQ_SET_ADDRESS: {
                    uint8_t new_addr = (uint8_t)(pkt.wValue & 0x7Fu);
                    usb_ep0_send_zlp();
                    usb_ep0_arm_out();
                    usb_set_device_address(new_addr);
                    VPRINTF(LOW, "MCU: SET_ADDRESS addr=%d\n", new_addr);
                    handled = true;
                    break;
                }
                case USB_REQ_GET_STATUS: {
                    // Standard device GET_STATUS: 2-byte status word.
                    // bit[0]=Self-Powered, bit[1]=Remote Wakeup, both 0.
                    static const uint32_t status_buf = 0x00000000u;
                    usb_ep0_send_data(&status_buf, 2);
                    usb_ep0_arm_out();
                    VPRINTF(LOW, "MCU: GET_STATUS -> 0x0000\n");
                    handled = true;
                    break;
                }
                case USB_REQ_CLEAR_FEATURE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device CLEAR_FEATURE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_FEATURE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_FEATURE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_DESCRIPTOR:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_DESCRIPTOR"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_GET_CONFIGURATION:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device GET_CONFIGURATION"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_CONFIGURATION:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_CONFIGURATION"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else if (recipient == USB_RECIP_INTERFACE) {
            switch (pkt.bRequest) {
                case USB_REQ_GET_INTERFACE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface GET_INTERFACE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_INTERFACE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface SET_INTERFACE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else if (recipient == USB_RECIP_ENDPOINT) {
            switch (pkt.bRequest) {
                case USB_REQ_SYNCH_FRAME:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Endpoint SYNCH_FRAME"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Endpoint bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else {
            VPRINTF(LOW, "MCU: USB Unhandled Standard recipient=%d bRequest=0x%02x"
                    " - stalling\n", recipient, pkt.bRequest);
            usb_ep0_stall();
        }
    } else if (req_type == USB_TYPE_CLASS) {
        VPRINTF(LOW, "MCU: USB Unhandled Class request recipient=%d bRequest=0x%02x"
                " - stalling\n", recipient, pkt.bRequest);
        usb_ep0_stall();
    } else if (req_type == USB_TYPE_VENDOR) {
        VPRINTF(LOW, "MCU: USB Unhandled Vendor request recipient=%d bRequest=0x%02x"
                " - stalling\n", recipient, pkt.bRequest);
        usb_ep0_stall();
    } else {
        VPRINTF(LOW, "MCU: USB Reserved bmRequestType=0x%02x bRequest=0x%02x"
                " - stalling\n", pkt.bmRequestType, pkt.bRequest);
        usb_ep0_stall();
    }

    // Per Integration Guide 4.2.4.1.1: clear SETUP bit last
    usb_clear_setup_bit();

    uint32_t cmd       = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    uint32_t ep0_in_rb = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);
    VPRINTF(LOW, "MCU: Post-SETUP-clear DEVCMDSTAT=0x%x EP0IN=0x%x\n", cmd, ep0_in_rb);

    return handled;
}
