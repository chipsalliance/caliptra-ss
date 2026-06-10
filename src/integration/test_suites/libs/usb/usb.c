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

// Shadow of the staged device-address (DEVCMDSTAT[6:0]).
//
// Hardware quirk (IP-XXX-3511): DEVCMDSTAT[6:0] reads return the LIVE
// `reg_dev_addr`, but writes always update the staged `reg_dev_addr_tmp` which
// is only committed to LIVE on the next `setup_received`. Any naive RMW of
// DEVCMDSTAT after `usb_set_device_address(N)` (e.g., `usb_clear_setup_bit()`)
// will read LIVE (still 0) and write that back into TMP, clobbering the
// staged address. The DUT then never enables the new address and goes silent
// on the host's first SETUP@addr=N. See
// `copilot/research/addr1_silence_fsdb_rca_pkg127.md` for the FSDB evidence.
//
// Fix: every RMW write to DEVCMDSTAT goes through usb_devcmdstat_write() which
// re-substitutes this shadow into bits[6:0] before writeback, preserving the
// staged address regardless of call order.
static uint8_t usb_dev_addr_shadow = 0;

// Shadow of the currently-selected configuration value (USB 2.0 §9.4.7).
// Updated by SET_CONFIGURATION; returned by GET_CONFIGURATION; cleared on
// bus reset (device returns to Default state per USB 2.0 §9.1.1.3).
static uint8_t usb_current_config = 0;
static uint32_t usb_transfers_handled = 0;

const uint8_t *(*usb_config_descriptor_override)(uint16_t *len) = 0;
bool (*usb_class_request_override)(const usb_setup_pkt_t *setup) = 0;

static void usb_devcmdstat_write(uint32_t val) {
    val = (val & ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK)
        | (usb_dev_addr_shadow & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK);
    lsu_write_32(SOC_USBHSD_DEVCMDSTAT, val);
}

__attribute__((weak))
const uint8_t *usb_get_config_descriptor(uint16_t *len) {
    if (usb_config_descriptor_override != 0) {
        return usb_config_descriptor_override(len);
    }

    if (len != 0) {
        *len = 0;
    }

    return 0;
}

__attribute__((weak))
bool usb_handle_class_request(const usb_setup_pkt_t *setup) {
    if (usb_class_request_override != 0) {
        return usb_class_request_override(setup);
    }

    return false;
}

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
    // Bus reset returns device address to 0 per USB spec; update shadow so all
    // subsequent DEVCMDSTAT RMW writes carry the reset address.
    usb_dev_addr_shadow = 0;
    // USB 2.0 §9.1.1.3: reset returns the device to the Default state with
    // no configuration selected. Mirror that in the firmware shadow so a
    // subsequent GET_CONFIGURATION reports 0 until SET_CONFIGURATION runs.
    usb_current_config = 0;
    // Clear DRES_C (W1C)
    usb_devcmdstat_write(cmd | USBHSD_DEVCMDSTAT_DRES_C_MASK);
    usb_ep0_reinit();
    // Reset device address to 0 per USB spec
    cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    cmd &= ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK;
    usb_devcmdstat_write(cmd);
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
    const uint8_t *byte_data = (const uint8_t *)data;
    uint32_t nwords = (nbytes + 3) / 4;

    for (uint32_t i = 0; i < nwords; i++) {
        uint32_t word = 0;
        uint32_t base = i * 4;

        for (uint32_t byte = 0; byte < 4; byte++) {
            uint32_t idx = base + byte;
            uint8_t val = (idx < nbytes) ? byte_data[idx] : 0u;
            word |= ((uint32_t)val) << (byte * 8);
        }

        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET + (i * 4), word);
    }

    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_NBYTES(nbytes)
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    // NOTE: VPRINTF intentionally omitted from EP0 IN arming hot-path.
    // Host VIP only gives ~5us between SETUP-ACK and giving up on IN polling;
    // adding logging here delays the arm beyond that window for back-to-back
    // SETUPs (e.g. GET_STATUS following GET_DESCRIPTOR).
}

void usb_ep0_send_zlp(void) {
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
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
    usb_devcmdstat_write(cmd | USBHSD_DEVCMDSTAT_SETUP_MASK);
}

void usb_set_device_address(uint8_t addr) {
    usb_dev_addr_shadow = (uint8_t)(addr & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK);
    uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    usb_devcmdstat_write(cmd);
}

void usb_dump_state(const char *tag) {
    const char *label = (tag != 0) ? tag : "state";
    uint32_t reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
    uint32_t intstat = lsu_read_32(SOC_USBHSD_INTSTAT);
    uint32_t ep0_out = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
    uint32_t ep0_in = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

    VPRINTF(LOW,
            "MCU: USB %s DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
            label, reg_data, intstat, ep0_out, ep0_in, (int)usb_transfers_handled);
}

void usb_event_loop(uint32_t max_iters) {
    for (uint32_t poll_count = 0; (max_iters == 0u) || (poll_count < max_iters); poll_count++) {
        uint32_t reg_data;

        if (poll_count == 0u) {
            usb_transfers_handled = 0u;
        }

        usb_handle_bus_reset();

        reg_data = lsu_read_32(SOC_USBHSD_INTSTAT);
        if ((reg_data & USBHSD_INTSTAT_DEV_INT_MASK) != 0u) {
            uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if ((cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) != 0u) {
                usb_handle_bus_reset();
            }
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        if ((reg_data & USBHSD_INTSTAT_EP0OUT_MASK) != 0u) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);

            if ((lsu_read_32(SOC_USBHSD_DEVCMDSTAT) & USBHSD_DEVCMDSTAT_SETUP_MASK) != 0u) {
                (void)usb_handle_control_transfer();
                usb_transfers_handled++;
            }
        }

        if ((USB_EVENT_LOOP_DIAG_PERIOD != 0u)
            && (poll_count > 0u)
            && ((poll_count % USB_EVENT_LOOP_DIAG_PERIOD) == 0u)) {
            VPRINTF(LOW,
                    "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
                    (int)poll_count,
                    lsu_read_32(SOC_USBHSD_DEVCMDSTAT),
                    lsu_read_32(SOC_USBHSD_INTSTAT),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008),
                    (int)usb_transfers_handled);
        }

        // mcu_sleep removed from poll loop: at 25ns/iter it costs ~3-4us
        // between consecutive polls, which exceeds the host VIP IN-retry
        // budget after a SETUP ACK. Busy-poll keeps SETUP detection within
        // 1 us of the EP0OUT interrupt.
    }
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
                    const uint8_t *config_desc = 0;
                    uint16_t config_len = 0;
                    uint32_t nbytes = 0;
                    bool have_descriptor = false;

                    if (desc_type == USB_DESC_DEVICE) {
                        nbytes = (pkt.wLength < 18u) ? pkt.wLength : 18u;
                        usb_ep0_send_data(usb_default_device_descriptor, nbytes);
                        have_descriptor = true;
                    } else if (desc_type == USB_DESC_CONFIGURATION) {
                        config_desc = usb_get_config_descriptor(&config_len);
                        if ((config_desc != 0) && (config_len != 0u)) {
                            nbytes = (pkt.wLength < config_len) ? pkt.wLength : config_len;
                            usb_ep0_send_data((const uint32_t *)config_desc, nbytes);
                            have_descriptor = true;
                        }
                    }

                    if (have_descriptor) {
                        usb_ep0_arm_out();
                        // Enable IntOnNAK_CO for status-phase detection
                        uint32_t cmd = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
                        cmd |= USBHSD_DEVCMDSTAT_INTONNAK_CO_MASK;
                        cmd &= ~USBHSD_DEVCMDSTAT_INTONNAK_CI_MASK;
                        usb_devcmdstat_write(cmd);
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
                    handled = true;
                    break;
                }
                case USB_REQ_GET_STATUS: {
                    // Standard device GET_STATUS: 2-byte status word.
                    // bit[0]=Self-Powered, bit[1]=Remote Wakeup, both 0.
                    static const uint32_t status_buf = 0x00000000u;
                    usb_ep0_send_data(&status_buf, 2);
                    usb_ep0_arm_out();
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
                case USB_REQ_GET_CONFIGURATION: {
                    // Standard device GET_CONFIGURATION: 1-byte current config.
                    // Returns the value most recently set by SET_CONFIGURATION,
                    // or 0 if the device is still in Address state.
                    uint32_t cfg_buf = (uint32_t)usb_current_config;
                    usb_ep0_send_data(&cfg_buf, 1);
                    usb_ep0_arm_out();
                    handled = true;
                    break;
                }
                case USB_REQ_SET_CONFIGURATION: {
                    // Standard device SET_CONFIGURATION: wValue low byte is
                    // the configuration value. The device descriptor declares
                    // bNumConfigurations=1, so accept 0 (unconfigure) or 1
                    // and stall any other value per USB 2.0 §9.4.7.
                    uint8_t new_cfg = (uint8_t)(pkt.wValue & 0xFFu);
                    if (new_cfg <= 1u) {
                        usb_current_config = new_cfg;
                        usb_ep0_send_zlp();
                        usb_ep0_arm_out();
                        handled = true;
                    } else {
                        VPRINTF(LOW, "MCU: USB SET_CONFIGURATION invalid value=%d"
                                " - stalling\n", new_cfg);
                        usb_ep0_stall();
                    }
                    break;
                }
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
        if (usb_handle_class_request(&pkt)) {
            handled = true;
        } else {
            VPRINTF(LOW, "MCU: USB Unhandled Class request recipient=%d bRequest=0x%02x"
                    " - stalling\n", recipient, pkt.bRequest);
            usb_ep0_stall();
        }
    } else if (req_type == USB_TYPE_VENDOR) {
        VPRINTF(LOW, "MCU: USB Unhandled Vendor request recipient=%d bRequest=0x%02x"
                " - stalling\n", recipient, pkt.bRequest);
        usb_ep0_stall();
    } else {
        VPRINTF(LOW, "MCU: USB Reserved bmRequestType=0x%02x bRequest=0x%02x"
                " - stalling\n", pkt.bmRequestType, pkt.bRequest);
        usb_ep0_stall();
    }

    // Per Integration Guide 4.2.4.1.1: clear SETUP bit after arming response.
    // This must happen quickly: host VIP retries IN tokens for only ~5us
    // before giving up and sending the next SETUP, which will be NAKed by
    // the DUT IP unless the SETUP bit is already cleared.
    usb_clear_setup_bit();

    // Post-handler diagnostic logging. Outside the critical timing window
    // (after EP arming + SETUP-bit clear) so it does not delay the response.
    VPRINTF(LOW, "MCU: SETUP handled bmReqType=0x%02x bReq=0x%02x wVal=0x%04x"
            " wIdx=0x%04x wLen=%d handled=%d\n",
            pkt.bmRequestType, pkt.bRequest, pkt.wValue,
            pkt.wIndex, pkt.wLength, (int)handled);
    if (pkt.bRequest == USB_REQ_SET_ADDRESS) {
        VPRINTF(LOW, "MCU: SET_ADDRESS addr=%d\n", (int)(pkt.wValue & 0x7Fu));
    }

    return handled;
}

// The MCU build currently pulls only usb.o from libs/usb. Include the
// recovery helper implementation here so its symbols link automatically
// without requiring per-test makefile edits.
#include "usb_ocp_recovery.c"
