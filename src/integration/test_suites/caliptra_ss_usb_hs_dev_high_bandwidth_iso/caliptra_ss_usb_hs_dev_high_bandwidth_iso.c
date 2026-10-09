// SPDX-License-Identifier: Apache-2.0
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
// Arms one 3072-byte high-bandwidth ISO IN descriptor with packet-distinct
// data. The UVM host intentionally lets SOF interrupt the service interval.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 100000u
#define USB_EXPECTED_TRANSFERS 7u
#define USB_HB_ISO_PACKET_BYTES 1024u
#define USB_HB_ISO_TRANSACTIONS 3u
#define USB_HB_ISO_TRANSFER_BYTES \
    (USB_HB_ISO_PACKET_BYTES * USB_HB_ISO_TRANSACTIONS)
#define USB_HB_ISO_IN_BUF_OFFSET 0x1000u
#define USB_EP_LIST_EP2_IN_OFFSET 0x028u
#define USB_SOF_ERROR_WAIT_ITERS 100000u
#define USB_ERROR_PACKET_UNEXPECTED 3u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

static uint8_t expected_byte(uint32_t byte_index) {
    uint32_t packet_index = byte_index / USB_HB_ISO_PACKET_BYTES;
    uint32_t packet_offset = byte_index % USB_HB_ISO_PACKET_BYTES;
    uint32_t packet_base;

    if (packet_index == 0u) {
        packet_base = 0x10u;
    } else if (packet_index == 1u) {
        packet_base = 0x50u;
    } else {
        packet_base = 0x90u;
    }
    return (uint8_t)(packet_base + packet_offset);
}

static void arm_high_bandwidth_iso_in(void) {
    uint32_t descriptor;

    for (uint32_t offset = 0;
         offset < USB_HB_ISO_TRANSFER_BYTES;
         offset += 4u) {
        uint32_t data_word =
            ((uint32_t)expected_byte(offset + 0u) << 0) |
            ((uint32_t)expected_byte(offset + 1u) << 8) |
            ((uint32_t)expected_byte(offset + 2u) << 16) |
            ((uint32_t)expected_byte(offset + 3u) << 24);
        lsu_write_32(
            USB_DMA_BASE_ADDR + USB_HB_ISO_IN_BUF_OFFSET + offset,
            data_word);
    }

    descriptor =
        USB_EP_ENTRY_ACTIVE |
        USB_EP_ENTRY_TYPE_PERIODIC |
        USB_EP_ENTRY_RF_ISO |
        USB_EP_ENTRY_NBYTES(USB_HB_ISO_TRANSFER_BYTES) |
        USB_EP_ENTRY_ADDR(USB_HB_ISO_IN_BUF_OFFSET);
    lsu_write_32(
        USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_OFFSET,
        descriptor);
    VPRINTF(
        LOW,
        "MCU: Armed EP2 IN high-bandwidth ISO descriptor=0x%x bytes=%d buffer=0x%x\n",
        descriptor,
        USB_HB_ISO_TRANSFER_BYTES,
        USB_HB_ISO_IN_BUF_OFFSET);
}

void main(void) {
    uint32_t transfers_handled;
    uint32_t descriptor = 0;
    uint32_t remaining = USB_HB_ISO_TRANSFER_BYTES;
    uint32_t active = 1u;

    VPRINTF(
        LOW,
        "========================================\n"
        "MCU: USB HS high-bandwidth ISO IN replay\n"
        "========================================\n");

    boot_usb_core_hub();
    usb_hub_connect();
    VPRINTF(
        LOW,
        "MCU: Hub and USBDC0 initialized; entering USB enumeration loop\n");

    transfers_handled =
        usb_event_loop(USB_POLL_TIMEOUT, USB_EXPECTED_TRANSFERS);
    if (transfers_handled < USB_EXPECTED_TRANSFERS) {
        VPRINTF(
            LOW,
            "MCU: Enumeration timeout: handled %d/%d transfers\n",
            transfers_handled,
            USB_EXPECTED_TRANSFERS);
        csr_write_mpmc_halt();
        return;
    }

    arm_high_bandwidth_iso_in();

    for (uint32_t wait = 0;
         wait < USB_SOF_ERROR_WAIT_ITERS;
         wait++) {
        uint32_t error_code =
            (lsu_read_32(USB_DEV_INFO) >> 11) & 0xfu;
        descriptor = lsu_read_32(
            USB_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_OFFSET);
        remaining = (descriptor >> 11) & 0x7fffu;
        active = (descriptor >> 31) & 1u;
        if ((error_code == USB_ERROR_PACKET_UNEXPECTED) ||
            ((active == 0u) && (remaining == 0u))) {
            break;
        }
    }

    VPRINTF(
        LOW,
        "MCU: EP2 IN descriptor after host transfer=0x%x active=%d remaining=%d\n",
        descriptor,
        active,
        remaining);
    if ((active == 0u) && (remaining == 0u)) {
        VPRINTF(
            LOW,
            "MCU: High-bandwidth ISO IN progress preserved - PASS\n");
    } else {
        VPRINTF(
            LOW,
            "MCU: High-bandwidth ISO IN progress lost after SOF - FAIL\n");
    }
    csr_write_mpmc_halt();
}
