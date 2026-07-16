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

#include "usb_ocp_recovery_cptra.h"

#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"

#define CPTRA_USB_OCP_RECOVERY_BYTE0_MASK 0xFFu

static void cptra_usb_ocp_recovery_delay(uint32_t cycles)
{
    for (uint32_t iteration = 0u; iteration < cycles; ++iteration) {
        __asm__ volatile ("nop");
    }
}

uint64_t cptra_usb_ocp_recovery_get_base(void)
{
    uint64_t low;
    uint64_t high;

    low = (uint64_t)lsu_read_32(
        CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L);
    high = (uint64_t)lsu_read_32(
        CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H);
    return (high << 32) | low;
}

uint8_t cptra_usb_ocp_recovery_read_dword(uint64_t address,
                                          uint32_t *value)
{
    if (value == 0) {
        return 1u;
    }
    return soc_ifc_axi_dma_read_ahb_payload_with_status(
        address, 0u, value, sizeof(*value), 0u);
}

uint8_t cptra_usb_ocp_recovery_read_dword_retry(uint64_t address,
                                                uint32_t *value)
{
    for (uint32_t attempt = 0u;
         attempt < CPTRA_USB_OCP_RECOVERY_DMA_RETRIES;
         ++attempt) {
        if (cptra_usb_ocp_recovery_read_dword(address, value) == 0u) {
            return 0u;
        }
        cptra_usb_ocp_recovery_delay(
            CPTRA_USB_OCP_RECOVERY_RETRY_DELAY);
    }
    return 1u;
}

uint8_t cptra_usb_ocp_recovery_write_dword(uint64_t address,
                                           uint32_t value)
{
    return soc_ifc_axi_dma_send_ahb_payload_with_status(
        address, 0u, &value, sizeof(value), 0u);
}

uint32_t cptra_usb_ocp_recovery_pack_ctrl(uint8_t cms,
                                          uint8_t image_selection,
                                          uint8_t activate)
{
    return ((uint32_t)cms)
         | ((uint32_t)image_selection << 8)
         | ((uint32_t)activate << 16);
}

uint32_t cptra_usb_ocp_recovery_read_image_size_words(void)
{
    uint32_t image_size_words = 0u;

    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_CTRL_1,
            &image_size_words) != 0u) {
        return 0u;
    }
    return image_size_words;
}

uint8_t cptra_usb_ocp_recovery_read_fifo_status(uint8_t *fifo_status,
                                                uint32_t *write_index)
{
    uint32_t status_word = 0u;
    uint32_t write_index_word = 0u;

    if ((fifo_status == 0) || (write_index == 0)) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_0,
            &status_word) != 0u) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_1,
            &write_index_word) != 0u) {
        return 1u;
    }

    *fifo_status =
        (uint8_t)(status_word & CPTRA_USB_OCP_RECOVERY_BYTE0_MASK);
    *write_index = write_index_word;
    return 0u;
}

uint8_t cptra_usb_ocp_recovery_drain_fifo(uint32_t image_size_words,
                                          uint32_t *destination,
                                          uint32_t destination_words)
{
    uint32_t words_to_read;

    if ((destination == 0) || (image_size_words == 0u) ||
        (image_size_words > destination_words)) {
        return 1u;
    }

    words_to_read = image_size_words;
    for (uint32_t index = 0u; index < words_to_read; ++index) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
                &destination[index]) != 0u) {
            return 1u;
        }
    }
    return 0u;
}
