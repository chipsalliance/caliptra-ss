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

#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"

#define CPTRA_USB_OCP_RECOVERY_BYTE0_MASK 0xFFu

static void cptra_usb_ocp_recovery_delay(uint32_t cycles)
{
    for (uint32_t iteration = 0u; iteration < cycles; ++iteration) {
        __asm__ volatile ("nop");
    }
}

static uint8_t cptra_usb_ocp_recovery_wait_dma_idle(void)
{
    uint32_t status;

    status = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    while ((status & AXI_DMA_REG_STATUS0_BUSY_MASK) &&
           !(status & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        status = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }
    if (status & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
        return 1u;
    }
    return 0u;
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
    soc_ifc_axi_dma_arm_read_ahb_payload(
        address, 0u, value, sizeof(*value), 0u);
    soc_ifc_axi_dma_get_read_ahb_payload(value, sizeof(*value));
    return cptra_usb_ocp_recovery_wait_dma_idle();
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
    soc_ifc_axi_dma_arm_send_ahb_payload(
        address, 0u, &value, sizeof(value), 0u);
    soc_ifc_axi_dma_get_send_ahb_payload(&value, sizeof(value));
    return cptra_usb_ocp_recovery_wait_dma_idle();
}

uint32_t cptra_usb_ocp_recovery_pack_ctrl(uint8_t cms,
                                          uint8_t image_selection,
                                          uint8_t activate)
{
    return ((uint32_t)cms)
         | ((uint32_t)image_selection << 8)
         | ((uint32_t)activate << 16);
}

uint8_t cptra_usb_ocp_recovery_read_device_status(uint8_t *device_status)
{
    uint32_t status_word = 0u;

    if (device_status == 0) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_DEVICE_STATUS_0,
            &status_word) != 0u) {
        return 1u;
    }
    *device_status =
        (uint8_t)(status_word & CPTRA_USB_OCP_RECOVERY_BYTE0_MASK);
    return 0u;
}

uint8_t cptra_usb_ocp_recovery_poll_device_status(
    uint8_t target_status,
    uint32_t poll_iterations,
    uint32_t consecutive_dma_error_limit,
    uint8_t *last_status)
{
    uint8_t device_status = 0u;
    uint32_t consecutive_dma_errors = 0u;

    for (uint32_t iteration = 0u;
         iteration < poll_iterations;
         ++iteration) {
        if (cptra_usb_ocp_recovery_read_device_status(
                &device_status) != 0u) {
            consecutive_dma_errors++;
            if (consecutive_dma_errors >= consecutive_dma_error_limit) {
                if (last_status != 0) {
                    *last_status = device_status;
                }
                return 1u;
            }
            cptra_usb_ocp_recovery_delay(
                CPTRA_USB_OCP_RECOVERY_RETRY_DELAY * 4u);
            continue;
        }

        consecutive_dma_errors = 0u;
        if (device_status == target_status) {
            if (last_status != 0) {
                *last_status = device_status;
            }
            return 0u;
        }
        cptra_usb_ocp_recovery_delay(
            CPTRA_USB_OCP_RECOVERY_RETRY_DELAY);
    }

    if (last_status != 0) {
        *last_status = device_status;
    }
    return 2u;
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
    const cptra_usb_ocp_recovery_drain_config_t config = {
        .initial_delay_cycles = 0u,
        .words_per_service = image_size_words,
        .inter_service_delay_cycles = 0u,
    };

    return cptra_usb_ocp_recovery_drain_fifo_configured(
        image_size_words, destination, destination_words, &config);
}

uint8_t cptra_usb_ocp_recovery_drain_fifo_configured(
    uint32_t image_size_words,
    uint32_t *destination,
    uint32_t destination_words,
    const cptra_usb_ocp_recovery_drain_config_t *config)
{
    uint32_t words_per_service;
    uint32_t words_in_service;

    if ((destination == 0) || (image_size_words == 0u) ||
        (image_size_words > destination_words) || (config == 0)) {
        return 1u;
    }

    words_per_service = config->words_per_service;
    if (words_per_service == 0u) {
        return 1u;
    }

    cptra_usb_ocp_recovery_delay(config->initial_delay_cycles);
    words_in_service = 0u;
    for (uint32_t index = 0u; index < image_size_words; ++index) {
        if (cptra_usb_ocp_recovery_read_dword_retry(
                SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_DATA,
                &destination[index]) != 0u) {
            return 1u;
        }
        words_in_service++;
        if ((words_in_service == words_per_service) &&
            ((index + 1u) < image_size_words)) {
            cptra_usb_ocp_recovery_delay(
                config->inter_service_delay_cycles);
            words_in_service = 0u;
        }
    }
    return 0u;
}
