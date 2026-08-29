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

    for (uint32_t poll = 0u;
         poll < CPTRA_USB_OCP_RECOVERY_DMA_IDLE_POLLS;
         ++poll) {
        status = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
        if (status & AXI_DMA_REG_STATUS0_ERROR_MASK) {
            lsu_write_32(
                CLP_AXI_DMA_REG_CTRL,
                AXI_DMA_REG_CTRL_FLUSH_MASK);
            return 1u;
        }
        if (!(status & AXI_DMA_REG_STATUS0_BUSY_MASK)) {
            return 0u;
        }
    }
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
    return 1u;
}

static uint8_t cptra_usb_ocp_recovery_wait_dma_fifo(
    uint8_t wait_for_data)
{
    uint32_t capacity;
    uint32_t depth;
    uint32_t status;

    capacity = (lsu_read_32(CLP_AXI_DMA_REG_CAP) &
        AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_MASK) >>
        AXI_DMA_REG_CAP_FIFO_MAX_DEPTH_LOW;
    if (capacity == 0u) {
        return 1u;
    }

    for (uint32_t poll = 0u;
         poll < CPTRA_USB_OCP_RECOVERY_DMA_IDLE_POLLS;
         ++poll) {
        status = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
        if (status & AXI_DMA_REG_STATUS0_ERROR_MASK) {
            lsu_write_32(
                CLP_AXI_DMA_REG_CTRL,
                AXI_DMA_REG_CTRL_FLUSH_MASK);
            return 1u;
        }
        depth = (status & AXI_DMA_REG_STATUS0_FIFO_DEPTH_MASK) >>
            AXI_DMA_REG_STATUS0_FIFO_DEPTH_LOW;
        if ((wait_for_data && (depth != 0u)) ||
            (!wait_for_data && (depth < capacity))) {
            return 0u;
        }
    }

    lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
    return 1u;
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
    uint32_t control;

    if (value == 0) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_wait_dma_idle() != 0u) {
        return 1u;
    }

    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L, (uint32_t)address);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (uint32_t)(address >> 32));
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, sizeof(*value));
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, 0u);
    control = AXI_DMA_REG_CTRL_GO_MASK |
        (axi_dma_rd_route_AHB_FIFO << AXI_DMA_REG_CTRL_RD_ROUTE_LOW) |
        (axi_dma_wr_route_DISABLE << AXI_DMA_REG_CTRL_WR_ROUTE_LOW);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, control);

    if (cptra_usb_ocp_recovery_wait_dma_fifo(1u) != 0u) {
        return 1u;
    }
    *value = lsu_read_32(CLP_AXI_DMA_REG_READ_DATA);
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
    uint32_t control;

    if (cptra_usb_ocp_recovery_wait_dma_idle() != 0u) {
        return 1u;
    }

    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L, (uint32_t)address);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (uint32_t)(address >> 32));
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, sizeof(value));
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, 0u);
    control = AXI_DMA_REG_CTRL_GO_MASK |
        (axi_dma_rd_route_DISABLE << AXI_DMA_REG_CTRL_RD_ROUTE_LOW) |
        (axi_dma_wr_route_AHB_FIFO << AXI_DMA_REG_CTRL_WR_ROUTE_LOW);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, control);

    if (cptra_usb_ocp_recovery_wait_dma_fifo(0u) != 0u) {
        return 1u;
    }
    lsu_write_32(CLP_AXI_DMA_REG_WRITE_DATA, value);
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

uint8_t cptra_usb_ocp_recovery_write_device_status(uint8_t device_status,
                                                    uint16_t reason_code)
{
    uint32_t status_word = (uint32_t)device_status
                         | ((uint32_t)reason_code << 16);

    return cptra_usb_ocp_recovery_write_dword(
        SOC_USB_OCP_RECOVERY_REG_DEVICE_STATUS_0, status_word);
}

uint8_t cptra_usb_ocp_recovery_write_recovery_status(
    uint8_t recovery_status, uint8_t image_index, uint8_t vendor_status)
{
    uint32_t status_word = ((uint32_t)recovery_status & 0x0Fu)
                         | (((uint32_t)image_index & 0x0Fu) << 4)
                         | ((uint32_t)vendor_status << 8);

    return cptra_usb_ocp_recovery_write_dword(
        SOC_USB_OCP_RECOVERY_REG_RECOVERY_STATUS, status_word);
}

uint8_t cptra_usb_ocp_recovery_wait_payload_available(uint32_t poll_iterations)
{
    for (uint32_t poll = 0u; poll < poll_iterations; ++poll) {
        if (lsu_read_32(CLP_AXI_DMA_REG_STATUS0)
            & AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK) {
            return 0u;
        }
        cptra_usb_ocp_recovery_delay(CPTRA_USB_OCP_RECOVERY_RETRY_DELAY);
    }
    return 1u;
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
                                                uint32_t *write_index,
                                                uint32_t *read_index,
                                                uint32_t *fifo_size)
{
    uint32_t status_word = 0u;
    uint32_t write_index_word = 0u;
    uint32_t read_index_word = 0u;
    uint32_t fifo_size_word = 0u;

    if ((fifo_status == 0) || (write_index == 0) ||
        (read_index == 0) || (fifo_size == 0)) {
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
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_2,
            &read_index_word) != 0u) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_STATUS_3,
            &fifo_size_word) != 0u) {
        return 1u;
    }

    *fifo_status =
        (uint8_t)(status_word & CPTRA_USB_OCP_RECOVERY_BYTE0_MASK);
    *write_index = write_index_word;
    *read_index = read_index_word;
    *fifo_size = fifo_size_word;
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

// ==========================================================================
// Access-semantics CPUif and firmware-synchronization helpers.
// ==========================================================================

// Writes firmware state code and data into SS_GENERIC_FW_EXEC_CTRL_0.
// State occupies bits [10:3], data occupies bits [18:11].
// The SS top exports [127:3] as fw_exec_ctrl_o[124:0], so the sequence
// observes state at [7:0] and data at [15:8] of that output.
void cptra_usb_ocp_recovery_signal_state(uint8_t state, uint8_t data)
{
    uint32_t val = ((uint32_t)state << 3) | ((uint32_t)data << 11);
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, val);
}

void cptra_usb_ocp_recovery_signal_state_generation(uint8_t state,
                                                    uint8_t data,
                                                    uint16_t generation)
{
    uint32_t ctrl0;
    uint32_t ctrl1;

    ctrl0 = ((uint32_t)state << 3)
          | ((uint32_t)data << 11)
          | (((uint32_t)generation & 0x1FFFu) << 19);
    ctrl1 = ((uint32_t)generation >> 13);

    // Invalidate the prior state before changing generation high bits. Without
    // this transition, a generation separated by 8192 could momentarily pair
    // its new high bits with a repeated prior state and data value.
    lsu_write_32(
        CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,
        ((uint32_t)CPTRA_USB_OCP_FW_STATE_COMMAND_BUSY << 3)
            | (((uint32_t)generation & 0x1FFFu) << 19));
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1, ctrl1);
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, ctrl0);
}

// Reads the full DEVICE_STATUS_0 word. PROT_ERROR is at bits [15:8].
// CPUif reads are non-destructive for this source-qualified check:
// only Recovery Agent USB reads clear PROT_ERROR.
uint8_t cptra_usb_ocp_recovery_read_device_status_word(uint32_t *word)
{
    if (word == 0) {
        return 1u;
    }
    return cptra_usb_ocp_recovery_read_dword_retry(
        SOC_USB_OCP_RECOVERY_REG_DEVICE_STATUS_0, word);
}

uint8_t cptra_usb_ocp_recovery_read_device_reset(uint32_t *val)
{
    if (val == 0) {
        return 1u;
    }
    return cptra_usb_ocp_recovery_read_dword_retry(
        SOC_USB_OCP_RECOVERY_REG_DEVICE_RESET, val);
}

uint8_t cptra_usb_ocp_recovery_write_device_reset(uint32_t val)
{
    return cptra_usb_ocp_recovery_write_dword(
        SOC_USB_OCP_RECOVERY_REG_DEVICE_RESET, val);
}

uint8_t cptra_usb_ocp_recovery_read_recovery_ctrl(uint32_t *val)
{
    if (val == 0) {
        return 1u;
    }
    return cptra_usb_ocp_recovery_read_dword_retry(
        SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL, val);
}

uint8_t cptra_usb_ocp_recovery_write_recovery_ctrl(uint32_t val)
{
    return cptra_usb_ocp_recovery_write_dword(
        SOC_USB_OCP_RECOVERY_REG_RECOVERY_CTRL, val);
}

uint8_t cptra_usb_ocp_recovery_read_indirect_fifo_ctrl(uint32_t *val)
{
    if (val == 0) {
        return 1u;
    }
    return cptra_usb_ocp_recovery_read_dword_retry(
        SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_CTRL_0, val);
}

uint8_t cptra_usb_ocp_recovery_write_indirect_fifo_ctrl(uint32_t val)
{
    return cptra_usb_ocp_recovery_write_dword(
        SOC_USB_OCP_RECOVERY_REG_INDIRECT_FIFO_CTRL_0, val);
}

uint8_t cptra_usb_ocp_recovery_read_path_disable(uint8_t *disabled)
{
    uint32_t value;

    if (disabled == 0) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_dword_retry(
            SOC_USB_OCP_RECOVERY_REG_CALIPTRA_CTRL, &value) != 0u) {
        return 1u;
    }
    *disabled = (value &
        USB_OCP_RECOVERY_REG_CALIPTRA_CTRL_OCP_PATH_DISABLE_MASK) != 0u;
    return 0u;
}

uint8_t cptra_usb_ocp_recovery_set_path_disable(uint8_t disabled)
{
    uint32_t value;
    uint8_t observed;

    value = disabled ?
        USB_OCP_RECOVERY_REG_CALIPTRA_CTRL_OCP_PATH_DISABLE_MASK : 0u;
    if (cptra_usb_ocp_recovery_write_dword(
            SOC_USB_OCP_RECOVERY_REG_CALIPTRA_CTRL, value) != 0u) {
        return 1u;
    }
    if (cptra_usb_ocp_recovery_read_path_disable(&observed) != 0u) {
        return 1u;
    }
    return observed == (disabled != 0u) ? 0u : 2u;
}

void cptra_usb_ocp_recovery_read_fw_command(uint32_t *command_word,
                                            uint32_t *command_magic)
{
    if (command_word != 0) {
        *command_word =
            lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
    }
    if (command_magic != 0) {
        *command_magic =
            lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1);
    }
}

uint8_t cptra_usb_ocp_recovery_read_caliptra_status(uint32_t *val)
{
    if (val == 0) {
        return 1u;
    }
    return cptra_usb_ocp_recovery_read_dword_retry(
        SOC_USB_OCP_RECOVERY_REG_CALIPTRA_STATUS, val);
}
