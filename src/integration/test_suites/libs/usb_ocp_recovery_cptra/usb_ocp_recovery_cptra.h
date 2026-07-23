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

#ifndef USB_OCP_RECOVERY_CPTRA_H
#define USB_OCP_RECOVERY_CPTRA_H

#include <stdint.h>

#define CPTRA_USB_OCP_RECOVERY_DMA_RETRIES 3u
#define CPTRA_USB_OCP_RECOVERY_RETRY_DELAY 16u

typedef struct {
    uint32_t initial_delay_cycles;
    uint32_t words_per_service;
    uint32_t inter_service_delay_cycles;
} cptra_usb_ocp_recovery_drain_config_t;

uint64_t cptra_usb_ocp_recovery_get_base(void);

uint8_t cptra_usb_ocp_recovery_read_dword(uint64_t address,
                                          uint32_t *value);

uint8_t cptra_usb_ocp_recovery_read_dword_retry(uint64_t address,
                                                uint32_t *value);

uint8_t cptra_usb_ocp_recovery_write_dword(uint64_t address,
                                           uint32_t value);

uint32_t cptra_usb_ocp_recovery_pack_ctrl(uint8_t cms,
                                          uint8_t image_selection,
                                          uint8_t activate);

uint8_t cptra_usb_ocp_recovery_read_device_status(uint8_t *device_status);

uint8_t cptra_usb_ocp_recovery_poll_device_status(
    uint8_t target_status,
    uint32_t poll_iterations,
    uint32_t consecutive_dma_error_limit,
    uint8_t *last_status);

uint32_t cptra_usb_ocp_recovery_read_image_size_words(void);

uint8_t cptra_usb_ocp_recovery_read_fifo_status(uint8_t *fifo_status,
                                                uint32_t *write_index,
                                                uint32_t *read_index,
                                                uint32_t *fifo_size);

uint8_t cptra_usb_ocp_recovery_drain_fifo(uint32_t image_size_words,
                                          uint32_t *destination,
                                          uint32_t destination_words);

uint8_t cptra_usb_ocp_recovery_drain_fifo_configured(
    uint32_t image_size_words,
    uint32_t *destination,
    uint32_t destination_words,
    const cptra_usb_ocp_recovery_drain_config_t *config);

#endif // USB_OCP_RECOVERY_CPTRA_H
