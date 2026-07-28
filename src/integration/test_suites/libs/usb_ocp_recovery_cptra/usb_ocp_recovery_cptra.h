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

// -------------------------------------------------------------------------
// Access-semantics CPUif and firmware-synchronization helpers.
//
// cptra_usb_ocp_recovery_signal_state
//   Writes a firmware state code and optional data byte into
//   SS_GENERIC_FW_EXEC_CTRL_0[10:3] and [18:11] respectively.
//   The SS top exports these bits at fw_exec_ctrl_o[7:0] and [15:8].
//   Bits [2:0] are left zero; they are not exported by the SS top.
//   May be called from any test that needs to publish a handshake state.
//
// cptra_usb_ocp_recovery_read_device_status_word
//   Reads the full 32-bit DEVICE_STATUS_0 word via DMA (with retry).
//   PROT_ERROR occupies bits [15:8] of the returned word.
//   This read is non-destructive with respect to source-qualified clear:
//   only Recovery Agent USB reads clear PROT_ERROR per OCP Recovery v1.1
//   Sec 9.1.
//
// cptra_usb_ocp_recovery_read_device_reset / write_device_reset
//   Read/write the DEVICE_RESET register word via DMA (with retry).
//
// cptra_usb_ocp_recovery_read_recovery_ctrl / write_recovery_ctrl
//   Read/write the RECOVERY_CTRL register word via DMA (with retry).
//
// cptra_usb_ocp_recovery_read_indirect_fifo_ctrl / write_indirect_fifo_ctrl
//   Read/write the INDIRECT_FIFO_CTRL_0 register word via DMA (with retry).
//
// cptra_usb_ocp_recovery_read_caliptra_status
//   Read the CALIPTRA_STATUS register word via DMA (with retry).
// -------------------------------------------------------------------------

void cptra_usb_ocp_recovery_signal_state(uint8_t state, uint8_t data);

uint8_t cptra_usb_ocp_recovery_read_device_status_word(uint32_t *word);

uint8_t cptra_usb_ocp_recovery_read_device_reset(uint32_t *val);
uint8_t cptra_usb_ocp_recovery_write_device_reset(uint32_t val);

uint8_t cptra_usb_ocp_recovery_read_recovery_ctrl(uint32_t *val);
uint8_t cptra_usb_ocp_recovery_write_recovery_ctrl(uint32_t val);

uint8_t cptra_usb_ocp_recovery_read_indirect_fifo_ctrl(uint32_t *val);
uint8_t cptra_usb_ocp_recovery_write_indirect_fifo_ctrl(uint32_t val);

uint8_t cptra_usb_ocp_recovery_read_caliptra_status(uint32_t *val);

#endif // USB_OCP_RECOVERY_CPTRA_H
