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

#ifndef CPTRA_USB_OCP_RECOVERY_H
#define CPTRA_USB_OCP_RECOVERY_H

#include <stdint.h>

#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_READY_FOR_RECOVERY_IMAGE 0x03u
#define CPTRA_OCP_RECOVERY_DEVICE_STATUS_RECOVERY_PENDING 0x04u
#define CPTRA_OCP_RECOVERY_RECOVERY_CTRL_USE_MEMORY_WINDOW_IMAGE 0x01u
#define CPTRA_OCP_RECOVERY_RECOVERY_CTRL_ACTIVATE_RECOVERY_IMAGE 0x0Fu

uint8_t cptra_ocp_recovery_read_device_status(uint8_t *device_status);
uint8_t cptra_ocp_recovery_poll_device_status(uint8_t target_status, uint32_t timeout_iters);
uint32_t cptra_ocp_recovery_read_image_size_words(void);
uint8_t cptra_ocp_recovery_read_fifo_status(uint8_t *fifo_status, uint32_t *write_index);
uint8_t cptra_ocp_recovery_drain_fifo(uint32_t image_size_words, uint32_t mbox_dest_addr, uint16_t block_size);
void cptra_ocp_recovery_set_recovery_ctrl(uint8_t cms, uint8_t img_sel, uint8_t activate);

#endif
