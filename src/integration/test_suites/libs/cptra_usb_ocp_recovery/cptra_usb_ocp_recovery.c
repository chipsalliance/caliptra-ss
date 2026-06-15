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

#include "cptra_usb_ocp_recovery.h"

#include "soc_address_map.h"
#include "soc_ifc.h"
#include "soc_ifc_ss.h"

#define CPTRA_OCP_RECOVERY_BYTE0_MASK 0xFFu

static uint8_t cptra_ocp_recovery_read_dword(uint64_t addr, uint32_t *value) {
    return soc_ifc_axi_dma_read_ahb_payload_with_status(addr, 0u, value, sizeof(*value), 0u);
}

static uint8_t cptra_ocp_recovery_write_dword(uint64_t addr, uint32_t value) {
    return soc_ifc_axi_dma_send_ahb_payload_with_status(addr, 0u, &value, sizeof(value), 0u);
}

static uint32_t cptra_ocp_recovery_pack_recovery_ctrl(uint8_t cms, uint8_t img_sel, uint8_t activate) {
    return ((uint32_t)cms << 0)
         | ((uint32_t)img_sel << 8)
         | ((uint32_t)activate << 16);
}

uint8_t cptra_ocp_recovery_read_device_status(uint8_t *device_status) {
    uint32_t device_status_word = 0u;

    if (device_status == 0) {
        return 1u;
    }

    // OCP Recovery v1.1 9.2, DEVICE_STATUS / Table 9-5: byte 0 is the device status.
    if (cptra_ocp_recovery_read_dword(SOC_USB_OCP_RECOVERY_DEVICE_STATUS_0, &device_status_word) != 0u) {
        return 1u;
    }

    *device_status = (uint8_t)(device_status_word & CPTRA_OCP_RECOVERY_BYTE0_MASK);
    return 0u;
}

uint8_t cptra_ocp_recovery_poll_device_status(uint8_t target_status, uint32_t timeout_iters) {
    uint8_t device_status;

    while (timeout_iters-- != 0u) {
        if (cptra_ocp_recovery_read_device_status(&device_status) != 0u) {
            return 1u;
        }
        if (device_status == target_status) {
            return 0u;
        }
    }

    return 1u;
}

uint32_t cptra_ocp_recovery_read_image_size_words(void) {
    uint32_t image_size_words = 0u;

    // OCP Recovery v1.1 9.2, INDIRECT_FIFO_CTRL / Table 9-13: bytes 2..5 hold Image Size in 4-byte units.
    (void)cptra_ocp_recovery_read_dword(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_1, &image_size_words);
    return image_size_words;
}

uint8_t cptra_ocp_recovery_read_fifo_status(uint8_t *fifo_status, uint32_t *write_index) {
    uint32_t fifo_status_word = 0u;
    uint32_t write_index_word = 0u;

    if ((fifo_status == 0) || (write_index == 0)) {
        return 1u;
    }

    // OCP Recovery v1.1 9.2, INDIRECT_FIFO_STATUS / Table 9-14: byte 0 is FIFO status and bytes 4..7 are Write Index.
    if (cptra_ocp_recovery_read_dword(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_0, &fifo_status_word) != 0u) {
        return 1u;
    }
    if (cptra_ocp_recovery_read_dword(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_1, &write_index_word) != 0u) {
        return 1u;
    }

    *fifo_status = (uint8_t)(fifo_status_word & CPTRA_OCP_RECOVERY_BYTE0_MASK);
    *write_index = write_index_word;
    return 0u;
}

uint8_t cptra_ocp_recovery_drain_fifo(uint32_t image_size_words, uint32_t mbox_dest_addr, uint16_t block_size) {
    uint32_t byte_count = image_size_words * sizeof(uint32_t);

    if (byte_count == 0u) {
        return 0u;
    }

    // OCP Recovery v1.1 8.2.5 and 9.2, INDIRECT_FIFO_DATA / Table 9-15: repeatedly access the fixed FIFO data register.
    return soc_ifc_axi_dma_read_mbox_payload(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_DATA,
                                             mbox_dest_addr,
                                             1u,
                                             byte_count,
                                             block_size);
}

void cptra_ocp_recovery_set_recovery_ctrl(uint8_t cms, uint8_t img_sel, uint8_t activate) {
    uint32_t ctrl_word;

    // OCP Recovery v1.1 9.2, RECOVERY_CTRL / Table 9-9: program CMS, then image selection, then activate.
    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, 0u, 0u);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_RECOVERY_CTRL, ctrl_word);

    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, img_sel, 0u);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_RECOVERY_CTRL, ctrl_word);

    ctrl_word = cptra_ocp_recovery_pack_recovery_ctrl(cms, img_sel, activate);
    (void)cptra_ocp_recovery_write_dword(SOC_USB_OCP_RECOVERY_RECOVERY_CTRL, ctrl_word);
}
