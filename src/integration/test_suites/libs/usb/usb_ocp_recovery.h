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

#ifndef USB_OCP_RECOVERY_H
#define USB_OCP_RECOVERY_H

#include <stdint.h>

#include "soc_address_map.h"
#include "usb.h"

#define USB_OCP_RECOVERY_REG_OFFSET(reg_addr) \
    ((uint32_t)((reg_addr) - SOC_USB_OCP_RECOVERY_BASE_ADDR))

#define USB_OCP_RECOVERY_DEVICE_STATUS_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_DEVICE_STATUS_0)
#define USB_OCP_RECOVERY_RECOVERY_CTRL_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_RECOVERY_CTRL)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_0)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_1_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_1)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_0)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_1_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_1)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_DATA_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_OCP_RECOVERY_INDIRECT_FIFO_DATA)

// USB 2.0 Section 9.6.3 Table 9-10: a configuration descriptor is 9 bytes long.
#define USB_STD_CONFIGURATION_DESCRIPTOR_LENGTH 0x09u

// USB 2.0 Section 9.6.5 Table 9-12: an interface descriptor is 9 bytes long.
#define USB_STD_INTERFACE_DESCRIPTOR_LENGTH 0x09u

// OCP Recovery v1.1 Section 8.5.3: the OCP_RECOVERY_FUNCTIONAL descriptor is 10 bytes.
#define USB_OCP_RECOVERY_FUNCTIONAL_DESCRIPTOR_LENGTH 0x0Au

// OCP Recovery v1.1 Section 8.5.2: keep interface number 0 to match the SV
// default in caliptra_ss_usb_shared_cfg::ocp_recovery_iface_num.
#define USB_OCP_RECOVERY_IFACE_NUM 0u

// OCP Recovery v1.1 Section 8.5.2 and Section 8.5.4: recovery interface class code is 0xEF.
#define USB_OCP_RECOVERY_INTERFACE_CLASS 0xEFu

// OCP Recovery v1.1 Section 8.5.2 and Section 8.5.4: recovery interface subclass is 0x08.
#define USB_OCP_RECOVERY_INTERFACE_SUBCLASS 0x08u

// OCP Recovery v1.1 Section 8.5.2 and Section 8.5.4: recovery interface protocol is 0x01.
#define USB_OCP_RECOVERY_INTERFACE_PROTOCOL 0x01u

// OCP Recovery v1.1 Section 8.5.3: class-specific interface descriptor type is 0x24.
#define USB_OCP_RECOVERY_FUNCTIONAL_DESC_TYPE 0x24u

// OCP Recovery v1.1 Section 8.5.3: OCP_RECOVERY_FUNCTIONAL subtype is 0x01.
#define USB_OCP_RECOVERY_FUNCTIONAL_DESC_SUBTYPE 0x01u

// OCP Recovery v1.1 Section 8.5.1: bRequest 0x00 encodes OCP_RECOVERY_TRANSFER.
#define USB_OCP_RECOVERY_TRANSFER_REQUEST 0x00u

// OCP Recovery v1.1 Section 8.5 lines 30-35: writes must advertise at least 64 bytes.
#define USB_OCP_RECOVERY_MAX_WR_TRANSFER_SIZE 64u

// OCP Recovery v1.1 Section 8.5 lines 30-35: reads must advertise at least 64 bytes.
#define USB_OCP_RECOVERY_MAX_RD_TRANSFER_SIZE 64u

// OCP Recovery v1.1 Section 8.5.3: bcdOCPRecVersion encodes spec major.minor, so v1.1 is 0x0110.
#define USB_OCP_RECOVERY_BCD_VERSION 0x0110u

// Returns a pointer to a static composite Configuration descriptor blob that
// advertises a single Interface (OCP Recovery, class 0xEF/0x08/0x01,
// bNumEndpoints=0x00) plus one OCP_RECOVERY_FUNCTIONAL descriptor (type 0x24,
// subtype 0x01) carrying the firmware-chosen wMaxRdTransferSize /
// wMaxWrTransferSize values.
const uint8_t *usb_ocp_recovery_get_config_descriptor(uint16_t *len);

// Class-request handler proxying recovery commands. For now, returns false on
// every call (Caliptra firmware, not MCU, services the OCP register accesses
// via the PIE-level arbiter; the MCU only needs to NOT stall the class
// request before the arbiter snoops the SETUP). However, the IP-3511 EPCS
// will fire EP0_OUT on the SETUP regardless of arbiter routing - this handler
// must return true (claim the SETUP) and emit a ZLP status phase so the MCU
// firmware does not stall. The arbiter handles the actual register access.
bool usb_ocp_recovery_handle_class_request(const usb_setup_pkt_t *setup);

// Convenience installer that overrides the weak hooks in libs/usb/usb.h by
// pointing to the recovery implementations. Call once from the per-test
// firmware after boot_usb_core() and before usb_event_loop().
void usb_advertise_ocp_recovery(void);

#endif // USB_OCP_RECOVERY_H
