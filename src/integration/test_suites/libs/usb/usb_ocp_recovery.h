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
    ((uint32_t)((reg_addr) - SOC_USB_COMBO_RECOVERY_BASE_ADDR))

#define USB_OCP_RECOVERY_DEVICE_STATUS_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_DEVICE_STATUS_0)
#define USB_OCP_RECOVERY_RECOVERY_CTRL_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_RECOVERY_CTRL)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_CTRL_0)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_CTRL_1_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_CTRL_1)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_0_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_STATUS_0)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_STATUS_1_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_STATUS_1)
#define USB_OCP_RECOVERY_INDIRECT_FIFO_DATA_OFFSET \
    USB_OCP_RECOVERY_REG_OFFSET(SOC_USB_COMBO_RECOVERY_INDIRECT_FIFO_DATA)

#define USB_OCP_RECOVERY_UNSUPPORTED_PLATFORM_CAPS_MASK \
    (RECOVERY_PROT_CAP_2_AGENT_CAPS_FORCED_RECOVERY_MASK | \
     RECOVERY_PROT_CAP_2_AGENT_CAPS_MGMT_RESET_MASK | \
     RECOVERY_PROT_CAP_2_AGENT_CAPS_DEVICE_RESET_MASK | \
     RECOVERY_PROT_CAP_2_AGENT_CAPS_INTERFACE_ISOLATION_MASK | \
     RECOVERY_PROT_CAP_2_AGENT_CAPS_FLASHLESS_BOOT_MASK)

#define USB_OCP_RECOVERY_VENDOR_DEFAULT_DATA 0x5Au
#define USB_OCP_RECOVERY_IDENTIFICATION_ENABLE_TOKEN 0xA3u
#define USB_OCP_RECOVERY_IDENTIFICATION_DISABLE_TOKEN 0xA4u
#define USB_OCP_RECOVERY_VENDOR_DISABLE_TOKEN 0xA5u

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

// Compatibility configuration descriptor entry point. Consumers that require
// the OCP Recovery v1.1 Section 8.5.3 field ordering use the v1p1 entry point.
const uint8_t *usb_ocp_recovery_get_config_descriptor(uint16_t *len);

// Returns the OCP Recovery v1.1 configuration descriptor using the functional
// descriptor layout from Section 8.5.3: reserved byte at offset 3, maximum
// write/read transfer sizes at offsets 4/6, and BCD version at offset 8.
const uint8_t *usb_ocp_recovery_get_v1p1_config_descriptor(uint16_t *len);

// Apply the platform capability policy before connecting the USB device.
// Unsupported reset, recovery-mode, flashless-boot, and interface-mastering
// features are removed from the firmware-programmable PROT_CAP bitmap.
bool usb_ocp_recovery_apply_capability_policy(void);

// Program and verify the firmware-owned 24-byte DEVICE_ID register storage.
// Call this before usb_ocp_recovery_apply_capability_policy() advertises it.
bool usb_ocp_recovery_program_device_id(void);

// Apply runtime policy requests conveyed through firmware-owned Recovery
// storage. Returns true when a capability policy was updated.
bool usb_ocp_recovery_service_capability_policy(void);

// Class-request hook for OCP Recovery EP0 traffic.  The VHDL PIE arbiter
// classifies OCP_RECOVERY_TRANSFER SETUPs and routes claimed requests to the
// recovery RTL, so the MCU path must not claim them here.  This hook returns
// false on every call; if an OCP recovery request reaches the MCU stack at all,
// the implementation logs that unexpected condition and falls back to the
// legacy USB stack behavior.
bool usb_ocp_recovery_handle_class_request(const usb_setup_pkt_t *setup);

#endif // USB_OCP_RECOVERY_H
