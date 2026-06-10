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

#include <stddef.h>

#include "usb_ocp_recovery.h"

// USB 2.0 Section 9.6.3 Table 9-10: bNumInterfaces for single-interface composite config.
#define USB_OCP_RECOVERY_CONFIG_NUM_INTERFACES 1u
// USB 2.0 Section 9.6.3 Table 9-10: bConfigurationValue, non-zero so SET_CONFIGURATION(1) matches.
#define USB_OCP_RECOVERY_CONFIG_VALUE 1u
// USB 2.0 Section 9.6.3 / 9.6.5: iConfiguration / iInterface, zero when no string descriptors provided.
#define USB_OCP_RECOVERY_STRING_INDEX_NONE 0u
// USB 2.0 Section 9.6.3 Table 9-10: bmAttributes bit 7 reserved (1), bit 6 self-powered (0=bus-powered), bit 5 remote wakeup (0).
#define USB_OCP_RECOVERY_CONFIG_ATTRIBUTES 0x80u
// USB 2.0 Section 9.6.3 Table 9-10: bMaxPower in 2 mA units, zero for bus-powered with no additional draw.
#define USB_OCP_RECOVERY_MAX_POWER_2MA_UNITS 0u
// USB 2.0 Section 9.6.5 Table 9-12: bAlternateSetting, default alternate setting is 0.
#define USB_OCP_RECOVERY_ALT_SETTING 0u
// OCP Recovery v1.1 Section 8.5.2 Table 8-2: bNumEndpoints, interface uses EP0 only.
#define USB_OCP_RECOVERY_NUM_ENDPOINTS 0u
#define USB_OCP_RECOVERY_CONFIG_TOTAL_LENGTH \
    (USB_STD_CONFIGURATION_DESCRIPTOR_LENGTH \
    + USB_STD_INTERFACE_DESCRIPTOR_LENGTH \
    + USB_OCP_RECOVERY_FUNCTIONAL_DESCRIPTOR_LENGTH)

extern const uint8_t *(*usb_config_descriptor_override)(uint16_t *len);
extern bool (*usb_class_request_override)(const usb_setup_pkt_t *setup);

static const uint8_t usb_ocp_recovery_config_descriptor[USB_OCP_RECOVERY_CONFIG_TOTAL_LENGTH] = {
    USB_STD_CONFIGURATION_DESCRIPTOR_LENGTH,
    USB_DESC_CONFIGURATION,
    (uint8_t)(sizeof(usb_ocp_recovery_config_descriptor) & 0xFFu),
    (uint8_t)((sizeof(usb_ocp_recovery_config_descriptor) >> 8) & 0xFFu),
    USB_OCP_RECOVERY_CONFIG_NUM_INTERFACES,
    USB_OCP_RECOVERY_CONFIG_VALUE,
    USB_OCP_RECOVERY_STRING_INDEX_NONE,
    USB_OCP_RECOVERY_CONFIG_ATTRIBUTES,
    USB_OCP_RECOVERY_MAX_POWER_2MA_UNITS,

    USB_STD_INTERFACE_DESCRIPTOR_LENGTH,
    USB_DESC_INTERFACE,
    USB_OCP_RECOVERY_IFACE_NUM,
    USB_OCP_RECOVERY_ALT_SETTING,
    USB_OCP_RECOVERY_NUM_ENDPOINTS,
    USB_OCP_RECOVERY_INTERFACE_CLASS,
    USB_OCP_RECOVERY_INTERFACE_SUBCLASS,
    USB_OCP_RECOVERY_INTERFACE_PROTOCOL,
    USB_OCP_RECOVERY_STRING_INDEX_NONE,

    // OCP Recovery v1.1 Section 8.5.3 Table 8-3: OCP_RECOVERY_FUNCTIONAL descriptor.
    // Byte order: bLength, bDescriptorType, bDescriptorSubType, bcdOCPRecVersion(LE),
    // wMaxWrTransferSize(LE), wMaxRdTransferSize(LE).
    USB_OCP_RECOVERY_FUNCTIONAL_DESCRIPTOR_LENGTH,
    USB_OCP_RECOVERY_FUNCTIONAL_DESC_TYPE,
    USB_OCP_RECOVERY_FUNCTIONAL_DESC_SUBTYPE,
    (uint8_t)(USB_OCP_RECOVERY_BCD_VERSION & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_BCD_VERSION >> 8) & 0xFFu),
    (uint8_t)(USB_OCP_RECOVERY_MAX_WR_TRANSFER_SIZE & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_MAX_WR_TRANSFER_SIZE >> 8) & 0xFFu),
    (uint8_t)(USB_OCP_RECOVERY_MAX_RD_TRANSFER_SIZE & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_MAX_RD_TRANSFER_SIZE >> 8) & 0xFFu),
};

const uint8_t *usb_ocp_recovery_get_config_descriptor(uint16_t *len) {
    if (len != NULL) {
        *len = (uint16_t)sizeof(usb_ocp_recovery_config_descriptor);
    }
    return usb_ocp_recovery_config_descriptor;
}

bool usb_ocp_recovery_handle_class_request(const usb_setup_pkt_t *setup) {
    if (setup == NULL) {
        return false;
    }

    if ((USB_BMREQTYPE_TYPE(setup->bmRequestType) == USB_TYPE_CLASS)
        && (USB_BMREQTYPE_RECIPIENT(setup->bmRequestType) == USB_RECIP_INTERFACE)
        && (setup->bRequest == USB_OCP_RECOVERY_TRANSFER_REQUEST)
        && ((uint8_t)(setup->wIndex & 0x00FFu) == USB_OCP_RECOVERY_IFACE_NUM)) {
        usb_ep0_send_zlp();
        return true;
    }

    return false;
}

void usb_advertise_ocp_recovery(void) {
    usb_config_descriptor_override = usb_ocp_recovery_get_config_descriptor;
    usb_class_request_override = usb_ocp_recovery_handle_class_request;
}
