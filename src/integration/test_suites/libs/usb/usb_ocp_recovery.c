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

#include "printf.h"
#include "usb_ocp_recovery.h"

// USB 2.0 Section 9.6.3 Table 9-10: bNumInterfaces for single-interface composite config.
#define USB_OCP_RECOVERY_CONFIG_NUM_INTERFACES 1u
// USB 2.0 Section 9.6.3 Table 9-10: bConfigurationValue, non-zero so SET_CONFIGURATION(1) matches.
#define USB_OCP_RECOVERY_CONFIG_VALUE 1u
// USB 2.0 Section 9.6.3 / 9.6.5: iConfiguration / iInterface, zero when no string descriptors provided.
#define USB_OCP_RECOVERY_STRING_INDEX_NONE 0u
// USB 2.0 Section 9.6.3 Table 9-10: bmAttributes bit 7 reserved (1), bit 6 self-powered (1), bit 5 remote wakeup (0).
// Self-powered must agree with GET_STATUS bit 0 reported by usb.c (USB 2.0 Section 9.4.5).
#define USB_OCP_RECOVERY_CONFIG_ATTRIBUTES 0xC0u
// USB 2.0 Section 9.6.3 Table 9-10: bMaxPower in 2 mA units, zero since the device draws no bus power.
#define USB_OCP_RECOVERY_MAX_POWER_2MA_UNITS 0u
// USB 2.0 Section 9.6.5 Table 9-12: bAlternateSetting, default alternate setting is 0.
#define USB_OCP_RECOVERY_ALT_SETTING 0u
// OCP Recovery v1.1 Section 8.5.2 Table 8-2: bNumEndpoints, interface uses EP0 only.
#define USB_OCP_RECOVERY_NUM_ENDPOINTS 0u
#define USB_OCP_RECOVERY_CONFIG_TOTAL_LENGTH \
    (USB_STD_CONFIGURATION_DESCRIPTOR_LENGTH \
    + USB_STD_INTERFACE_DESCRIPTOR_LENGTH \
    + USB_OCP_RECOVERY_FUNCTIONAL_DESCRIPTOR_LENGTH)

static const uint8_t usb_ocp_recovery_v1p1_config_descriptor[
    USB_OCP_RECOVERY_CONFIG_TOTAL_LENGTH] = {
    USB_STD_CONFIGURATION_DESCRIPTOR_LENGTH,
    USB_DESC_CONFIGURATION,
    (uint8_t)(sizeof(usb_ocp_recovery_v1p1_config_descriptor) & 0xFFu),
    (uint8_t)((sizeof(usb_ocp_recovery_v1p1_config_descriptor) >> 8) & 0xFFu),
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

    // OCP Recovery v1.1 Section 8.5.3: length, type, subtype, reserved,
    // maximum write size, maximum read size, and BCD specification version.
    USB_OCP_RECOVERY_FUNCTIONAL_DESCRIPTOR_LENGTH,
    USB_OCP_RECOVERY_FUNCTIONAL_DESC_TYPE,
    USB_OCP_RECOVERY_FUNCTIONAL_DESC_SUBTYPE,
    0u,
    (uint8_t)(USB_OCP_RECOVERY_MAX_WR_TRANSFER_SIZE & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_MAX_WR_TRANSFER_SIZE >> 8) & 0xFFu),
    (uint8_t)(USB_OCP_RECOVERY_MAX_RD_TRANSFER_SIZE & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_MAX_RD_TRANSFER_SIZE >> 8) & 0xFFu),
    (uint8_t)(USB_OCP_RECOVERY_BCD_VERSION & 0xFFu),
    (uint8_t)((USB_OCP_RECOVERY_BCD_VERSION >> 8) & 0xFFu),
};

// Strong override of the weak usb.c default: serves the OCP Recovery
// configuration descriptor on GET_DESCRIPTOR(CONFIGURATION).
const uint8_t *usb_get_config_descriptor(uint16_t *len) {
    if (len != NULL) {
        *len =
            (uint16_t)sizeof(usb_ocp_recovery_v1p1_config_descriptor);
    }
    return usb_ocp_recovery_v1p1_config_descriptor;
}

bool usb_ocp_recovery_program_device_id(void) {
    static const uint32_t device_id_words[] = {
        // OCP Recovery v1.1 Sec 9.2 DEVICE_ID: UUID type, no vendor string.
        // UUID bytes are 0x10 through 0x1F; bytes 18 through 23 are padding.
        0x11100002u,
        0x15141312u,
        0x19181716u,
        0x1D1C1B1Au,
        0x00001F1Eu,
        0x00000000u,
    };

    for (uint32_t i = 0u;
         i < (sizeof(device_id_words) / sizeof(device_id_words[0])); ++i) {
        const uintptr_t addr =
            SOC_USB_COMBO_RECOVERY_DEVICE_ID_0 + (i * sizeof(uint32_t));
        lsu_write_32(addr, device_id_words[i]);
        if (lsu_read_32(addr) != device_id_words[i]) {
            return false;
        }
    }
    return true;
}

bool usb_ocp_recovery_apply_capability_policy(void) {
    uint32_t prot_cap_2 =
        lsu_read_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2);

    // Do not advertise firmware-owned policy until its data is initialized.
    prot_cap_2 &=
        ~(USB_OCP_RECOVERY_UNSUPPORTED_PLATFORM_CAPS_MASK |
          RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK |
          RECOVERY_PROT_CAP_2_AGENT_CAPS_VENDOR_COMMAND_MASK);
    lsu_write_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2, prot_cap_2);

    lsu_write_32(
        SOC_USB_COMBO_RECOVERY_VENDOR,
        USB_OCP_RECOVERY_VENDOR_DEFAULT_DATA);

    prot_cap_2 |=
        RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK |
        RECOVERY_PROT_CAP_2_AGENT_CAPS_VENDOR_COMMAND_MASK;
    lsu_write_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2, prot_cap_2);

    const uint32_t readback =
        lsu_read_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2);
    return ((readback & USB_OCP_RECOVERY_UNSUPPORTED_PLATFORM_CAPS_MASK) == 0u)
        && ((readback &
             (RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK |
              RECOVERY_PROT_CAP_2_AGENT_CAPS_VENDOR_COMMAND_MASK)) ==
            (RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK |
             RECOVERY_PROT_CAP_2_AGENT_CAPS_VENDOR_COMMAND_MASK));
}

bool usb_ocp_recovery_service_capability_policy(void) {
    const uint32_t vendor_data =
        lsu_read_32(SOC_USB_COMBO_RECOVERY_VENDOR) &
        RECOVERY_VENDOR_VENDOR_DATA_MASK;

    uint32_t prot_cap_2 =
        lsu_read_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2);

    if (vendor_data == USB_OCP_RECOVERY_IDENTIFICATION_ENABLE_TOKEN) {
        prot_cap_2 |=
            RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK;
    } else if (vendor_data ==
            USB_OCP_RECOVERY_IDENTIFICATION_DISABLE_TOKEN) {
        prot_cap_2 &=
            ~RECOVERY_PROT_CAP_2_AGENT_CAPS_IDENTIFICATION_MASK;
    } else if (vendor_data == USB_OCP_RECOVERY_VENDOR_DISABLE_TOKEN) {
        prot_cap_2 &=
            ~RECOVERY_PROT_CAP_2_AGENT_CAPS_VENDOR_COMMAND_MASK;
    } else {
        return false;
    }

    lsu_write_32(SOC_USB_COMBO_RECOVERY_PROT_CAP_2, prot_cap_2);
    return true;
}

// Strong override of the weak usb.c default class-request hook.
bool usb_handle_class_request(const usb_setup_pkt_t *setup) {
    if (setup == NULL) {
        return false;
    }

    // OCP Recovery v1.1 Sec 8.5.1: the recovery class transfer SETUP
    // (bmRequestType[6:5]=Class, recipient=Interface,
    //  bRequest=OCP_RECOVERY_TRANSFER, wIndex[7:0]=REC_IFACE_NUM)
    // is intercepted by the VHDL `usb_ocp_recovery_post_sync_arb` upstream of the
    // legacy EPCS and answered by the SV-side recovery RTL directly.
    // The MCU class hook MUST NOT claim the SETUP -- if it does, the
    // legacy EPCS sends a ZLP that wins the response race and the host
    // sees an empty payload.  Returning false here lets the MCU stack
    // STALL or NAK as usual; the arbiter's response on EP0 IN takes
    // precedence on the wire because PIE's `epinfo_to_pie_*` mux is
    // owned by the arbiter while `rec_ctrl_claim` is asserted.
    //
    // Defensive: if we ever observe this hook firing for an OCP class
    // SETUP in sim, it means the arbiter is NOT claiming -- log a
    // visible marker for debug and fall through to STALL.
    if ((USB_BMREQTYPE_TYPE(setup->bmRequestType) == USB_TYPE_CLASS)
        && (USB_BMREQTYPE_RECIPIENT(setup->bmRequestType) == USB_RECIP_INTERFACE)
        && (setup->bRequest == USB_OCP_RECOVERY_TRANSFER_REQUEST)
        && ((uint8_t)(setup->wIndex & 0x00FFu) == USB_OCP_RECOVERY_IFACE_NUM)) {
        VPRINTF(LOW,
                "MCU: WARNING OCP recovery class SETUP reached MCU stack (bmReqType=0x%x bReq=0x%x wVal=0x%x wIdx=0x%x wLen=%u) -- arbiter did not claim; passing through to legacy USB stack which will STALL.\n",
                setup->bmRequestType, setup->bRequest, setup->wValue,
                setup->wIndex, setup->wLength);
    }

    return false;
}
