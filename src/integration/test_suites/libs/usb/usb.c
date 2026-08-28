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

#include "usb.h"

// Shadow of the staged device-address (DEVCMDSTAT[6:0]).
//
// Hardware quirk (IP-XXX-3511): DEVCMDSTAT[6:0] reads return the LIVE
// `reg_dev_addr`, but writes always update the staged `reg_dev_addr_tmp` which
// is only committed to LIVE on the next `setup_received`. Any naive RMW of
// DEVCMDSTAT after `usb_set_device_address(N)` (e.g., `usb_clear_setup_bit()`)
// will read LIVE (still 0) and write that back into TMP, clobbering the
// staged address. The DUT then never enables the new address and goes silent
// on the host's first SETUP@addr=N. See
// `copilot/research/addr1_silence_fsdb_rca_pkg127.md` for the FSDB evidence.
//
// Fix: every RMW write to DEVCMDSTAT goes through usb_devcmdstat_write() which
// re-substitutes this shadow into bits[6:0] before writeback, preserving the
// staged address regardless of call order.
static uint8_t usb_dev_addr_shadow = 0;

// Shadow of the currently-selected configuration value (USB 2.0 §9.4.7).
// Updated by SET_CONFIGURATION; returned by GET_CONFIGURATION; cleared on
// bus reset (device returns to Default state per USB 2.0 §9.1.1.3).
static uint8_t usb_current_config = 0;

static void usb_devcmdstat_write(uint32_t val) {
    val = (val & ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK)
        | (usb_dev_addr_shadow & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK);
    lsu_write_32(USB_DEV0_DEVCMDSTAT, val);
}

// Minimal USB 2.0 device descriptor (18 bytes, packed as uint32_t for SRAM writes)
const uint32_t usb_default_device_descriptor[5] = {
    0x00020112,  // bLength=18, bDescType=1(DEVICE), bcdUSB=0x0200 (LE)
    0x40000000,  // bDevClass=0, bDevSubClass=0, bDevProto=0, bMaxPktSz0=64
    0x00000000,  // idVendor=0x0000, idProduct=0x0000
    0x00000100,  // bcdDevice=0x0100, iManufacturer=0
    0x01000000   // iProduct=0, iSerialNumber=0, bNumConfigurations=1
};

// -------------------------------------------------------------------------
// Minimal HUB RAM descriptor images.
//
// These are deliberately minimal (18-byte hub device descriptor, single
// configuration with a single interrupt-IN endpoint for the hub status
// change pipe, standard hub class descriptor for a 2-port non-removable
// hub, device qualifier and other-speed-configuration descriptors so a
// HS host's mandatory GET_DESCRIPTOR(DEVICE_QUALIFIER) request succeeds).
// Byte layout matches USB 2.0 spec tables 9-8 (device), 9-10 (config),
// 11-13 (hub class, USB 2.0 spec section 11.23.2.1), 9-9 (qualifier).
// -------------------------------------------------------------------------

// Hub Device Descriptor (18 bytes, bDeviceClass=0x09=HUB)
static const uint8_t usb_hub_device_descriptor[18] = {
    0x12, 0x01,             // bLength=18, bDescriptorType=DEVICE
    0x00, 0x02,             // bcdUSB = 0x0200
    0x09, 0x00, 0x00,       // bDeviceClass=HUB, bDeviceSubClass=0, bDeviceProtocol=0
    0x40,                   // bMaxPacketSize0 = 64
    0x00, 0x00,             // idVendor = 0x0000
    0x00, 0x00,             // idProduct = 0x0000
    0x00, 0x01,             // bcdDevice = 0x0100
    0x00, 0x00, 0x00,       // iManufacturer, iProduct, iSerialNumber = 0
    0x01                    // bNumConfigurations = 1
};

// Configuration Descriptor + Interface + Endpoint (9+9+7 = 25 bytes)
static const uint8_t usb_hub_config_descriptor[25] = {
    // Configuration Descriptor
    0x09, 0x02,             // bLength=9, bDescriptorType=CONFIGURATION
    0x19, 0x00,             // wTotalLength = 25
    0x01,                   // bNumInterfaces = 1
    0x01,                   // bConfigurationValue = 1
    0x00,                   // iConfiguration = 0
    0xE0,                   // bmAttributes: self-powered, remote-wakeup
    0x00,                   // bMaxPower = 0 (self-powered)
    // Interface Descriptor
    0x09, 0x04,             // bLength=9, bDescriptorType=INTERFACE
    0x00,                   // bInterfaceNumber = 0
    0x00,                   // bAlternateSetting = 0
    0x01,                   // bNumEndpoints = 1
    0x09, 0x00, 0x00,       // bInterfaceClass=HUB, SubClass=0, Protocol=0
    0x00,                   // iInterface = 0
    // Endpoint Descriptor (interrupt IN, status change pipe)
    0x07, 0x05,             // bLength=7, bDescriptorType=ENDPOINT
    0x81,                   // bEndpointAddress = EP1 IN
    0x03,                   // bmAttributes = Interrupt
    0x02, 0x00,             // wMaxPacketSize = 2
    0x0C                    // bInterval = 12
};

// Hub Class Descriptor (USB 2.0 section 11.23.2.1), 2-port, non-removable
static const uint8_t usb_hub_class_descriptor[9] = {
    0x09,                   // bDescLength = 9 (7 + 1 DeviceRemovable byte
                             // + 1 PortPwrCtrlMask byte for 2 ports)
    0x29,                   // bDescriptorType = HUB
    0x02,                   // bNbrPorts = 2
    0x00, 0x00,             // wHubCharacteristics = ganged power, not compound
    0x00,                   // bPwrOn2PwrGood = 0
    0x00,                   // bHubContrCurrent = 0
    0x00,                   // DeviceRemovable bitmap (ports 1-2 not removable)
    0xFF                    // PortPwrCtrlMask (legacy, all 1s)
};

// Device Qualifier Descriptor (10 bytes, required for HS devices so a HS
// host's GET_DESCRIPTOR(DEVICE_QUALIFIER) succeeds instead of stalling).
static const uint8_t usb_hub_qualifier_descriptor[10] = {
    0x0A, 0x06,             // bLength=10, bDescriptorType=DEVICE_QUALIFIER
    0x00, 0x02,             // bcdUSB = 0x0200
    0x09, 0x00, 0x00,       // bDeviceClass=HUB, SubClass=0, Protocol=0
    0x40,                   // bMaxPacketSize0 = 64
    0x01,                   // bNumConfigurations = 1
    0x00                    // bReserved = 0
};

// Write a byte array into HUB RAM at the given byte offset, 4 bytes at a
// time (HUB RAM is word-addressable via the hub_axi AXI port).
static void usb_hub_ram_write_bytes(uint32_t offset, const uint8_t *data, uint32_t len) {
    uint32_t i = 0;
    while (i < len) {
        uint32_t word = 0;
        for (uint32_t b = 0; b < 4; b++) {
            uint32_t byte = (i + b < len) ? data[i + b] : 0u;
            word |= (byte << (8 * b));
        }
        lsu_write_32(USB_HUB_RAM_BASE_ADDR + offset + i, word);
        i += 4;
    }
}

// Program one 16-byte SETUP-match entry at HUB RAM offset
// USB_HUB_RAM_SETUP_TABLE_OFFSET + (index * 16).
//   bmreqtype/breq/wvalue/req_l/dpbuf/wvalue_mask/windex/dplen/windex_mask
// req_l: bits[6:0] = Request field (internal op selector), bit7 = L (last)
// dpbuf: bit7=1 selects descriptor-slot response, bits[6:0]=slot select;
//        bits[7:6]=00 => standard request encoding used here.
static void usb_hub_write_setup_entry(uint32_t index, uint8_t bmreqtype,
                                       uint8_t breq, uint16_t wvalue,
                                       uint16_t wvalue_mask, uint16_t windex,
                                       uint16_t windex_mask, uint16_t dplen,
                                       uint8_t req_l, uint8_t dpbuf) {
    uint32_t base = USB_HUB_RAM_SETUP_TABLE_OFFSET + (index * USB_HUB_RAM_SETUP_ENTRY_SIZE);
    uint8_t entry[16] = {0};
    entry[USB_HUB_SETUP_ENTRY_BMREQTYPE]     = bmreqtype;
    entry[USB_HUB_SETUP_ENTRY_BREQUEST]      = breq;
    entry[USB_HUB_SETUP_ENTRY_WVALUE]        = (uint8_t)(wvalue & 0xFFu);
    entry[USB_HUB_SETUP_ENTRY_WVALUE + 1]    = (uint8_t)(wvalue >> 8);
    entry[USB_HUB_SETUP_ENTRY_REQ_L]         = req_l;
    entry[USB_HUB_SETUP_ENTRY_DPBUF]         = dpbuf;
    entry[USB_HUB_SETUP_ENTRY_WVALUE_MASK]   = (uint8_t)(wvalue_mask & 0xFFu);
    entry[USB_HUB_SETUP_ENTRY_WVALUE_MASK+1] = (uint8_t)(wvalue_mask >> 8);
    entry[USB_HUB_SETUP_ENTRY_WINDEX]        = (uint8_t)(windex & 0xFFu);
    entry[USB_HUB_SETUP_ENTRY_WINDEX + 1]    = (uint8_t)(windex >> 8);
    entry[USB_HUB_SETUP_ENTRY_DPLEN]         = (uint8_t)(dplen & 0xFFu);
    entry[USB_HUB_SETUP_ENTRY_DPLEN + 1]     = (uint8_t)(dplen >> 8);
    entry[USB_HUB_SETUP_ENTRY_WINDEX_MASK]   = (uint8_t)(windex_mask & 0xFFu);
    entry[USB_HUB_SETUP_ENTRY_WINDEX_MASK+1] = (uint8_t)(windex_mask >> 8);
    usb_hub_ram_write_bytes(base, entry, 16);
}

// -------------------------------------------------------------------------
// usb_hub_init_and_connect
//
// Programs the HUB RAM (hub device/config/class/qualifier descriptors +
// SETUP-match table) per the USB Hub Composite Device User Guide section
// 3.2.7, validates the image via readback, then sets HUB_EN followed by
// HUB_CONNECT. This MUST run before the upstream host can ever see USBDC0
// or USBDC1 - without it, the hub entity never presents itself on the bus
// at all, which manifests as a permanent DRES_C-never-set hang identical
// to the one observed in vcs_sim.log (DEVCMDSTAT/INTSTAT never change).
// -------------------------------------------------------------------------
void usb_hub_init_and_connect(void) {
    VPRINTF(LOW, "MCU: usb_hub_init_and_connect - programming HUB RAM\n");

    // Step 1-2: Clear HUB_CONNECT and HUB_EN before (re)programming RAM.
    lsu_write_32(USB_HUB_CTRL, 0x00000000u);

    // Step 3-4: Write descriptor images into HUB RAM.
    usb_hub_ram_write_bytes(USB_HUB_RAM_DESC0_OFFSET, usb_hub_device_descriptor,
                             sizeof(usb_hub_device_descriptor));
    usb_hub_ram_write_bytes(USB_HUB_RAM_DESC1_OFFSET, usb_hub_config_descriptor,
                             sizeof(usb_hub_config_descriptor));
    usb_hub_ram_write_bytes(USB_HUB_RAM_DESC2_OFFSET, usb_hub_class_descriptor,
                             sizeof(usb_hub_class_descriptor));
    usb_hub_ram_write_bytes(USB_HUB_RAM_DESC3_OFFSET, usb_hub_qualifier_descriptor,
                             sizeof(usb_hub_qualifier_descriptor));
    // Other-Speed-Configuration descriptor: reuse the config descriptor
    // bytes but patch bDescriptorType to OTHER_SPEED_CONFIGURATION (0x07).
    {
        uint8_t other_speed[sizeof(usb_hub_config_descriptor)];
        for (uint32_t i = 0; i < sizeof(usb_hub_config_descriptor); i++) {
            other_speed[i] = usb_hub_config_descriptor[i];
        }
        other_speed[1] = USB_DESC_OTHER_SPEED_CONFIGURATION;
        usb_hub_ram_write_bytes(USB_HUB_RAM_DESC4_OFFSET, other_speed, sizeof(other_speed));
    }

    // Step 5: Program the dev-link pointer slot (read by the RTL's
    // usb_ep0_handler.m.vhdl PROC_SETUP_DECODE FSM at C_DEV_LINK_START,
    // a DWORD address) to point at the SETUP-match table. The value
    // written here MUST be a DWORD address (byte_offset / 4), not the
    // raw byte offset - the RTL uses this value directly as
    // setup_mem_addr without any further scaling.
    lsu_write_32(USB_HUB_RAM_BASE_ADDR + USB_HUB_RAM_PTR_SETUP_OFFSET,
                 USB_HUB_RAM_SETUP_TABLE_DWORD_ADDR);


    // Step 6-8: Program SETUP-match entries. Minimal set sufficient for
    // standard device enumeration plus basic hub-class port status/feature
    // requests used during hub bring-up.
    uint32_t idx = 0;
    // GET_DESCRIPTOR SETUP-match entries' DPBUF slot field is consumed by
    // the EP0-IN streaming DMA path (upd_dma_addr/ep0_mem_addr), which
    // addresses hub_desc_mem starting at absolute hub_axi-aperture byte 0
    // (slot 0 = aperture byte 0), NOT at USB_HUB_RAM_BASE_ADDR (aperture
    // byte 0x200). Firmware writes descriptors at USB_HUB_RAM_BASE_ADDR +
    // USB_HUB_RAM_DESCn_OFFSET, i.e. absolute aperture byte 0x200+offset.
    // Bias every slot number by USB_HUB_DESC_SLOT_BASE (see usb.h Root
    // Cause #3) so the DPBUF slot's implied aperture address
    // (slot*64 bytes) matches the actual write address.
    // GET_DESCRIPTOR(DEVICE) -> slot 0 (Descriptor0)
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_DESCRIPTOR,
                               (USB_DESC_DEVICE << 8), 0xFF00, 0x0000, 0x0000,
                               18, 0x00, 0x80 | (USB_HUB_DESC_SLOT_BASE + 0x00));
    // GET_DESCRIPTOR(CONFIGURATION) -> slot 1 (Descriptor1)
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_DESCRIPTOR,
                               (USB_DESC_CONFIGURATION << 8), 0xFF00, 0x0000, 0x0000,
                               sizeof(usb_hub_config_descriptor), 0x00,
                               0x80 | (USB_HUB_DESC_SLOT_BASE + 0x01));
    // GET_DESCRIPTOR(DEVICE_QUALIFIER) -> slot 3 (Descriptor3)
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_DESCRIPTOR,
                               (USB_DESC_DEVICE_QUALIFIER << 8), 0xFF00, 0x0000, 0x0000,
                               sizeof(usb_hub_qualifier_descriptor), 0x00,
                               0x80 | (USB_HUB_DESC_SLOT_BASE + 0x03));
    // GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) -> slot 4 (Descriptor4)
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_DESCRIPTOR,
                               (USB_DESC_OTHER_SPEED_CONFIGURATION << 8), 0xFF00,
                               0x0000, 0x0000,
                               sizeof(usb_hub_config_descriptor), 0x00,
                               0x80 | (USB_HUB_DESC_SLOT_BASE + 0x04));
    // GET_DESCRIPTOR(HUB CLASS, via class request) -> slot 2 (Descriptor2)
    usb_hub_write_setup_entry(idx++, 0xA0, USB_REQ_GET_DESCRIPTOR,
                               (0x29u << 8), 0xFF00, 0x0000, 0x0000,
                               sizeof(usb_hub_class_descriptor),
                               0x00 | 0x40 /* class-request op */,
                               0x80 | (USB_HUB_DESC_SLOT_BASE + 0x02));

    // SET_ADDRESS -> internal op, no data phase
    usb_hub_write_setup_entry(idx++, 0x00, USB_REQ_SET_ADDRESS,
                               0x0000, 0x0000, 0x0000, 0x0000,
                               0, 0x01 /* internal SET_ADDRESS op */, 0x00);
    // SET_CONFIGURATION -> internal op, no data phase
    usb_hub_write_setup_entry(idx++, 0x00, USB_REQ_SET_CONFIGURATION,
                               0x0000, 0x0000, 0x0000, 0x0000,
                               0, 0x02 /* internal SET_CONFIGURATION op */, 0x00);
    // GET_CONFIGURATION -> internal op, 1-byte data phase
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_CONFIGURATION,
                               0x0000, 0x0000, 0x0000, 0x0000,
                               1, 0x03 /* internal GET_CONFIGURATION op */, 0x00);
    // GET_STATUS(device) -> internal op, 2-byte data phase
    usb_hub_write_setup_entry(idx++, 0x80, USB_REQ_GET_STATUS,
                               0x0000, 0x0000, 0x0000, 0x0000,
                               2, 0x04, 0x00);

    // ---------------------------------------------------------------------
    // Hub-Class port bring-up requests, required so hub_port_bringup()
    // (caliptra_ss_usb_hs_dev_bulk_out_sequence.svh) can be re-enabled.
    // Per usb_app_hw_hub.m.vhdl, hub_port_enable(port) is only ever set in
    // response to a live SetPortFeature(PORT_RESET) class request decoded
    // through ep0_request/ep0_wvalue/ep0_windex - which are driven by these
    // SETUP-match table entries' req_l opcode field (C_CLASS_REQ_* constants
    // in usb_ep_config_hub_pkg.p.vhdl: CLEAR_FEATURE=0x40, SET_FEATURE=0x41,
    // GET_STATUS=0x42). windex (port number) is deliberately masked out
    // (don't-care) since hub_port_bringup() may target any port index; the
    // hub HW itself range-checks windex against C_HUB_NB_PORTS and decodes
    // the port from windex-1 at dispatch time, not at SETUP-match time.
    // ---------------------------------------------------------------------
    // SetFeature(PORT_POWER) -> class op 0x41 (SET_FEATURE)
    usb_hub_write_setup_entry(idx++, 0x23, 0x03,
                               0x0008, 0xFFFF, 0x0000, 0x0000,
                               0, 0x41, 0x00);
    // SetFeature(PORT_RESET) -> class op 0x41 (SET_FEATURE)
    usb_hub_write_setup_entry(idx++, 0x23, 0x03,
                               0x0004, 0xFFFF, 0x0000, 0x0000,
                               0, 0x41, 0x00);
    // GetPortStatus -> class op 0x42 (GET_STATUS), 4-byte status word
    usb_hub_write_setup_entry(idx++, 0xA3, 0x00,
                               0x0000, 0xFFFF, 0x0000, 0x0000,
                               4, 0x42, 0x00);
    // ClearFeature(C_PORT_RESET) -> class op 0x40 (CLEAR_FEATURE).
    usb_hub_write_setup_entry(idx++, 0x23, 0x01,
                               0x0014, 0xFFFF, 0x0000, 0x0000,
                               0, 0x40, 0x00);
    // ClearFeature(PORT_ENABLE) -> class op 0x40 (CLEAR_FEATURE).
    //
    // This is the ONLY hub-class request that genuinely powers-down the
    // embedded downstream device USBDC0 in this IP. Per usb_app_hw_hub.m.vhdl
    // PROC_REQUEST_HANDLING, ClearFeature with wValue=1 (Port_Enable) drives
    //   hub_port_enable_int(var_port) <= '0'   (var_port = wIndex - 1)
    // and per ip_xxx_3511_hs_mem_compound_structure.a.vhdl USBDC0's
    // controller-enable is gated by hub_port_enable(0):
    //   usbreg_deviceenabled(1) <= hub_port_enable(0) and usbreg_arm_deviceenabled
    // so clearing Port_Enable on port 1 (wIndex=1 -> var_port=0) forces
    // USBDC0 deviceenabled to 0 - a waveform-visible power-down. Recovery is
    // via SetFeature(PORT_RESET) (wValue=4) which re-asserts hub_port_enable
    // AND pulses hub_port_reset -> USBDC0 sees a fresh bus reset.
    //
    // The RTL setup-match FSM (usb_ep0_handler.m.vhdl PROC_SETUP_DECODE) only
    // populates ep0_request (the class opcode routed to the hub handler) from
    // a MATCHED table entry: match requires exact bmReqType+bRequest AND
    // (live_wValue AND wvalue_mask) == table_wValue. The C_PORT_RESET entry
    // above matches wValue=0x0014 exactly, so a separate wValue=0x0001 entry
    // is mandatory for ClearFeature(PORT_ENABLE) to be decoded (otherwise the
    // transfer is ACK'd at the protocol level but is a no-op = false pass).
    // This is the final table entry, so it carries the L (last) bit; the
    // linear search terminates here.
    usb_hub_write_setup_entry(idx++, 0x23, 0x01,
                               0x0001, 0xFFFF, 0x0000, 0x0000,
                               0, 0x40 | USB_HUB_SETUP_ENTRY_L_MASK, 0x00);



    VPRINTF(LOW, "MCU: usb_hub_init_and_connect - %d SETUP-match entries programmed\n",
            (int)idx);

    // Step 9-10: Read back and validate. Spot-check ptrSetupTable and the
    // first/last SETUP-match entries; a full byte-for-byte compare of all
    // descriptor bytes is omitted here for brevity but the readback of the
    // control-flow-critical fields (pointer, final L bit) is mandatory.
    uint32_t ptr_rb = lsu_read_32(USB_HUB_RAM_BASE_ADDR + USB_HUB_RAM_PTR_SETUP_OFFSET);
    VPRINTF(LOW, "MCU: HUB RAM ptrSetupTable readback = 0x%x (expected 0x%x)\n",
            ptr_rb, USB_HUB_RAM_SETUP_TABLE_DWORD_ADDR);

    uint32_t last_entry_base = USB_HUB_RAM_SETUP_TABLE_OFFSET
                              + ((idx - 1) * USB_HUB_RAM_SETUP_ENTRY_SIZE);
    uint32_t last_word1 = lsu_read_32(USB_HUB_RAM_BASE_ADDR + last_entry_base + 0x04);
    uint8_t last_req_l = (uint8_t)(last_word1 & 0xFFu);
    VPRINTF(LOW, "MCU: HUB RAM last SETUP entry req_l readback = 0x%x (L bit expected set)\n",
            last_req_l);

    // Step 11: Enable the hub entity. HUB_CONNECT is deliberately NOT set
    // here - it is set separately by usb_hub_connect(), per the reference
    // janus_hub_ctrl_bfm.sv two-phase sequencing (HUB_EN alone first, then
    // after a settling delay, HUB_EN|HUB_CONNECT together).
    lsu_write_32(USB_HUB_CTRL, USBHUB_CTRL_HUB_EN_MASK);
    uint32_t hub_ctrl_rb = lsu_read_32(USB_HUB_CTRL);
    VPRINTF(LOW, "MCU: HUB_CTRL after HUB_EN=1 readback = 0x%x\n", hub_ctrl_rb);

    VPRINTF(LOW, "MCU: usb_hub_init_and_connect - RAM programmed, HUB_EN set"
            " (HUB_CONNECT deferred to usb_hub_connect())\n");
}

// -------------------------------------------------------------------------
// usb_hub_connect
//
// Step 12: Connect the hub to the upstream port (VBUS is assumed valid in
// this testbench environment; a real system would poll a VBUS-valid status
// bit here before setting HUB_CONNECT). Split out from
// usb_hub_init_and_connect() to match the reference janus_hub_ctrl_bfm.sv
// two-phase sequencing: HUB_EN must be set and settled BEFORE HUB_CONNECT
// is asserted. Call this after usb_hub_init_and_connect() (with a settling
// delay in between if desired) and after USBDC0 is ready via
// boot_usb_core(), since the host will begin enumerating hub port 0 (and
// thus USBDC0) as soon as the hub connects upstream.
// -------------------------------------------------------------------------
void usb_hub_connect(void) {
    lsu_write_32(USB_HUB_CTRL, USBHUB_CTRL_HUB_EN_MASK | USBHUB_CTRL_HUB_CONNECT_MASK);
    uint32_t hub_ctrl_rb = lsu_read_32(USB_HUB_CTRL);
    VPRINTF(LOW, "MCU: HUB_CTRL after HUB_CONNECT=1 readback = 0x%x\n", hub_ctrl_rb);
    VPRINTF(LOW, "MCU: usb_hub_connect - done\n");
}


// -------------------------------------------------------------------------
// boot_usb_core - Initialize the USB device controller
//
// Sets up the EP command/status list and data buffers in SRAM, then
// configures EPLISTSTART, DATABUFSTART, DEVCMDSTAT, and interrupt enables
// so the USB device is ready to respond to host enumeration.
//
// SRAM layout:
//   0x000-0x00F: EP0 command/status list (4 words)
//   0x010-0x0FF: Other EP entries (zeroed/disabled)
//   0x100-0x107: SETUP data buffer (8 bytes)
//   0x140-0x17F: EP0 OUT data buffer (64 bytes)
//   0x180-0x1BF: EP0 IN data buffer (64 bytes)
// -------------------------------------------------------------------------
void boot_usb_core(void) {
    uint32_t reg_data;

    VPRINTF(LOW, "MCU: boot_usb_core - initializing USB device controller\n");

    // --- Step -1: Hub-Enabled mode - program HUB RAM and set HUB_EN ---
    // USB_EnableHub is tied to 1'b0 in caliptra_ss_top.sv (matching the
    // reference janus_compound_smoke_tb.vhdl), so the hub entity is brought
    // up entirely at runtime by firmware. usb_hub_init_and_connect()
    // programs+validates the HUB RAM (descriptors + SETUP-match table) and
    // sets HUB_EN, per:
    //   hub_enable_eff <= usb_hubenable_ss OR hub_enable_q;
    // (ip_xxx_3511_hs_mem_compound_structure.a.vhdl). This must run before
    // the host can ever see USBDC0 or USBDC1, both of which are embedded
    // downstream devices of the compound hub in this mode. usb_hub_connect()
    // (which asserts HUB_CONNECT) is called separately, later, once USBDC0
    // is also ready - see caliptra_ss_usb_hs_dev_bulk_out.c's main().
    usb_hub_init_and_connect();



    // --- Step 0a: OTG PHY mux is NOT present on the new hub-composite IP ---
    // The legacy single-device IP had a PORTMODE register (SOC_USBHSH_PORTMODE,
    // offset 0x50) that steered UTMI signals between an internal host/device
    // mux. The new ip_xxx_3511_hs_mem_compound hub IP has no such mux/register:
    // hub routing is controlled by the USB_EnableHub top-level strap (tied to
    // 1'b0 here) plus the runtime HUB_EN register, and the USBDC0 register
    // file only decodes offsets 0x00-0x3C (haddr[5:2], 4-bit / 16-register
    // window - see usb.h).

    //
    // Root cause: writing SOC_USBHSH_PORTMODE (0x2000_1050) landed inside the
    // new dev0_axi register aperture (offset 0x50 < DEV0_REG_ADDR_TOP=0x100),
    // but since only haddr[5:2] is decoded, offset 0x50 ALIASES onto offset
    // 0x10 (USB_DEV0_LPM), silently corrupting LPM on every boot. This left
    // the device controller in an undefined state and was the direct cause
    // of the u_dev0_axi2ahb.u_r_resp_fifo DataKnown_A fatal assertion (X data)
    // on the very next dev0_axi read. Fix: remove the write.

    // --- Step 0b: skip the diagnostic pre-write DEVCMDSTAT read ---
    // The vendor USBDC0 register file inside ip_xxx_3511_hs_mem_compound
    // does not drive fully-known (non-X) data on its AHB read-data output
    // for registers that have never been written since reset. Performing a
    // raw AXI read of DEVCMDSTAT here - before any write has ever occurred
    // on dev0_axi - returns X for at least one bit-field, which propagates
    // into u_dev0_axi2ahb.u_r_resp_fifo and fires the fatal DataKnown_A
    // assertion. This diagnostic read was purely informational (its value
    // was only ever printed, never used for a control decision), so it has
    // been removed. DEVCMDSTAT is safely read back further below, AFTER
    // Step 3 has written it for the first time.

    // --- Step 0: Initialize SRAM via DMA port ---

    // EP0 OUT entry: Active=1, NBytes=8 (for SETUP).
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET) >> 6
    //             = 0x20001240 >> 6 & 0x7FF = 0x49
    // Using USB_EP_ENTRY_ABS_ADDR so the DMA-computed buffer address matches
    // the absolute AXI address the MCU uses to read/write the same SRAM word.
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    // EP0 SETUP buffer address entry.
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET) >> 6
    //             = 0x20001200 >> 6 & 0x7FF = 0x48
    uint32_t ep0_setup_entry = USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    // EP0 IN entry: Active=0, NBytes=0.
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET) >> 6
    //             = 0x20001280 >> 6 & 0x7FF = 0x4A
    uint32_t ep0_in_entry = USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    // EPLISTSTART must point to the absolute AXI address of the EP list in
    // USBDC0's SRAM. The ahb_dma_slave inside the compound wrapper uses the
    // FULL absolute AXI haddr as the SRAM index (stored_addr <= ads_haddr).
    // The USB DMA engine uses ads_dma_addr = EPLISTSTART + entry_offset, so
    // EPLISTSTART must equal the AXI address where the EP list was written,
    // which is USB_DEV0_DMA_BASE_ADDR (0x20001100). Setting it to 0 causes
    // the DMA engine to access SRAM at word 0 while the MCU writes at word
    // 0x1100>>3 = 0x220 - a complete SRAM address mismatch that explains why
    // all SETUP packet reads return zero.
    lsu_write_32(USB_DEV0_EPLISTSTART, USB_DEV0_DMA_BASE_ADDR);

    // --- Step 2: Set data buffer page address ---
    // Same rationale: DATABUFSTART must equal USB_DEV0_DMA_BASE_ADDR so that
    // DMA writes of SETUP/data land at the same absolute AXI addresses the
    // firmware reads from (e.g. SETUP buffer at USB_DEV0_DMA_BASE_ADDR+0x100).
    lsu_write_32(USB_DEV0_DATABUFSTART, USB_DEV0_DMA_BASE_ADDR);

    // --- Step 3: Enable device ---
    // HS link-up: do NOT set FORCE_FULLSPEED. The device controller will
    // perform HS chirp at the next bus reset.

    reg_data = USBHSD_DEVCMDSTAT_DEV_EN_MASK
             | USBHSD_DEVCMDSTAT_FORCE_VBUS_MASK
             | USBHSD_DEVCMDSTAT_FORCE_NEEDCLK_MASK
             | USBHSD_DEVCMDSTAT_DCON_MASK;
    lsu_write_32(USB_DEV0_DEVCMDSTAT, reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n", reg_data);


    // Read back to confirm - safe: DEVCMDSTAT was just written above, so
    // the vendor register file's output is now fully known (non-X).
    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 4: Enable interrupts ---
    lsu_write_32(USB_DEV0_INTEN,
        USBHSD_INTSTAT_DEV_INT_MASK |
        USBHSD_INTSTAT_EP0OUT_MASK  |
        USBHSD_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        USBHSD_INTSTAT_DEV_INT_MASK | USBHSD_INTSTAT_EP0OUT_MASK | USBHSD_INTSTAT_EP0IN_MASK);

    // --- Step 5: Clear pending interrupts ---
    lsu_write_32(USB_DEV0_INTSTAT, 0xC0000FFF);

    VPRINTF(LOW, "MCU: boot_usb_core - done\n");
}

// -------------------------------------------------------------------------
// boot_usb_core_fs - Initialize the USB device controller in FS-only mode
//
// Identical to boot_usb_core() except that DEVCMDSTAT bit 21 (PFSC - Port
// Force Full Speed Connect) is set before connecting. Setting PFSC prevents
// the device controller from emitting K-chirp after bus reset, so the UTMI
// TX is ready for FS packet exchange immediately. Use this function in tests
// that run with a FS-only host (e.g. SVT VIP with high_speed_capable=0)
// where no chirp reply will be driven and the default chirp timeout (~2.2ms)
// would stall the first SETUP transfer.
//
// DO NOT call this function when HS operation is required.
// -------------------------------------------------------------------------
void boot_usb_core_fs(void) {
    uint32_t reg_data;

    VPRINTF(LOW, "MCU: boot_usb_core_fs - initializing USB device controller (FS-only)\n");

    // --- Step 0a: OTG PHY mux is NOT present on the new hub-composite IP ---
    // See boot_usb_core() above for full rationale: the legacy PORTMODE write
    // aliased onto USB_DEV0_LPM in the new hub IP's register decode and was
    // the root cause of a fatal X-propagation assertion. Removed.

    // --- Step 0b: skip the diagnostic pre-write DEVCMDSTAT read ---
    // See boot_usb_core() above: the vendor USBDC0 register file drives X
    // on reads to never-written registers, and this diagnostic read (before
    // any write to dev0_axi has ever occurred) triggered the fatal
    // DataKnown_A assertion in u_dev0_axi2ahb.u_r_resp_fifo. Removed.

    // --- Step 0: Initialize SRAM via DMA port ---

    // EP0 OUT entry: Active=1, NBytes=8 (for SETUP).
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET) >> 6
    //             = 0x20001240 >> 6 & 0x7FF = 0x49
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    // EP0 SETUP buffer address entry.
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET) >> 6
    //             = 0x20001200 >> 6 & 0x7FF = 0x48
    uint32_t ep0_setup_entry = USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    // EP0 IN entry: Active=0, NBytes=0.
    // addr_offset = (USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET) >> 6
    //             = 0x20001280 >> 6 & 0x7FF = 0x4A
    uint32_t ep0_in_entry = USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    // Same fix as boot_usb_core(): EPLISTSTART must be the absolute AXI
    // address of the EP list (USB_DEV0_DMA_BASE_ADDR), not zero.
    lsu_write_32(USB_DEV0_EPLISTSTART, USB_DEV0_DMA_BASE_ADDR);

    // --- Step 2: Set data buffer page address ---
    // Same fix: DATABUFSTART must equal USB_DEV0_DMA_BASE_ADDR.
    lsu_write_32(USB_DEV0_DATABUFSTART, USB_DEV0_DMA_BASE_ADDR);

    // --- Step 2b: Initialize HUB RAM and assert HUB_EN ---
    // The hub composite IP requires HUB RAM programming (descriptor table +
    // SETUP-match entries) and HUB_EN assertion before DCON is raised.
    // Identical requirement as boot_usb_core(); omitting this step leaves
    // hub EP0 unable to respond to host SETUP packets (NAK violation).
    usb_hub_init_and_connect();

    // --- Step 3: Enable device in FS-only mode ---
    // PFSC (bit 21) suppresses the device-side K-chirp so that the UTMI TX
    // initializes immediately for FS. Without PFSC the chirp state machine
    // would wait ~2.2ms for a J-chirp reply that a FS-only host never sends,
    // delaying the first SETUP ACK beyond the VIP tend_to_end_delay_fs window.

    reg_data = USBHSD_DEVCMDSTAT_DEV_EN_MASK
             | USBHSD_DEVCMDSTAT_FORCE_VBUS_MASK
             | USBHSD_DEVCMDSTAT_FORCE_NEEDCLK_MASK
             | USBHSD_DEVCMDSTAT_DCON_MASK
             | USBHSD_DEVCMDSTAT_PFSC_MASK;
    lsu_write_32(USB_DEV0_DEVCMDSTAT, reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n", reg_data);

    // Read back to confirm
    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 4: Enable interrupts ---
    lsu_write_32(USB_DEV0_INTEN,
        USBHSD_INTSTAT_DEV_INT_MASK |
        USBHSD_INTSTAT_EP0OUT_MASK  |
        USBHSD_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        USBHSD_INTSTAT_DEV_INT_MASK | USBHSD_INTSTAT_EP0OUT_MASK | USBHSD_INTSTAT_EP0IN_MASK);

    // --- Step 5: Clear pending interrupts ---
    lsu_write_32(USB_DEV0_INTSTAT, 0xC0000FFF);

    VPRINTF(LOW, "MCU: boot_usb_core_fs - done\n");
}

void usb_ep0_reinit(void) {
    // The reference vendor testbench model
    // (usb_hub_composite_device/TESTBENCH/MODELS/janus_ahb_fw_bfm.sv)
    // programs the EP-list SRAM (EP0 OUT / SETUP-offset / EP0 IN entries,
    // plus EP1-EP4 zeroing) via init_dma_ram() exactly ONCE, at startup,
    // before DEV_EN is ever asserted. Its bus-reset handling path
    // (service_irq()'s INT_DEV / DRES_C branch) does nothing more than
    // set a flag (reset_event_seen_o) - it never rewrites any EP-list
    // entry. The EP-list/data-buffer SRAM is plain memory that is NOT
    // cleared or otherwise touched by a USB bus reset in this IP; only
    // the register-file control/status bits (DEVCMDSTAT, etc.) are
    // affected.
    VPRINTF(LOW, "MCU: usb_ep0_reinit - no-op (EP list SRAM left untouched,"
            " matching reference janus_ahb_fw_bfm.sv behavior)\n");
}

void usb_handle_bus_reset(void) {
    uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    if (!(cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK)) {
        return;
    }
    VPRINTF(LOW, "MCU: USB bus reset detected\n");
    // Bus reset returns device address to 0 per USB spec; update shadow so all
    // subsequent DEVCMDSTAT RMW writes carry the reset address.
    usb_dev_addr_shadow = 0;
    // USB 2.0 §9.1.1.3: reset returns the device to the Default state with
    // no configuration selected. Mirror that in the firmware shadow so a
    // subsequent GET_CONFIGURATION reports 0 until SET_CONFIGURATION runs.
    usb_current_config = 0;
    // Clear DRES_C (W1C)
    usb_devcmdstat_write(cmd | USBHSD_DEVCMDSTAT_DRES_C_MASK);
    usb_ep0_reinit();
    // Reset device address to 0 per USB spec
    cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    cmd &= ~USBHSD_DEVCMDSTAT_DEV_ADDR_MASK;
    usb_devcmdstat_write(cmd);
}

void usb_read_setup_packet(usb_setup_pkt_t *pkt) {
    uint32_t w0 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    uint32_t w1 = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET + 4);
    pkt->bmRequestType = (uint8_t)((w0 >>  0) & 0xFF);
    pkt->bRequest      = (uint8_t)((w0 >>  8) & 0xFF);
    pkt->wValue        = (uint16_t)((w0 >> 16) & 0xFFFF);
    pkt->wIndex        = (uint16_t)((w1 >>  0) & 0xFFFF);
    pkt->wLength       = (uint16_t)((w1 >> 16) & 0xFFFF);
    // NOTE: VPRINTF intentionally omitted from the SETUP read hot-path.
    // Logging before priming EP0 IN causes the VIP tend_to_end_delay_check
    // timer (~2.3us) to fire. Callers log AFTER priming if needed.
}

void usb_ep0_send_data(const uint32_t *data, uint32_t nbytes) {
    uint32_t nwords = (nbytes + 3) / 4;
    for (uint32_t i = 0; i < nwords; i++) {
        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET + (i * 4), data[i]);
    }
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_NBYTES(nbytes)
                    | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    // NOTE: VPRINTF intentionally omitted from EP0 IN arming hot-path.
    // Host VIP only gives ~5us between SETUP-ACK and giving up on IN polling;
    // adding logging here delays the arm beyond that window for back-to-back
    // SETUPs (e.g. GET_STATUS following GET_DESCRIPTOR).
}

void usb_ep0_send_zlp(void) {
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
}

void usb_ep0_stall(void) {
    uint32_t ep0_in  = USB_EP_ENTRY_STALL
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    uint32_t ep0_out = USB_EP_ENTRY_STALL
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
    VPRINTF(LOW, "MCU: EP0 stalled\n");
}

void usb_ep0_arm_out(void) {
    uint32_t ep0_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV0_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
}

void usb_clear_setup_bit(void) {
    uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    usb_devcmdstat_write(cmd | USBHSD_DEVCMDSTAT_SETUP_MASK);
}

void usb_set_device_address(uint8_t addr) {
    usb_dev_addr_shadow = (uint8_t)(addr & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK);
    uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    usb_devcmdstat_write(cmd);
}

// -------------------------------------------------------------------------
// usb_handle_control_transfer
//
// Reads the current SETUP packet from SRAM and dispatches it by decoding
// bmRequestType (type + recipient) and bRequest. Fully implements:
//   - Standard/Device: SET_ADDRESS, GET_DESCRIPTOR(DEVICE)
// All other requests are explicitly logged and cause an EP0 stall so that
// simulation logs clearly identify unimplemented transfers.
// usb_clear_setup_bit() is always called last, per Integration Guide 4.2.4.1.1.
// Returns true if handled without stall, false otherwise.
// -------------------------------------------------------------------------
bool usb_handle_control_transfer(void) {
    usb_setup_pkt_t pkt;
    bool handled = false;

    usb_read_setup_packet(&pkt);

    uint8_t req_type  = USB_BMREQTYPE_TYPE(pkt.bmRequestType);
    uint8_t recipient = USB_BMREQTYPE_RECIPIENT(pkt.bmRequestType);

    // Clear EP0 IN interrupt before programming response
    lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

    if (req_type == USB_TYPE_STANDARD) {
        if (recipient == USB_RECIP_DEVICE) {
            switch (pkt.bRequest) {
                case USB_REQ_GET_DESCRIPTOR: {
                    uint8_t desc_type = (uint8_t)((pkt.wValue >> 8) & 0xFF);
                    if (desc_type == USB_DESC_DEVICE) {
                        uint32_t nbytes = (pkt.wLength < 18u) ? pkt.wLength : 18u;
                        usb_ep0_send_data(usb_default_device_descriptor, nbytes);
                        usb_ep0_arm_out();
                        // Enable IntOnNAK_CO for status-phase detection
                        uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
                        cmd |=  USBHSD_DEVCMDSTAT_INTONNAK_CO_MASK;
                        cmd &= ~USBHSD_DEVCMDSTAT_INTONNAK_CI_MASK;
                        usb_devcmdstat_write(cmd);
                        handled = true;
                    } else {
                        usb_ep0_stall();
                        VPRINTF(LOW, "MCU: USB Unhandled GET_DESCRIPTOR type=0x%02x"
                                " - stalling\n", desc_type);
                    }
                    break;
                }
                case USB_REQ_SET_ADDRESS: {
                    uint8_t new_addr = (uint8_t)(pkt.wValue & 0x7Fu);
                    usb_ep0_send_zlp();
                    usb_ep0_arm_out();
                    usb_set_device_address(new_addr);
                    handled = true;
                    break;
                }
                case USB_REQ_GET_STATUS: {
                    // Standard device GET_STATUS: 2-byte status word.
                    // bit[0]=Self-Powered, bit[1]=Remote Wakeup, both 0.
                    static const uint32_t status_buf = 0x00000000u;
                    usb_ep0_send_data(&status_buf, 2);
                    usb_ep0_arm_out();
                    handled = true;
                    break;
                }
                case USB_REQ_CLEAR_FEATURE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device CLEAR_FEATURE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_FEATURE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_FEATURE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_DESCRIPTOR:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_DESCRIPTOR"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_GET_CONFIGURATION: {
                    // Standard device GET_CONFIGURATION: 1-byte current config.
                    // Returns the value most recently set by SET_CONFIGURATION,
                    // or 0 if the device is still in Address state.
                    uint32_t cfg_buf = (uint32_t)usb_current_config;
                    usb_ep0_send_data(&cfg_buf, 1);
                    usb_ep0_arm_out();
                    handled = true;
                    break;
                }
                case USB_REQ_SET_CONFIGURATION: {
                    // Standard device SET_CONFIGURATION: wValue low byte is
                    // the configuration value. The device descriptor declares
                    // bNumConfigurations=1, so accept 0 (unconfigure) or 1
                    // and stall any other value per USB 2.0 §9.4.7.
                    uint8_t new_cfg = (uint8_t)(pkt.wValue & 0xFFu);
                    if (new_cfg <= 1u) {
                        usb_current_config = new_cfg;
                        usb_ep0_send_zlp();
                        usb_ep0_arm_out();
                        handled = true;
                    } else {
                        VPRINTF(LOW, "MCU: USB SET_CONFIGURATION invalid value=%d"
                                " - stalling\n", new_cfg);
                        usb_ep0_stall();
                    }
                    break;
                }
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Device bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else if (recipient == USB_RECIP_INTERFACE) {
            switch (pkt.bRequest) {
                case USB_REQ_GET_INTERFACE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface GET_INTERFACE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                case USB_REQ_SET_INTERFACE:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface SET_INTERFACE"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Interface bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else if (recipient == USB_RECIP_ENDPOINT) {
            switch (pkt.bRequest) {
                case USB_REQ_SYNCH_FRAME:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Endpoint SYNCH_FRAME"
                            " - stalling\n");
                    usb_ep0_stall();
                    break;
                default:
                    VPRINTF(LOW, "MCU: USB Unhandled Standard/Endpoint bRequest=0x%02x"
                            " - stalling\n", pkt.bRequest);
                    usb_ep0_stall();
                    break;
            }
        } else {
            VPRINTF(LOW, "MCU: USB Unhandled Standard recipient=%d bRequest=0x%02x"
                    " - stalling\n", recipient, pkt.bRequest);
            usb_ep0_stall();
        }
    } else if (req_type == USB_TYPE_CLASS) {
        VPRINTF(LOW, "MCU: USB Unhandled Class request recipient=%d bRequest=0x%02x"
                " - stalling\n", recipient, pkt.bRequest);
        usb_ep0_stall();
    } else if (req_type == USB_TYPE_VENDOR) {
        VPRINTF(LOW, "MCU: USB Unhandled Vendor request recipient=%d bRequest=0x%02x"
                " - stalling\n", recipient, pkt.bRequest);
        usb_ep0_stall();
    } else {
        VPRINTF(LOW, "MCU: USB Reserved bmRequestType=0x%02x bRequest=0x%02x"
                " - stalling\n", pkt.bmRequestType, pkt.bRequest);
        usb_ep0_stall();
    }

    // Per Integration Guide 4.2.4.1.1: clear SETUP bit after arming response.
    // This must happen quickly: host VIP retries IN tokens for only ~5us
    // before giving up and sending the next SETUP, which will be NAKed by
    // the DUT IP unless the SETUP bit is already cleared.
    usb_clear_setup_bit();

    // Post-handler diagnostic logging. Outside the critical timing window
    // (after EP arming + SETUP-bit clear) so it does not delay the response.
    VPRINTF(LOW, "MCU: SETUP handled bmReqType=0x%02x bReq=0x%02x wVal=0x%04x"
            " wIdx=0x%04x wLen=%d handled=%d\n",
            pkt.bmRequestType, pkt.bRequest, pkt.wValue,
            pkt.wIndex, pkt.wLength, (int)handled);
    if (pkt.bRequest == USB_REQ_SET_ADDRESS) {
        VPRINTF(LOW, "MCU: SET_ADDRESS addr=%d\n", (int)(pkt.wValue & 0x7Fu));
    }

    return handled;
}
