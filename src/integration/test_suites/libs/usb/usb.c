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
// reg_dev_addr, but writes always update the staged reg_dev_addr_tmp which is
// only committed to LIVE on the next setup_received. Any naive RMW of
// DEVCMDSTAT after usb_set_device_address(N) (e.g. usb_clear_setup_bit()) will
// read LIVE (still 0) and write that back into TMP, clobbering the staged
// address. The DUT then never enables the new address and goes silent on the
// host's first SETUP@addr=N.
//
// Fix: every RMW write to DEVCMDSTAT goes through usb_devcmdstat_write() which
// re-substitutes this shadow into bits[6:0] before writeback, preserving the
// staged address regardless of call order.

// -------------------------------------------------------------------------
// Runtime active-device context (dual-controller support).
//
// usb.h selects a single controller aperture at compile time via USB_DEV_SEL.
// For single-device tests that is sufficient and nothing here changes their
// behaviour: usb_active_dev defaults to USB_DEV_SEL and is never touched.
//
// The usb_hib_compound dual-device test, however, must drive BOTH embedded
// controllers from one image. usb_select_device() repoints the whole library
// at either controller at RUNTIME; the device-neutral USB_DEV_* register
// macros and USB_DMA_BASE_ADDR are re-defined below (for this translation unit
// only) to resolve against the active controller's base instead of the fixed
// compile-time base. usb.h is left untouched, so every other test that uses
// those macros is unaffected.
//
// All enumeration shadow state that affects behaviour (device address,
// configuration, remote-wakeup feature, EP0-IN pending latch) is kept per
// device so the two controllers can enumerate in parallel without clobbering
// each other's state. Pure telemetry counters remain single-instance; they are
// only read by the single-device legacy EP0 observer tests.
// -------------------------------------------------------------------------
static int usb_active_dev = USB_DEV_SEL;

static inline uint32_t usb_active_csr_base(void) {
    return (usb_active_dev == 1) ? (uint32_t)SOC_USB_DEV1_CSR_BASE_ADDR
                                 : (uint32_t)SOC_USB_COMBO_DEV0_CSR_BASE_ADDR;
}
static inline uint32_t usb_active_mem_base(void) {
    return (usb_active_dev == 1) ? (uint32_t)SOC_USB_DEV1_MEM_BASE_ADDR
                                 : (uint32_t)SOC_USB_DEV0_MEM_BASE_ADDR;
}

// Public runtime selector (declared in usb.h). dev 0 = USBDC0, dev 1 = USBDC1;
// any other value is treated as 0.
void usb_select_device(int dev) { usb_active_dev = (dev == 1) ? 1 : 0; }
int  usb_get_active_device(void) { return usb_active_dev; }

// Re-point the device-neutral base macros at the runtime active controller for
// this translation unit only. The derived register macros (USB_DEV_DEVCMDSTAT,
// USB_DEV_INTSTAT, ...), USB_DMA_BASE_ADDR / USB_DEV_DMA_BASE_ADDR, and
// USB_EP_ENTRY_ABS_ADDR are all defined in usb.h in terms of these two bases,
// so re-defining the bases here makes the entire library follow usb_active_dev.
#undef USB_DEV_CSR_BASE_ADDR
#undef USB_DEV_MEM_BASE_ADDR
#define USB_DEV_CSR_BASE_ADDR  usb_active_csr_base()
#define USB_DEV_MEM_BASE_ADDR  usb_active_mem_base()

// Per-device enumeration shadows, indexed by the active controller. The macro
// aliases keep every existing reference in this file textually unchanged while
// making it resolve to the active controller's slot.
static uint8_t usb_dev_addr_shadow_arr[2]        = {0, 0};
static uint8_t usb_current_config_arr[2]          = {0, 0};
static bool    usb_remote_wakeup_enabled_arr[2]   = {false, false};
static uint8_t usb_ep0_in_pending_latched_arr[2]  = {0, 0};
#define usb_dev_addr_shadow        usb_dev_addr_shadow_arr[usb_active_dev]
#define usb_current_config         usb_current_config_arr[usb_active_dev]
#define usb_remote_wakeup_enabled  usb_remote_wakeup_enabled_arr[usb_active_dev]
#define usb_ep0_in_pending_latched usb_ep0_in_pending_latched_arr[usb_active_dev]

// Legacy EP0 observer telemetry counters (retained from upstream). These do not
// affect enumeration behaviour and are only consumed by single-device tests, so
// they remain single-instance.
static uint32_t usb_transfers_handled = 0;
static uint32_t usb_bus_reset_count = 0;
static uint32_t usb_ep0_irq_count = 0;
static uint32_t usb_ep0_out_irq_count = 0;
static uint32_t usb_ep0_in_irq_count = 0;
static uint32_t usb_setup_dispatch_count = 0;
static uint32_t usb_snapshot_publish_sequence = 0;
static uint8_t usb_baseline_ready_pending = 0;
static uint16_t usb_baseline_ready_generation = 0;


// Application hooks installed by boot_usb_core() (PR #1299 seam). The
// hook-based (OCP-recovery / host) enumeration path uses these; the legacy
// device path (boot_usb_core_hub / boot_usb_core_fs) leaves them 0 and the
// superset handler services standard device requests directly.
const uint8_t *(*usb_config_descriptor_override)(uint16_t *len) = 0;
bool (*usb_class_request_override)(const usb_setup_pkt_t *setup) = 0;

// Every RMW write to DEVCMDSTAT goes through here. It re-substitutes the staged
// device-address shadow into bits[6:0] (see usb_dev_addr_shadow above) and
// forces LPM_SUP so the controller keeps advertising LPM support for the whole
// run (a raw write that drove bit 11 to 0 would permanently disable LPM). The
// target is the device-neutral DEVCMDSTAT selected by USB_DEV_SEL.
static void usb_devcmdstat_write(uint32_t val) {
    val = (val & ~DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK)
        | (usb_dev_addr_shadow & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK);
    val |= DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK;
    lsu_write_32(USB_DEV_DEVCMDSTAT, val);
}

__attribute__((weak))
const uint8_t *usb_get_config_descriptor(uint16_t *len) {
    if (usb_config_descriptor_override != 0) {
        return usb_config_descriptor_override(len);
    }

    if (len != 0) {
        *len = 0;
    }

    return 0;
}

__attribute__((weak))
bool usb_handle_class_request(const usb_setup_pkt_t *setup) {
    if (usb_class_request_override != 0) {
        return usb_class_request_override(setup);
    }

    return false;
}

// Minimal USB 2.0 device descriptor (18 bytes, packed as uint32_t for SRAM
// writes). Used by the hook-based (OCP/host) enumeration path.
const uint32_t usb_default_device_descriptor[5] = {
    0x02000112,  // bLength=18, bDescType=1(DEVICE), bcdUSB=0x0200 (LE)
    0x40000000,  // bDevClass=0, bDevSubClass=0, bDevProto=0, bMaxPktSz0=64
    0x00000000,  // idVendor=0x0000, idProduct=0x0000
    0x00000100,  // bcdDevice=0x0100, iManufacturer=0
    0x01000000   // iProduct=0, iSerialNumber=0, bNumConfigurations=1
};

// Fixed USB 2.0 device descriptors for the two embedded controllers. DEV0 and
// DEV1 carry distinct idProduct/bcdDevice values so a scoreboard can identify
// which controller answered the host's GET_DESCRIPTOR(DEVICE) request. Served
// on the legacy device path (boot_usb_core_hub / boot_usb_core_fs) via
// usb_ep0_send_device_descriptor(), selected at compile time by USB_DEV_SEL.
const usb_device_descriptor_t usb_dev0_device_descriptor = {
    .bLength            = 18,
    .bDescriptorType    = USB_DESC_DEVICE,
    .bcdUSB             = 0x0200,   // USB 2.0
    .bDeviceClass       = 0xFF,     // DEV0: vendor-specific class
    .bDeviceSubClass    = 0x01,     // DEV0
    .bDeviceProtocol    = 0x01,
    .bMaxPacketSize0    = 64,
    .idVendor           = 0x1234,   // DEV0
    .idProduct          = 0x0001,   // DEV0
    .bcdDevice          = 0x0100,   // DEV0
    .iManufacturer      = 0x01,
    .iProduct           = 0x02,
    .iSerialNumber      = 0x03,
    .bNumConfigurations = 1
};

const usb_device_descriptor_t usb_dev1_device_descriptor = {
    .bLength            = 18,
    .bDescriptorType    = USB_DESC_DEVICE,
    .bcdUSB             = 0x0210,   // DEV1: USB 2.1
    .bDeviceClass       = 0xEF,     // DEV1: miscellaneous class
    .bDeviceSubClass    = 0x02,     // DEV1
    .bDeviceProtocol    = 0x01,
    .bMaxPacketSize0    = 64,
    .idVendor           = 0x5678,   // DEV1
    .idProduct          = 0x0002,   // DEV1
    .bcdDevice          = 0x0200,   // DEV1
    .iManufacturer      = 0x01,
    .iProduct           = 0x02,
    .iSerialNumber      = 0x03,
    .bNumConfigurations = 1
};

// -------------------------------------------------------------------------
// usb_hub_init_and_connect
//
// Enables the hub entity by setting HUB_EN in the hub control register
// (SOC_USB_COMBO_HUB_CONTROL). HUB_CONNECT is deliberately NOT set here - it is
// set separately by usb_hub_connect(), per the reference two-phase sequencing
// (HUB_EN alone first, then HUB_EN|HUB_CONNECT together after a settling
// delay).
//
// This MUST run before the upstream host can ever see USBDC0 or USBDC1 -
// USB_EnableHub is tied 1'b0 at top level, so hub_enable_q is driven by
// ep0_mem(C_HUB_CS)(0) and without this write the hub entity never presents
// itself on the bus, which manifests as a permanent DRES_C-never-set hang.
//
// The descriptor flip-flop array is still writable through the hub aperture
// while the write-lock is deasserted, so this applies a small targeted override
// of the hub DEVICE / QUALIFIER / CONFIGURATION / CLASS descriptors to
// non-default values. The override MUST happen before HUB_CONNECT: the whole
// array freezes only once HUB_EN AND HUB_CONNECT are both set. HUB_EN alone
// (set below) does not lock the array.
//
// NOTE (this RTL): the current EP0 response path may read C_EP0_ROM directly,
// so these shadow writes may no longer change the descriptor RESPONSE. They are
// retained for parity with legacy; any scoreboard effect must be re-validated.
// -------------------------------------------------------------------------
void usb_hub_init_and_connect(void) {
    VPRINTF(LOW, "MCU: usb_hub_init_and_connect - enabling hub entity\n");

    // Clear HUB_CONNECT and HUB_EN first, so the enable is a clean edge even if
    // a previous run left the register set.
    lsu_write_32(USB_HUB_CTRL, 0x00000000u);

    // Override the hub DEVICE descriptor (DataPhase_Buffer_0) BEFORE
    // HUB_CONNECT, while the descriptor flip-flop array is still unlocked.
    // word2 (idVendor | idProduct<<16) and word3 (bcdDevice | iManufacturer<<16
    // | iProduct<<24) are clean full words. iSerialNumber is byte 0 of word4,
    // packed with bNumConfigurations, so it is updated with a read-modify-write
    // of only the low byte.
    lsu_write_32(USB_HUB_DESC_DEV_WORD2, USB_HUB_DESC_DEV_WORD2_VAL);
    lsu_write_32(USB_HUB_DESC_DEV_WORD3, USB_HUB_DESC_DEV_WORD3_VAL);
    uint32_t hub_desc_w4 = lsu_read_32(USB_HUB_DESC_DEV_WORD4);
    hub_desc_w4 = (hub_desc_w4 & 0xFFFFFF00u) | USB_HUB_DESC_DEV_ISERIAL_VAL;
    lsu_write_32(USB_HUB_DESC_DEV_WORD4, hub_desc_w4);
    VPRINTF(LOW, "MCU: hub device-descriptor override readback"
            " w2=0x%x w3=0x%x w4=0x%x\n",
            lsu_read_32(USB_HUB_DESC_DEV_WORD2),
            lsu_read_32(USB_HUB_DESC_DEV_WORD3),
            lsu_read_32(USB_HUB_DESC_DEV_WORD4));

    // Override the hub DEVICE QUALIFIER descriptor (DataPhase_Buffer_3) BEFORE
    // HUB_CONNECT. qw1 is a clean full word (all four bytes are qualifier
    // fields).
    lsu_write_32(USB_HUB_DESC_QUAL_WORD1, USB_HUB_DESC_QUAL_WORD1_VAL);
    VPRINTF(LOW, "MCU: hub device-qualifier override readback qw1=0x%x\n",
            lsu_read_32(USB_HUB_DESC_QUAL_WORD1));

    // Override iConfiguration in the CONFIGURATION descriptor and the
    // OTHER_SPEED_CONFIGURATION descriptor BEFORE HUB_CONNECT. iConfiguration is
    // byte 2 of word1, so it is updated with a read-modify-write of only that
    // byte to preserve bmAttributes and the other fields.
    uint32_t hub_cfg_w1 = lsu_read_32(USB_HUB_DESC_CFG_WORD1);
    hub_cfg_w1 = (hub_cfg_w1 & 0xFF00FFFFu) | ((uint32_t)USB_HUB_DESC_ICONFIG_VAL << 16);
    lsu_write_32(USB_HUB_DESC_CFG_WORD1, hub_cfg_w1);
    uint32_t hub_osc_w1 = lsu_read_32(USB_HUB_DESC_OSC_WORD1);
    hub_osc_w1 = (hub_osc_w1 & 0xFF00FFFFu) | ((uint32_t)USB_HUB_DESC_ICONFIG_VAL << 16);
    lsu_write_32(USB_HUB_DESC_OSC_WORD1, hub_osc_w1);
    VPRINTF(LOW, "MCU: hub config/other-speed iConfiguration override readback"
            " cfg_w1=0x%x osc_w1=0x%x\n",
            lsu_read_32(USB_HUB_DESC_CFG_WORD1),
            lsu_read_32(USB_HUB_DESC_OSC_WORD1));

    // Override the hub CLASS descriptor (DataPhase_Buffer_2) BEFORE HUB_CONNECT.
    // word1 is a clean full-word write.
    lsu_write_32(USB_HUB_DESC_HUB_WORD1, USB_HUB_DESC_HUB_WORD1_VAL);
    VPRINTF(LOW, "MCU: hub class-descriptor override readback hw1=0x%x\n",
            lsu_read_32(USB_HUB_DESC_HUB_WORD1));

    // Enable the hub entity. HUB_CONNECT is set later by usb_hub_connect().
    lsu_write_32(USB_HUB_CTRL, USBHUB_CTRL_HUB_EN_MASK);
    uint32_t hub_ctrl_rb = lsu_read_32(USB_HUB_CTRL);
    VPRINTF(LOW, "MCU: HUB_CTRL after HUB_EN=1 readback = 0x%x\n", hub_ctrl_rb);

    VPRINTF(LOW, "MCU: usb_hub_init_and_connect - HUB_EN set"
            " (HUB_CONNECT deferred to usb_hub_connect())\n");
}

// -------------------------------------------------------------------------
// usb_hub_connect
//
// Connect the hub to the upstream port by setting HUB_CONNECT (together with
// HUB_EN, which must already be set by a prior usb_hub_init_and_connect()
// call). Split out to match the reference two-phase sequencing: HUB_EN must be
// set and settled BEFORE HUB_CONNECT. Call after the device controller is ready
// (boot_usb_core_hub()), since the host begins enumerating hub port 0 as soon
// as the hub connects upstream.
// -------------------------------------------------------------------------
void usb_hub_connect(void) {
    lsu_write_32(USB_HUB_CTRL, USBHUB_CTRL_HUB_EN_MASK | USBHUB_CTRL_HUB_CONNECT_MASK);
    uint32_t hub_ctrl_rb = lsu_read_32(USB_HUB_CTRL);
    VPRINTF(LOW, "MCU: HUB_CTRL after HUB_CONNECT=1 readback = 0x%x\n", hub_ctrl_rb);
    VPRINTF(LOW, "MCU: usb_hub_connect - done\n");
}

// -------------------------------------------------------------------------
// boot_usb_core - Initialize the USB device controller (STANDALONE DEV0)
//
// Hook-based enumeration entry point used by the OCP-recovery and host tests.
// Installs the application's config-descriptor and class-request hooks, sets up
// the EP command/status list and data buffers in SRAM, then configures
// EPLISTSTART, DATABUFSTART, DEVCMDSTAT and interrupt enables so the USB device
// is ready to respond to host enumeration. No hub bring-up (this path runs DEV0
// standalone) and no LPM_SUP force (writes DEVCMDSTAT raw to preserve the
// upstream behaviour byte-for-byte).
//
// SRAM layout:
//   0x000-0x00F: EP0 command/status list (4 words)
//   0x010-0x0FF: Other EP entries (zeroed/disabled)
//   0x100-0x107: SETUP data buffer (8 bytes)
//   0x140-0x17F: EP0 OUT data buffer (64 bytes)
//   0x180-0x1BF: EP0 IN data buffer (64 bytes)
// -------------------------------------------------------------------------
void boot_usb_core(usb_config_descriptor_provider_t config_desc_fn,
                   usb_class_request_handler_t class_req_fn) {
    uint32_t reg_data;

    // Install the application's USB config-descriptor and class-request hooks
    // BEFORE any host enumeration can begin. Passing 0 selects the built-in
    // defaults (no config descriptor / STALL class requests).
    usb_config_descriptor_override = config_desc_fn;
    usb_class_request_override     = class_req_fn;

    VPRINTF(LOW, "MCU: boot_usb_core - initializing USB device controller\n");

    // Read DEVCMDSTAT to check initial state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT initial = 0x%x\n", reg_data);

    // --- Step 0: Initialize SRAM via DMA port ---

    // EP0 OUT entry: Active=1, NBytes=8 (for SETUP), addr_offset = 0x140>>6 = 5
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    // EP0 SETUP buffer address entry: addr_offset = 0x100>>6 = 4
    uint32_t ep0_setup_entry = USB_EP_ENTRY_ADDR(USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    // EP0 IN entry: Active=0, NBytes=0, addr_offset = 0x180>>6 = 6
    uint32_t ep0_in_entry = USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    lsu_write_32(USB_DEV_EPLISTSTART, 0x00000000);

    // --- Step 2: Set data buffer page address ---
    lsu_write_32(USB_DEV_DATABUFSTART, 0x00000000);

    // --- Step 3: Wait for VBUS ---
    VPRINTF(LOW, "MCU: Wait VBUS\n");
    while(!(lsu_read_32(USB_DEV_DEVCMDSTAT) & DEV0_CSR_DEVCMDSTAT_VBUS_DEBOUNCED_MASK));

    // --- Step 4: Enable device ---
    // HS link-up: do NOT set FORCE_FULLSPEED. The device controller will
    // perform HS chirp at the next bus reset.
    reg_data = DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK
             | DEV0_CSR_DEVCMDSTAT_DCON_MASK;
    lsu_write_32(USB_DEV_DEVCMDSTAT, reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n", reg_data);

    // Read back to confirm
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 5: Enable interrupts ---
    lsu_write_32(USB_DEV_INTEN,
        DEV0_CSR_INTSTAT_DEV_INT_MASK |
        DEV0_CSR_INTSTAT_EP0OUT_MASK  |
        DEV0_CSR_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        DEV0_CSR_INTSTAT_DEV_INT_MASK | DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK);

    // --- Step 6: Clear pending interrupts ---
    lsu_write_32(USB_DEV_INTSTAT, USB_DEV0_IMPLEMENTED_INTERRUPT_MASK);

    VPRINTF(LOW, "MCU: boot_usb_core - done\n");
}

// -------------------------------------------------------------------------
// boot_usb_core_hub - Initialize the USB device controller in HUB+DEVICE mode
//
// Legacy device entry point. Brings the on-chip hub up (usb_hub_init_and_connect
// at Step -1), configures the EP list/SRAM buffers, and enables device mode with
// FORCE_VBUS and FORCE_NEEDCLK set during bring-up (so the UTMI clock keeps
// running through enumeration; suspend tests clear FORCE_NEEDCLK later via
// usb_allow_clock_stop()). DEVCMDSTAT is written through usb_devcmdstat_write()
// so LPM_SUP is forced. HUB_CONNECT is NOT asserted here - the test calls
// usb_hub_connect() once the device controller is fully programmed.
// -------------------------------------------------------------------------
void boot_usb_core_hub(void) {
    uint32_t reg_data;

    VPRINTF(LOW, "MCU: boot_usb_core_hub - initializing USB device controller (hub+device)\n");

    // --- Step -1: bring up the compound hub (phase 1 of 2) ---
    // USB_EnableHub is tied 1'b0 at top level, so the hub entity is brought up
    // entirely at runtime by firmware. This programs the hub descriptor
    // overrides and sets HUB_EN; it must run before the host can ever see the
    // embedded device controllers. HUB_CONNECT is asserted separately, later,
    // by usb_hub_connect() once the device controller is also ready.
    usb_hub_init_and_connect();

    // --- Step 0: Initialize SRAM via DMA port ---

    // EP0 OUT entry: Active=1, NBytes=8 (for SETUP). USB_EP_ENTRY_ABS_ADDR
    // subtracts the controller's MEM base before the >>6 shift, so the
    // AddrOffset field is offset-relative for BOTH DEV0 (base 0x3000_0000) and
    // DEV1 (base 0x3001_0000). This must match the offset-relative form used by
    // usb_ep0_reinit() after a bus reset; otherwise DEV1 bit16 of the absolute
    // address would leak into AddrOffset bit10 and point the buffers outside the
    // DEV1 SRAM window (see USB_EP_ENTRY_ABS_ADDR in usb.h).
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    uint32_t ep0_setup_entry = USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    uint32_t ep0_in_entry = USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    // On this RTL the SRAM is a dedicated dense memory (USB_DMA_BASE_ADDR) and
    // EPLISTSTART is relative to it, so it is 0.
    lsu_write_32(USB_DEV_EPLISTSTART, 0x00000000);


    // --- Step 2: Set data buffer page address ---
    lsu_write_32(USB_DEV_DATABUFSTART, 0x00000000);

    // --- Step 3: Enable device ---
    // HS link-up: do NOT set FORCE_FULLSPEED. FORCE_NEEDCLK keeps the UTMI
    // clock running during bring-up (suspend tests clear it later). Composed
    // from literal masks and written through usb_devcmdstat_write() so LPM_SUP
    // is (re-)forced rather than cleared.
    reg_data = DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK
    //         | DEV0_CSR_DEVCMDSTAT_FORCE_VBUS_MASK
             | DEV0_CSR_DEVCMDSTAT_FORCE_NEEDCLK_MASK
             | DEV0_CSR_DEVCMDSTAT_DCON_MASK;
    usb_devcmdstat_write(reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n",
            reg_data | DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK);

    // Read back to confirm
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 4: Enable interrupts ---
    lsu_write_32(USB_DEV_INTEN,
        DEV0_CSR_INTSTAT_DEV_INT_MASK |
        DEV0_CSR_INTSTAT_EP0OUT_MASK  |
        DEV0_CSR_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        DEV0_CSR_INTSTAT_DEV_INT_MASK | DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK);

    // --- Step 5: Clear pending interrupts ---
    lsu_write_32(USB_DEV_INTSTAT, USB_DEV0_IMPLEMENTED_INTERRUPT_MASK);

    VPRINTF(LOW, "MCU: boot_usb_core_hub - done\n");
}

// -------------------------------------------------------------------------
// boot_usb_core_fs - Initialize the USB device controller in HUB+DEVICE FS mode
//
// Identical to boot_usb_core_hub() except that DEVCMDSTAT bit 21
// (FORCE_FULLSPEED - the legacy PFSC bit) is set before connecting, which
// suppresses the device-side K-chirp so the UTMI TX is ready for FS packet
// exchange immediately. Use in tests that run with a FS-only host VIP
// (high_speed_capable=0) where no chirp reply is driven and the ~2.2ms chirp
// timeout would stall the first SETUP. DO NOT use when HS operation is required.
// -------------------------------------------------------------------------
void boot_usb_core_fs(void) {
    uint32_t reg_data;

    VPRINTF(LOW, "MCU: boot_usb_core_fs - initializing USB device controller (hub+device, FS-only)\n");

    // --- Step -1: bring up the compound hub (phase 1 of 2) ---
    usb_hub_init_and_connect();

    // --- Step 0: Initialize SRAM via DMA port ---
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x000, ep0_out_entry);
    VPRINTF(LOW, "MCU: EP0 OUT entry = 0x%x\n", ep0_out_entry);

    uint32_t ep0_setup_entry = USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x004, ep0_setup_entry);

    uint32_t ep0_in_entry = USB_EP_ENTRY_ABS_ADDR(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + 0x008, ep0_in_entry);

    // Reserved word
    lsu_write_32(USB_DMA_BASE_ADDR + 0x00C, 0x00000000);

    // Zero out remaining EP entries (EP1-EP4, 4 words each)
    for (uint32_t i = 0x010; i < 0x100; i += 4) {
        lsu_write_32(USB_DMA_BASE_ADDR + i, 0x00000000);
    }
    VPRINTF(LOW, "MCU: EP list and SRAM buffers initialized\n");

    // --- Step 1: Set EP list base address ---
    lsu_write_32(USB_DEV_EPLISTSTART, 0x00000000);

    // --- Step 2: Set data buffer page address ---
    lsu_write_32(USB_DEV_DATABUFSTART, 0x00000000);

    // --- Step 3: Enable device in FS-only mode ---
    // FORCE_FULLSPEED (bit 21) suppresses the device-side K-chirp so the UTMI
    // TX initializes immediately for FS. Written through usb_devcmdstat_write()
    // so LPM_SUP is (re-)forced.
    reg_data = DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK
             | DEV0_CSR_DEVCMDSTAT_FORCE_VBUS_MASK
             | DEV0_CSR_DEVCMDSTAT_FORCE_NEEDCLK_MASK
             | DEV0_CSR_DEVCMDSTAT_DCON_MASK
             | DEV0_CSR_DEVCMDSTAT_FORCE_FULLSPEED_MASK;
    usb_devcmdstat_write(reg_data);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT written = 0x%x\n",
            reg_data | DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK);

    // Read back to confirm
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT readback = 0x%x\n", reg_data);

    // --- Step 4: Enable interrupts ---
    lsu_write_32(USB_DEV_INTEN,
        DEV0_CSR_INTSTAT_DEV_INT_MASK |
        DEV0_CSR_INTSTAT_EP0OUT_MASK  |
        DEV0_CSR_INTSTAT_EP0IN_MASK);
    VPRINTF(LOW, "MCU: USB INTEN written = 0x%x\n",
        DEV0_CSR_INTSTAT_DEV_INT_MASK | DEV0_CSR_INTSTAT_EP0OUT_MASK | DEV0_CSR_INTSTAT_EP0IN_MASK);

    // --- Step 5: Clear pending interrupts ---
    lsu_write_32(USB_DEV_INTSTAT, USB_DEV0_IMPLEMENTED_INTERRUPT_MASK);

    VPRINTF(LOW, "MCU: boot_usb_core_fs - done\n");
}

void usb_ep0_reinit(void) {
    uint32_t ep0_out_entry = USB_EP_ENTRY_ACTIVE
                           | USB_EP_ENTRY_NBYTES(8)
                           | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out_entry);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x004,
                 USB_EP_ENTRY_ADDR(USB_SRAM_SETUP_BUF_OFFSET));
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008,
                 USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET));
    VPRINTF(LOW, "MCU: usb_ep0_reinit - EP0 entries restored (EP0OUT=0x%x)\n", ep0_out_entry);
}

void usb_handle_bus_reset(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    if (!(cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK)) {
        return;
    }
    VPRINTF(LOW, "MCU: USB bus reset detected\n");
    usb_bus_reset_count++;
    usb_ep0_in_pending_latched = 0u;
    // Bus reset returns device address to 0 per USB spec; update shadow so all
    // subsequent DEVCMDSTAT RMW writes carry the reset address.
    usb_dev_addr_shadow = 0;
    // USB 2.0 section 9.1.1.3: reset returns the device to the Default state
    // with no configuration selected. Mirror that in the firmware shadows.
    usb_current_config = 0;
    usb_remote_wakeup_enabled = false;
    // Clear DRES_C (W1C)
    usb_devcmdstat_write(cmd | DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);
    usb_ep0_reinit();
    // Reset device address to 0 per USB spec
    cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    cmd &= ~DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK;
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
    const uint8_t *byte_data = (const uint8_t *)data;
    uint32_t nwords = (nbytes + 3) / 4;

    for (uint32_t i = 0; i < nwords; i++) {
        uint32_t word = 0;
        uint32_t base = i * 4;

        for (uint32_t byte = 0; byte < 4; byte++) {
            uint32_t idx = base + byte;
            uint8_t val = (idx < nbytes) ? byte_data[idx] : 0u;
            word |= ((uint32_t)val) << (byte * 8);
        }

        lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP0_IN_BUF_OFFSET + (i * 4), word);
    }

    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_NBYTES(nbytes)
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    // NOTE: VPRINTF intentionally omitted from EP0 IN arming hot-path.
    // Host VIP only gives ~5us between SETUP-ACK and giving up on IN polling;
    // adding logging here delays the arm beyond that window for back-to-back
    // SETUPs (e.g. GET_STATUS following GET_DESCRIPTOR).
}

void usb_ep0_send_device_descriptor(uint32_t nbytes) {
    // Select the descriptor of the controller currently being serviced. This
    // follows the RUNTIME active device so a dual-controller image serves the
    // correct per-device descriptor; for single-device tests usb_active_dev
    // stays at its USB_DEV_SEL default, so behaviour is unchanged.
    const usb_device_descriptor_t *desc = (usb_active_dev == 1)
                                        ? &usb_dev1_device_descriptor
                                        : &usb_dev0_device_descriptor;

    // The descriptor is 4-byte aligned and its packed wire layout is already
    // little-endian, so it can be copied word-by-word straight into the EP0 IN
    // SRAM buffer via the existing send path.
    usb_ep0_send_data((const uint32_t *)desc, nbytes);
}

void usb_ep0_send_zlp(void) {
    uint32_t ep0_in = USB_EP_ENTRY_ACTIVE
                    | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
}

void usb_ep0_stall(void) {
    uint32_t ep0_in  = USB_EP_ENTRY_STALL | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_IN_BUF_OFFSET);
    uint32_t ep0_out = USB_EP_ENTRY_STALL | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008, ep0_in);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
    VPRINTF(LOW, "MCU: EP0 stalled\n");
}

void usb_ep0_arm_out(void) {
    uint32_t ep0_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP0_OUT_BUF_OFFSET);
    lsu_write_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000, ep0_out);
}

void usb_clear_setup_bit(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    usb_devcmdstat_write(cmd | DEV0_CSR_DEVCMDSTAT_SETUP_MASK);
}

uint8_t usb_is_configured(void) {
    // USB 2.0 sec 9.4.7 / 9.1.1.5: the device is in the Configured state once a
    // SET_CONFIGURATION with a non-zero configuration value has been accepted.
    // usb_current_config tracks that value (cleared on bus reset).
    return (usb_current_config != 0u) ? 1u : 0u;
}

void usb_legacy_ep0_capture_snapshot(
    usb_legacy_ep0_snapshot_t *snapshot)
{
    if (snapshot == 0) {
        return;
    }

    snapshot->publish_sequence = ++usb_snapshot_publish_sequence;
    snapshot->setup_word0 = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET);
    snapshot->setup_word1 = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_SETUP_BUF_OFFSET + 4u);
    snapshot->ep0_out_descriptor = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000u);
    snapshot->ep0_setup_descriptor = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x004u);
    snapshot->ep0_in_descriptor = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008u);
    snapshot->ep0_reserved_descriptor = lsu_read_32(
        USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x00Cu);
    snapshot->devcmdstat = lsu_read_32(USB_DEV_DEVCMDSTAT);
    snapshot->intstat = lsu_read_32(USB_DEV_INTSTAT);
    snapshot->inten = lsu_read_32(USB_DEV_INTEN);
    snapshot->configuration = (uint32_t)usb_current_config;
    snapshot->transfers_handled = usb_transfers_handled;
    snapshot->bus_reset_count = usb_bus_reset_count;
    snapshot->ep0_irq_count = usb_ep0_irq_count;
    snapshot->ep0_out_irq_count = usb_ep0_out_irq_count;
    snapshot->ep0_in_irq_count = usb_ep0_in_irq_count;
    snapshot->setup_dispatch_count = usb_setup_dispatch_count;
    snapshot->snapshot_version = USB_LEGACY_EP0_SNAPSHOT_VERSION;
}

static uint32_t usb_legacy_ep0_snapshot_header(
    uint8_t magic,
    usb_legacy_ep0_snapshot_state_t state,
    uint8_t field_index,
    uint16_t generation)
{
    return
        ((uint32_t)magic << 24) |
        (((uint32_t)state & 0x3u) << 22) |
        (((uint32_t)field_index & 0x1Fu) << 17) |
        (uint32_t)generation;
}

static void usb_legacy_ep0_publish_field(
    usb_legacy_ep0_snapshot_state_t state,
    uint8_t field_index,
    uint16_t generation,
    uint32_t value)
{
    uint32_t header = usb_legacy_ep0_snapshot_header(
        USB_LEGACY_EP0_DATA_MAGIC,
        state,
        field_index,
        generation);
    uint32_t expected_ack = usb_legacy_ep0_snapshot_header(
        USB_LEGACY_EP0_ACK_MAGIC,
        state,
        field_index,
        generation);

    lsu_write_32(
        SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0,
        value);
    lsu_write_32(
        SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        header);
    while (lsu_read_32(
            SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0) !=
            expected_ack) {
    }

    lsu_write_32(
        SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        0u);
    while (lsu_read_32(
            SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0) != 0u) {
    }
}

static void usb_legacy_ep0_publish_snapshot(
    const usb_legacy_ep0_snapshot_t *snapshot,
    uint16_t generation,
    usb_legacy_ep0_snapshot_state_t state)
{
    if (snapshot == 0) {
        return;
    }

    usb_legacy_ep0_publish_field(
        state, 0u, generation,
        snapshot->publish_sequence);
    usb_legacy_ep0_publish_field(
        state, 1u, generation,
        snapshot->setup_word0);
    usb_legacy_ep0_publish_field(
        state, 2u, generation,
        snapshot->setup_word1);
    usb_legacy_ep0_publish_field(
        state, 3u, generation,
        snapshot->ep0_out_descriptor);
    usb_legacy_ep0_publish_field(
        state, 4u, generation,
        snapshot->ep0_setup_descriptor);
    usb_legacy_ep0_publish_field(
        state, 5u, generation,
        snapshot->ep0_in_descriptor);
    usb_legacy_ep0_publish_field(
        state, 6u, generation,
        snapshot->ep0_reserved_descriptor);
    usb_legacy_ep0_publish_field(
        state, 7u, generation,
        snapshot->devcmdstat);
    usb_legacy_ep0_publish_field(
        state, 8u, generation,
        snapshot->intstat);
    usb_legacy_ep0_publish_field(
        state, 9u, generation,
        snapshot->inten);
    usb_legacy_ep0_publish_field(
        state, 10u, generation,
        snapshot->configuration);
    usb_legacy_ep0_publish_field(
        state, 11u, generation,
        snapshot->transfers_handled);
    usb_legacy_ep0_publish_field(
        state, 12u, generation,
        snapshot->bus_reset_count);
    usb_legacy_ep0_publish_field(
        state, 13u, generation,
        snapshot->ep0_irq_count);
    usb_legacy_ep0_publish_field(
        state, 14u, generation,
        snapshot->ep0_out_irq_count);
    usb_legacy_ep0_publish_field(
        state, 15u, generation,
        snapshot->ep0_in_irq_count);
    usb_legacy_ep0_publish_field(
        state, 16u, generation,
        snapshot->setup_dispatch_count);
    usb_legacy_ep0_publish_field(
        state, 17u, generation,
        snapshot->snapshot_version);
}

void usb_legacy_ep0_publish_baseline(uint16_t generation)
{
    usb_legacy_ep0_snapshot_t snapshot;

    // Baseline publication is observational only. The successful marker
    // transfer has already completed normal legacy servicing and armed EP0 for
    // the next request; changing controller state here would alter the path
    // being verified.
    usb_legacy_ep0_capture_snapshot(&snapshot);
    usb_legacy_ep0_publish_snapshot(
        &snapshot,
        generation,
        USB_LEGACY_EP0_SNAPSHOT_BASELINE);
    VPRINTF(LOW,
            "MCU: EP0 observer baseline gen=%u EP0OUT=0x%08x EP0IN=0x%08x DEVCMDSTAT=0x%08x INTSTAT=0x%08x\n",
            generation,
            snapshot.ep0_out_descriptor,
            snapshot.ep0_in_descriptor,
            snapshot.devcmdstat,
            snapshot.intstat);
    usb_baseline_ready_generation = generation;
    usb_baseline_ready_pending = 1u;
}

void usb_legacy_ep0_publish_post_snapshot(uint16_t generation)
{
    usb_legacy_ep0_snapshot_t snapshot;

    usb_legacy_ep0_capture_snapshot(&snapshot);
    usb_legacy_ep0_publish_snapshot(
        &snapshot,
        generation,
        USB_LEGACY_EP0_SNAPSHOT_POST);
    lsu_write_32(
        SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0,
        snapshot.publish_sequence);
    lsu_write_32(
        SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
        usb_legacy_ep0_snapshot_header(
            USB_LEGACY_EP0_READY_MAGIC,
            USB_LEGACY_EP0_SNAPSHOT_POST,
            USB_LEGACY_EP0_READY_FIELD,
            generation));
}

uint32_t usb_legacy_ep0_get_setup_dispatch_count(void)
{
    return usb_setup_dispatch_count;
}

uint32_t usb_legacy_ep0_get_bus_reset_count(void)
{
    return usb_bus_reset_count;
}

void usb_set_device_address(uint8_t addr) {
    usb_dev_addr_shadow = (uint8_t)(addr & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK);
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    usb_devcmdstat_write(cmd);
}

void usb_set_device_connect(uint8_t connected) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

    cmd &= ~(DEV0_CSR_DEVCMDSTAT_SETUP_MASK |
             DEV0_CSR_DEVCMDSTAT_DCON_C_MASK |
             DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK |
             DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);
    if (connected != 0u) {
        while ((lsu_read_32(USB_DEV_DEVCMDSTAT) &
                DEV0_CSR_DEVCMDSTAT_VBUS_DEBOUNCED_MASK) == 0u) {
        }
        cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
        cmd &= ~(DEV0_CSR_DEVCMDSTAT_SETUP_MASK |
                 DEV0_CSR_DEVCMDSTAT_DCON_C_MASK |
                 DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK |
                 DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);
        cmd |= DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK |
               DEV0_CSR_DEVCMDSTAT_DCON_MASK;
    } else {
        cmd &= ~DEV0_CSR_DEVCMDSTAT_DCON_MASK;
    }
    usb_devcmdstat_write(cmd);
}

// -------------------------------------------------------------------------
// usb_allow_clock_stop
//
// Clear FORCE_NEEDCLK so the device controller can drop its unconditional clock
// request and actually reach suspend. boot_usb_core_hub() / boot_usb_core_fs()
// set FORCE_NEEDCLK=1 to keep the UTMI clock running during bring-up, which is
// what the enumeration-only tests want; while it is set, utmi_suspendm never
// falls and a suspend/resume checker never sees its edge. Call this after
// enumeration completes and before the host-side suspend stimulus is armed.
// FORCE_VBUS is left untouched.
// -------------------------------------------------------------------------
void usb_allow_clock_stop(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
    cmd &= ~DEV0_CSR_DEVCMDSTAT_FORCE_NEEDCLK_MASK;
    usb_devcmdstat_write(cmd);
    VPRINTF(LOW, "MCU: FORCE_NEEDCLK cleared (DEVCMDSTAT=0x%x)\n",
            lsu_read_32(USB_DEV_DEVCMDSTAT));
}

// -------------------------------------------------------------------------
// usb_request_remote_wakeup
//
// Drives a device-initiated remote wakeup (resume K upstream). The trigger is
// not a "set a bit" operation: usbreg_remotewakeup is raised when a DEVCMDSTAT
// write presents bit 17 (DSUS) as 0 while the controller is currently
// suspended. A plain OR-in RMW reads DSUS back as 1 while suspended and so
// never triggers it; bit 17 must be masked off. The same write acknowledges
// DSUS_C (W1C); DRES_C, SETUP and DCON_C are masked off so the caller's pending
// events survive. Returns true if the wakeup was driven, false if the
// controller was not suspended.
// -------------------------------------------------------------------------
bool usb_request_remote_wakeup(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

    if ((cmd & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) == 0u) {
        VPRINTF(LOW, "MCU: remote wakeup skipped, controller not suspended (DEVCMDSTAT=0x%x)\n",
                cmd);
        return false;
    }

    // Do not disturb write-1-clear events that the caller still needs.
    cmd &= ~(DEV0_CSR_DEVCMDSTAT_SETUP_MASK
             | DEV0_CSR_DEVCMDSTAT_DCON_C_MASK
             | DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);

    // The wakeup command itself: DSUS driven to 0 while suspended.
    cmd &= ~DEV0_CSR_DEVCMDSTAT_DSUS_MASK;

    // Acknowledge the suspend-change event in the same write.
    cmd |= DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK;

    usb_devcmdstat_write(cmd);
    VPRINTF(LOW, "MCU: remote wakeup requested (wrote DEVCMDSTAT=0x%x, reads back 0x%x)\n",
            cmd, lsu_read_32(USB_DEV_DEVCMDSTAT));
    return true;
}

// -------------------------------------------------------------------------
// usb_request_lpm_remote_wakeup
//
// Device-initiated exit from L1 (LPM Sleep), the L1 analogue of
// usb_request_remote_wakeup(). usbreg_lpmremotewakeup is asserted when a
// DEVCMDSTAT write presents bit 19 (LPM_SUS) as 0 while both reg_dev_lpm_suspend
// AND reg_dev_lpm_remote_wake are 1 (the latter is the host-granted bRemoteWake
// from the LPM token), so both bits are checked here before the write.
// -------------------------------------------------------------------------
bool usb_request_lpm_remote_wakeup(void) {
    uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

    if ((cmd & DEV0_CSR_DEVCMDSTAT_LPM_SUS_MASK) == 0u) {
        VPRINTF(LOW, "MCU: L1 wakeup skipped, controller not in L1 (DEVCMDSTAT=0x%x)\n",
                cmd);
        return false;
    }
    if ((cmd & DEV0_CSR_DEVCMDSTAT_LPM_REWP_MASK) == 0u) {
        VPRINTF(LOW, "MCU: L1 wakeup skipped, host did not grant bRemoteWake (DEVCMDSTAT=0x%x)\n",
                cmd);
        return false;
    }

    // Do not disturb write-1-clear events that the caller still needs.
    cmd &= ~(DEV0_CSR_DEVCMDSTAT_SETUP_MASK
             | DEV0_CSR_DEVCMDSTAT_DCON_C_MASK
             | DEV0_CSR_DEVCMDSTAT_DRES_C_MASK);

    // The wakeup command itself: LPM_SUS driven to 0 while in L1.
    cmd &= ~DEV0_CSR_DEVCMDSTAT_LPM_SUS_MASK;

    // Acknowledge the suspend-change event in the same write. DSUS_C is shared
    // between the L2 and L1 state changes in this IP.
    cmd |= DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK;

    usb_devcmdstat_write(cmd);
    VPRINTF(LOW, "MCU: L1 remote wakeup requested (wrote DEVCMDSTAT=0x%x, reads back 0x%x)\n",
            cmd, lsu_read_32(USB_DEV_DEVCMDSTAT));
    return true;
}

void usb_dump_state(const char *tag) {
    const char *label = (tag != 0) ? tag : "state";
    uint32_t reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    uint32_t intstat = lsu_read_32(USB_DEV_INTSTAT);
    uint32_t ep0_out = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
    uint32_t ep0_in = lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

    VPRINTF(LOW,
            "MCU: USB %s DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
            label, reg_data, intstat, ep0_out, ep0_in, (int)usb_transfers_handled);
}

uint32_t usb_event_loop(uint32_t max_iters, uint32_t expected_transfers) {
    for (uint32_t poll_count = 0; (max_iters == 0u) || (poll_count < max_iters); poll_count++) {
        uint32_t reg_data;

        usb_handle_bus_reset();

        reg_data = lsu_read_32(USB_DEV_INTSTAT);
        if ((reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) != 0u) {
            if (usb_ep0_in_pending_latched == 0u) {
                usb_ep0_in_irq_count++;
                usb_ep0_irq_count++;
            }
            usb_ep0_in_pending_latched = 1u;
        } else {
            usb_ep0_in_pending_latched = 0u;
        }

        if ((reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) != 0u) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            VPRINTF(LOW, "MCU: DEV_INT - DEVCMDSTAT = 0x%x\n", cmd);
            if ((cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) != 0u) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV_INTSTAT,
                         DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if ((reg_data & DEV0_CSR_INTSTAT_EP0OUT_MASK) != 0u) {
            usb_ep0_out_irq_count++;
            usb_ep0_irq_count++;
            lsu_write_32(USB_DEV_INTSTAT,
                         DEV0_CSR_INTSTAT_EP0OUT_MASK);

            if ((lsu_read_32(USB_DEV_DEVCMDSTAT) &
                 DEV0_CSR_DEVCMDSTAT_SETUP_MASK) != 0u) {
                (void)usb_handle_control_transfer();
                usb_transfers_handled++;

                if ((expected_transfers != 0) && (usb_transfers_handled >= expected_transfers)) {
                    break;
                }
            }
        }

        if ((USB_EVENT_LOOP_DIAG_PERIOD != 0u)
            && (poll_count > 0u)
            && ((poll_count % USB_EVENT_LOOP_DIAG_PERIOD) == 0u)) {
            VPRINTF(LOW,
                    "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
                    (int)poll_count,
                    lsu_read_32(USB_DEV_DEVCMDSTAT),
                    lsu_read_32(USB_DEV_INTSTAT),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000),
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008),
                    (int)usb_transfers_handled);
        }

        if (usb_baseline_ready_pending != 0u) {
            // Publish readiness after a complete poll iteration. Firmware then
            // immediately enters the next iteration, minimizing the interval
            // between the semantic ready indication and EP0 service.
            lsu_write_32(
                SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0,
                usb_snapshot_publish_sequence);
            lsu_write_32(
                SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1,
                usb_legacy_ep0_snapshot_header(
                    USB_LEGACY_EP0_READY_MAGIC,
                    USB_LEGACY_EP0_SNAPSHOT_BASELINE,
                    USB_LEGACY_EP0_READY_FIELD,
                    usb_baseline_ready_generation));
            usb_baseline_ready_pending = 0u;
        }

        // mcu_sleep removed from poll loop: at 25ns/iter it costs ~3-4us
        // between consecutive polls, which exceeds the host VIP IN-retry
        // budget after a SETUP ACK. Busy-poll keeps SETUP detection within
        // 1 us of the EP0OUT interrupt.
    }
    return usb_transfers_handled;
}

// -------------------------------------------------------------------------
// usb_handle_control_transfer
//
// Reads the current SETUP packet from SRAM and dispatches it by decoding
// bmRequestType (type + recipient) and bRequest. This is the unified SUPERSET
// handler that services BOTH the legacy device family and the upstream OCP/host
// family on disjoint branches:
//   - Standard/Device GET_DESCRIPTOR(DEVICE): serves the legacy compile-time
//     selected dev0/dev1 device descriptor (usb_ep0_send_device_descriptor).
//   - Standard/Device GET_DESCRIPTOR(CONFIGURATION): serves the application's
//     config descriptor via the usb_get_config_descriptor hook (OCP/host path).
//   - Standard/Device GET_STATUS / SET_FEATURE / CLEAR_FEATURE: legacy
//     self-powered + DEVICE_REMOTE_WAKEUP shadow behaviour.
//   - Class requests: dispatched to the usb_handle_class_request hook (OCP).
// usb_clear_setup_bit() is always called last, per Integration Guide 4.2.4.1.1.
// Returns true if handled without stall, false otherwise.
// -------------------------------------------------------------------------
bool usb_handle_control_transfer(void) {
    usb_setup_pkt_t pkt;
    bool handled = false;
    uint32_t intstat;

    usb_setup_dispatch_count++;
    usb_read_setup_packet(&pkt);

    uint8_t req_type  = USB_BMREQTYPE_TYPE(pkt.bmRequestType);
    uint8_t recipient = USB_BMREQTYPE_RECIPIENT(pkt.bmRequestType);

    // Clear EP0 IN interrupt before programming the response. Reset the edge
    // latch at the same operation so a subsequent completion can increment the
    // sticky counter even if no polling iteration observed the low interval.
    intstat = lsu_read_32(USB_DEV_INTSTAT);
    if (((intstat & DEV0_CSR_INTSTAT_EP0IN_MASK) != 0u) &&
        (usb_ep0_in_pending_latched == 0u)) {
        usb_ep0_in_irq_count++;
        usb_ep0_irq_count++;
    }
    lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
    usb_ep0_in_pending_latched = 0u;

    if (req_type == USB_TYPE_STANDARD) {
        if (recipient == USB_RECIP_DEVICE) {
            switch (pkt.bRequest) {
                case USB_REQ_GET_DESCRIPTOR: {
                    uint8_t desc_type = (uint8_t)((pkt.wValue >> 8) & 0xFF);
                    const uint8_t *config_desc = 0;
                    uint16_t config_len = 0;
                    uint32_t nbytes = 0;
                    bool have_descriptor = false;

                    if (desc_type == USB_DESC_DEVICE) {
                        // Legacy device path: serve the compile-time-selected
                        // dev0/dev1 device descriptor. The OCP/host family never
                        // issues GET_DESCRIPTOR(DEVICE), so this branch is
                        // exclusive to the device tests.
                        nbytes = (pkt.wLength < 18u) ? pkt.wLength : 18u;
                        usb_ep0_send_device_descriptor(nbytes);
                        have_descriptor = true;
                    } else if (desc_type == USB_DESC_CONFIGURATION) {
                        // Hook path (OCP/host): serve the application's config
                        // descriptor if one is installed.
                        config_desc = usb_get_config_descriptor(&config_len);
                        if ((config_desc != 0) && (config_len != 0u)) {
                            nbytes = (pkt.wLength < config_len) ? pkt.wLength : config_len;
                            usb_ep0_send_data((const uint32_t *)config_desc, nbytes);
                            have_descriptor = true;
                        }
                    }

                    if (have_descriptor) {
                        usb_ep0_arm_out();
                        // Enable IntOnNAK_CO for status-phase detection
                        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
                        cmd |=  DEV0_CSR_DEVCMDSTAT_INTONNAK_CO_MASK;
                        cmd &= ~DEV0_CSR_DEVCMDSTAT_INTONNAK_CI_MASK;
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
                    // bit[0]=Self-Powered (1, these embedded controllers report
                    // self-powered), bit[1]=Remote Wakeup (reflects the
                    // DEVICE_REMOTE_WAKEUP feature shadow). Response is 0x0003
                    // once remote wakeup is enabled and 0x0001 otherwise.
                    uint32_t status_buf =
                        0x00000001u
                        | (usb_remote_wakeup_enabled ? 0x00000002u : 0x00000000u);
                    usb_ep0_send_data(&status_buf, 2);
                    usb_ep0_arm_out();
                    handled = true;
                    break;
                }
                case USB_REQ_CLEAR_FEATURE:
                    // Standard device CLEAR_FEATURE(DEVICE_REMOTE_WAKEUP):
                    // clear the remote-wakeup shadow and ACK with a ZLP status
                    // phase. Any other feature selector is unsupported here.
                    if (pkt.wValue == USB_FEATURE_DEVICE_REMOTE_WAKEUP) {
                        usb_remote_wakeup_enabled = false;
                        usb_ep0_send_zlp();
                        usb_ep0_arm_out();
                        handled = true;
                        VPRINTF(LOW, "MCU: USB CLEAR_FEATURE(DEVICE_REMOTE_WAKEUP)"
                                " - remote wakeup disabled\n");
                    } else {
                        VPRINTF(LOW, "MCU: USB Unhandled Standard/Device CLEAR_FEATURE"
                                " wValue=0x%04x - stalling\n", pkt.wValue);
                        usb_ep0_stall();
                    }
                    break;
                case USB_REQ_SET_FEATURE:
                    // Standard device SET_FEATURE(DEVICE_REMOTE_WAKEUP): set the
                    // remote-wakeup shadow and ACK with a ZLP status phase. A
                    // subsequent GET_STATUS then returns bit[1]=1 (0x0002). Any
                    // other feature selector is unsupported.
                    if (pkt.wValue == USB_FEATURE_DEVICE_REMOTE_WAKEUP) {
                        usb_remote_wakeup_enabled = true;
                        usb_ep0_send_zlp();
                        usb_ep0_arm_out();
                        handled = true;
                        VPRINTF(LOW, "MCU: USB SET_FEATURE(DEVICE_REMOTE_WAKEUP)"
                                " - remote wakeup enabled\n");
                    } else {
                        VPRINTF(LOW, "MCU: USB Unhandled Standard/Device SET_FEATURE"
                                " wValue=0x%04x - stalling\n", pkt.wValue);
                        usb_ep0_stall();
                    }
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
                    // Standard device SET_CONFIGURATION: wValue low byte is the
                    // configuration value. The device descriptor declares
                    // bNumConfigurations=1, so accept 0 (unconfigure) or 1 and
                    // stall any other value per USB 2.0 section 9.4.7.
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
        if (usb_handle_class_request(&pkt)) {
            handled = true;
        } else {
            VPRINTF(LOW, "MCU: USB Unhandled Class request recipient=%d bRequest=0x%02x"
                    " - stalling\n", recipient, pkt.bRequest);
            usb_ep0_stall();
        }
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
    // This must happen quickly: host VIP retries IN tokens for only ~5us before
    // giving up and sending the next SETUP, which will be NAKed by the DUT IP
    // unless the SETUP bit is already cleared.
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

// File contains AI-generated response based on internal company sources
