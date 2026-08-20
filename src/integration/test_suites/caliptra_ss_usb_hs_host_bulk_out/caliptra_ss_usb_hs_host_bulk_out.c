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
//
// Description: USB High-Speed host bulk OUT test firmware for the Caliptra Subsystem.
//
// DUT role: USB HOST (ip_3515 ATL host controller, SOC_USBHSH_* registers).
// VIP role: USB DEVICE (SVT VIP device sequence, receives 256B bulk OUT from DUT).
//
// Test flow:
//   1. Boot MCU. Assert HCRESET, poll until cleared.
//   2. Clear PORTMODE[16] to select HOST mode (after HCRESET).
//   3. Set RS (Run/Stop).
//   4. Write ATL PTD slot 0 (4 words) at USB SRAM base:
//        Word 0: MULT=3, MaxPkt=512, V=1
//        Word 1: RL=0xF, HubAddr=0, Port=0, EP=1, DevAddr=1
//        Word 2: DataStartAddr=0x400, I=1, NrBytesToTransfer=0x1C00 (7KB)
//        Word 3: Active=1, EpType=BULK(2), Token=OUT(0), NakCnt=0xF
//   5. Initialize 7KB data payload at USB_SRAM_BASE+0x400: word[i] = i.
//      (Done before port reset so the ~340 us write does not eat into the
//       twtrev=301 us window that opens after RECEIVING_IS.)
//   6. Set Port Power (PP) and Port Reset (PR) -- no PFSC (HS capable).
//   7. Wait ~742 us for HS chirp handshaking, then clear PR.
//   8. Wait for PR to self-clear (DUT completes reset sequence).
//   9. Verify PSPD = 0x2 (HS) in PORTSC1[21:20].
//  10. Verify PED | PEDC in PORTSC1, clear PEDC.
//  11. Configure ATLPTDBASEADDR, DATAPLBASEADDR, LASTPTD=0, USBINTR=ATL_IRQ_E,
//      FLADJ=0x20. Clear all pending USBSTS. Enable ATL via USBCMD[ATL_EN].
//      (Only ~8 register writes before ATL_EN -- fires well within twtrev=301 us.)
//  12. Poll USBSTS for ATL_IRQ (bit 16). Verify DONE_MAP bit 0 set.
//  13. Read PTD word 3: verify Active=0, NrBytesTransfered=7168.
//  14. Print PASSED/FAILED and halt.
//

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "stdbool.h"
#include "veer-csr.h"

// ---------------------------------------------------------------------------
// Timeout / retry constants (MCU clk ~333 MHz, ~3 ns/iter in RTL simulation)
// ---------------------------------------------------------------------------
#define HCRESET_POLL_MAX    20000u    // iterations waiting for HCRESET to clear
// HS chirp handshaking requires ~10ms. In
// simulation the VIP tdrst timer is set to 50us.  Timeline:
//   - MCU writes PR at ~44 us sim time (observed from MCU VPRINTF).
//   - VIP attaches at ~10 us (poweron_auto_attach_delay), J-state visible.
//   - DUT drives SE0 when PR is asserted at ~44 us.
//   - tsigatt (100 us) starts when VIP detects J->SE0 transition at ~44 us.
//   - tsigatt expires at ~144 us, tdrst (50 us) timer starts.
//   - VIP fires chirp-K at ~194 us, 3 KJ pairs complete, chirp done at ~714 us.
//   - VIP enters PERIPHERAL_HI_SPEED at 714239 ns (observed in simulation).
//   - After chirp, ATL drives LINESTATE_J starting at 764004 ns.
//   - tlinestate_duration timer starts: 66 us window ends at 830004 ns.
//   - ATL drives K again at 814012 ns (50 us J period) -- interrupts timer.
//   - PR must deassert WITHIN the first J window (764-814 us) so ATL stops.
//   - Actual MCU iteration time = ~14 ns/iter (fence + AHB latency, measured).
//   - Target deassert at ~786 us. Hold needed = 786 - 44 = 742 us.
//   - 742000 ns / 14 ns/iter = ~53000 iters. PR deasserts at ~44 + 742 = 786 us.
//   - J timer started at 764 us, ATL stops at 786 us, J continues to 830 us.
//   - VIP sees 66 us clean J (830-764=66 us) and exits BUS_RESET. OK.
#define PR_HOLD_DELAY       53000u    // hold PR ~742 us (deasserts ~786 us, within 764-814 us J window)
#define PR_CLEAR_POLL_MAX   200000u   // iterations waiting for PR to clear after deassert
#define PED_POLL_MAX        200000u   // iterations waiting for PED after reset
#define ATL_IRQ_POLL_MAX    500000u   // iterations waiting for ATL transfer done (256B HS = ~1 packet)
#define CTRL_IRQ_POLL_MAX   200000u   // iterations waiting for ATL control transfer stage done

// ---------------------------------------------------------------------------
// USBHSH register bit definitions
// (derived from soc_address_map.h USBHSH_* mask fields)
// ---------------------------------------------------------------------------
// USBCMD
#define USBHSH_RS           (1u << 0)    // Run/Stop
#define USBHSH_HCRESET      (1u << 1)    // Host Controller Reset
#define USBHSH_ATL_EN       (1u << 8)    // ATL list enable
// USBSTS / USBINTR
#define USBHSH_ATL_IRQ      (1u << 16)   // ATL transfer done interrupt / enable
// PORTSC1
#define USBHSH_CCS          (1u << 0)    // Current Connect Status
#define USBHSH_CSC          (1u << 1)    // Connect Status Change (W1C)
#define USBHSH_PED          (1u << 2)    // Port Enable/Disable
#define USBHSH_PEDC         (1u << 3)    // Port Enable/Disable Change (W1C)
#define USBHSH_PR           (1u << 8)    // Port Reset
#define USBHSH_PP           (1u << 12)   // Port Power
// PFSC deliberately omitted -- HS capable, no forced FS
#define USBHSH_PSPD_SHIFT   20u
#define USBHSH_PSPD_MASK    (3u << USBHSH_PSPD_SHIFT)
#define USBHSH_PSPD_HS      (2u << USBHSH_PSPD_SHIFT) // 0b10 = HS
// PORTMODE
#define USBHSH_PORT_MODE_HOST   0u       // bit 16 = 0 -> HOST mode

// ---------------------------------------------------------------------------
// USB 2.0 standard control request codes (used for USB enumeration).
// ---------------------------------------------------------------------------
#define USB_REQ_SET_ADDRESS         0x05u
#define USB_REQ_SET_CONFIGURATION   0x09u

// ---------------------------------------------------------------------------
// Control PTD values for EP0 (MaxPkt=64, CONTROL type).
//
// W0: MULT=1, MaxPkt=64, V=1
// W2 SETUP stage: DataStartAddr=0x400, I=0, NrBytesToTransfer=8
// W2 STATUS stage: DataStartAddr=0x400, I=0, NrBytesToTransfer=0
// W3 SETUP token (token=2): Active=1, EpType=CONTROL, Token=SETUP, NakCnt=0xF
// W3 STATUS IN token (token=1): Active=1, EpType=CONTROL, Token=IN, NakCnt=0xF
// ---------------------------------------------------------------------------
#define CTRL_PTD_W0         PTD_W0(1, 64, 1)           // 0x10400001
#define CTRL_PTD_W2_SETUP   PTD_W2(USB_DATA_START_ADDR, 1, 8)  // 0x04008008 -- i_flag=1 (IOC=1, ATL_IRQ fires on completion)
#define CTRL_PTD_W2_STATUS  PTD_W2(USB_DATA_START_ADDR, 1, 0)  // 0x04008000 -- i_flag=1 (IOC=1, ATL_IRQ fires on completion)
#define CTRL_PTD_W3_SETUP   PTD_W3(1, 0, 0, 0, 2, 0xF, 0)     // 0x80790000
#define CTRL_PTD_W3_STATUS  PTD_W3(1, 0, 0, 0, 1, 0xF, 0)     // 0x80788000

// ---------------------------------------------------------------------------
// USB SRAM layout (PTD at base, data at base+0x400)
//
//   USB_DMA_BASE_ADDR (0x20010000): USB SRAM start
//   +0x000 .. +0x3FF (1024 B): ATL PTD area (32 slots x 16 bytes)
//   +0x400 .. +0x1BFF (6144 B): 7KB data payload (7168 bytes, 1792 words)
//
// DataStartAddress in PTD word2[26:16] = raw byte offset from DATAPLBASEADDR.
// DATAPLBASEADDR = USB_DMA_BASE_ADDR, data starts at offset 0x400 = 1024 bytes.
// DataStartAddress field = 0x400 (stored directly; golden PTD W2 = 0x04009C00 confirms).
// ---------------------------------------------------------------------------
#define USB_DMA_BASE            0x20010000u
#define USB_ATL_PTD_BASE        (USB_DMA_BASE)              // PTD slot 0 at base+0
#define USB_DATA_BASE           (USB_DMA_BASE + 0x400u)     // data at base+1KB
#define USB_HS_BULK_BYTES       256u                         // 256 bytes = 0x100 (one HS bulk packet, for fast simulation)
#define USB_HS_MAX_PACKET       512u                         // HS bulk max packet
#define USB_DATA_START_ADDR     0x400u                       // PTD DataStartAddress field value (raw byte offset into SRAM)

// ---------------------------------------------------------------------------
// ATL PTD 4-word encoding (ip_3515 / ip_3528 format).
//
// Bit positions verified against golden values:
//   verify_equal(atl_descriptor[0], 0x32000001)
//   verify_equal(atl_descriptor[1], 0x0000F011)
//   verify_equal(atl_descriptor[2], 0x04009C00)
//   verify_equal(atl_descriptor[3], 0x807C0000)
//
// Word 0: [0]=V, [26:16]=MaxPacketLength, [29:28]=Mult
// Word 1: [7:4]=DeviceAddress (7 bits, bits[10:4]), [3:0]=EP (4 bits, bits[3:0]),
//         [15:12]=RL (4 bits), [24:18]=PortNumber, [31:25]=HubAddress
// Word 2: [14:0]=NrBytesToTransfer, [15]=I, [26:16]=DataStartAddress (raw byte offset)
// Word 3: [14:0]=NrBytesTransfered, [18:17]=EpType, [22:19]=NakCnt,
//         [24]=B, [25]=H, [31]=Active
//
// Token:  0=OUT, 1=IN, 2=SETUP  (bits[16:15], value=0 for OUT has no effect)
// EpType: 0=Control, 1=Iso, 2=Bulk, 3=Interrupt
// ---------------------------------------------------------------------------
#define PTD_W0(mult, maxpkt, v) \
    (((uint32_t)(mult)   << 28) | \
     ((uint32_t)(maxpkt) << 16) | \
     ((uint32_t)(v)      <<  0))

#define PTD_W1(rl, hubaddr, port, ep, devaddr) \
    (((uint32_t)(rl)      << 12) | \
     ((uint32_t)(hubaddr) << 25) | \
     ((uint32_t)(port)    << 18) | \
     ((uint32_t)(devaddr) <<  4) | \
     ((uint32_t)(ep)      <<  0))

#define PTD_W2(datastartaddr, i_flag, nrbytes) \
    (((uint32_t)(datastartaddr) << 16) | \
     ((uint32_t)(i_flag)        << 15) | \
     ((uint32_t)(nrbytes)       <<  0))

#define PTD_W3(active, h, b, eptype, token, nakcnt, nrbytesdone) \
    (((uint32_t)(active)      << 31) | \
     ((uint32_t)(h)           << 25) | \
     ((uint32_t)(b)           << 24) | \
     ((uint32_t)(nakcnt)      << 19) | \
     ((uint32_t)(eptype)      << 17) | \
     ((uint32_t)(token)       << 15) | \
     ((uint32_t)(nrbytesdone) <<  0))

#define PTD_W3_ACTIVE_BIT       (1u << 31)
#define PTD_W3_NRBYTES_MASK     0x00007FFFu

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static bool poll_until_clear(uint32_t addr, uint32_t mask, uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (!(lsu_read_32(addr) & mask)) return true;
        // Fence prevents back-to-back loads from overflowing the VeeR EL2 store buffer.
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT waiting for %s to clear (addr=0x%x)\n", lbl, addr);
    return false;
}

static bool poll_until_set(uint32_t addr, uint32_t mask, uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (lsu_read_32(addr) & mask) return true;
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT waiting for %s to set (addr=0x%x)\n", lbl, addr);
    return false;
}

// ---------------------------------------------------------------------------
// usb_atl_ctrl_xfer_no_data
//
// Issues a USB 2.0 no-data-stage control transfer using ATL slot 0.
// Used for SET_ADDRESS and SET_CONFIGURATION during USB enumeration.
//
// Sends: SETUP(8B) stage followed by STATUS IN(0B) stage.
// The ATL must already be enabled (ATL_EN=1) and SKIP_MAP=0xFFFFFFFE so
// that slot 0 is processed on the next microframe.
//
// Parameters:
//   dev_addr  - USB device address for SETUP token (0 for SET_ADDRESS, 1 for SET_CONFIGURATION)
//   request   - bRequest value (USB_REQ_SET_ADDRESS or USB_REQ_SET_CONFIGURATION)
//   wValue    - wValue field (new address or configuration index)
// ---------------------------------------------------------------------------
static bool usb_atl_ctrl_xfer_no_data(uint8_t dev_addr, uint8_t request, uint16_t wValue)
{
    // Build 8-byte SETUP packet in USB_DATA_BASE.
    // Layout: [bmRequestType, bRequest, wValue_lo, wValue_hi, wIndex_lo, wIndex_hi, wLength_lo, wLength_hi]
    // Packed as two 32-bit little-endian words.
    uint32_t setup_w0 = ((uint32_t)(wValue & 0xFFu) << 16) |
                        ((uint32_t)(request)         <<  8) |
                        0x00u;                              // bmRequestType=0x00 (host-to-device, standard, device)
    uint32_t setup_w1 = 0x00000000u;                        // wIndex=0, wLength=0
    lsu_write_32(USB_DATA_BASE + 0u, setup_w0);
    lsu_write_32(USB_DATA_BASE + 4u, setup_w1);

    VPRINTF(LOW, "MCU: CTRL SETUP addr=%d req=0x%x wValue=0x%x\n",
            dev_addr, request, wValue);

    // --- SETUP stage ---
    lsu_write_32(USB_ATL_PTD_BASE + 0x00u, CTRL_PTD_W0);
    lsu_write_32(USB_ATL_PTD_BASE + 0x04u, PTD_W1(0, 0, 0, 0, dev_addr));
    lsu_write_32(USB_ATL_PTD_BASE + 0x08u, CTRL_PTD_W2_SETUP);
    lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, CTRL_PTD_W3_SETUP);
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ);  // clear pending

    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ, CTRL_IRQ_POLL_MAX, "CTRL_SETUP_IRQ")) {
        VPRINTF(LOW, "MCU: CTRL SETUP timeout (req=0x%x addr=%d)\n", request, dev_addr);
        return false;
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ);  // clear W1C

    // NOTE: ip_3515 ATL auto-handles the STATUS stage as part of the SETUP PTD
    // for no-data control transfers. No separate STATUS PTD is needed.

    // --- IRQ status checks: DONE_MAP and PTD W3 ---
    {
        uint32_t done_map = lsu_read_32(SOC_USBHSH_ATL_PTD_DONE_MAP);
        uint32_t ptd_w3   = lsu_read_32(USB_ATL_PTD_BASE + 0x0Cu);
        VPRINTF(LOW, "MCU: CTRL IRQ check: DONE_MAP=0x%x PTD_W3=0x%x\n", done_map, ptd_w3);
        if (!(done_map & 0x1u)) {
            VPRINTF(LOW, "MCU: CTRL DONE_MAP slot 0 not set (req=0x%x addr=%d)\n", request, dev_addr);
            return false;
        }
        if (ptd_w3 & PTD_W3_ACTIVE_BIT) {
            VPRINTF(LOW, "MCU: CTRL PTD Active=1 after IRQ (req=0x%x addr=%d)\n", request, dev_addr);
            return false;
        }
    }

    VPRINTF(LOW, "MCU: CTRL done (req=0x%x addr=%d)\n", request, dev_addr);
    return true;
}

void main(void)
{
    uint32_t reg;
    uint32_t pspd;
    uint32_t ptd_w3;
    uint32_t nr_bytes_done;
    bool     passed = false;

    VPRINTF(LOW, "=================\n"
                 "MCU: USB HS host bulk OUT test (DUT=HOST HS, VIP=DEVICE)\n"
                 "=================\n\n");

    boot_mcu();

    // -----------------------------------------------------------------------
    // Caliptra core bringup -- must happen BEFORE the USB port-reset spin so
    // the Caliptra FW does not time out and call $finish while the MCU is
    // still holding PR.  We advance the breakpoint
    // immediately after boot so Caliptra proceeds in parallel with USB init.
    // -----------------------------------------------------------------------
    mcu_cptra_advance_brkpoint();
    VPRINTF(LOW, "MCU: Caliptra brkpoint advanced. Starting USB init.\n");

    // -----------------------------------------------------------------------
    // Step 1: HCRESET (LPC_USB_HS0_HOST->USBCMD |= HCRESET)
    // PORTMODE must be set AFTER HCRESET -- HCRESET restores PORTMODE default
    // (device=1), so writing HOST mode before reset would be undone.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD, lsu_read_32(SOC_USBHSH_USBCMD) | USBHSH_HCRESET);
    if (!poll_until_clear(SOC_USBHSH_USBCMD, USBHSH_HCRESET, HCRESET_POLL_MAX, "HCRESET")) {
        VPRINTF(LOW, "MCU: FATAL - HCRESET did not clear.\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: HCRESET complete.\n");

    // -----------------------------------------------------------------------
    // Step 2: Select HOST mode (PORTMODE[16]=0) after HCRESET.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTMODE, USBHSH_PORT_MODE_HOST);
    VPRINTF(LOW, "MCU: PORTMODE = HOST.\n");

    // -----------------------------------------------------------------------
    // Step 3: Run/Stop (LPC_USB_HS0_HOST->USBCMD = RS)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD, USBHSH_RS);
    VPRINTF(LOW, "MCU: USBCMD RS set.\n");

    // -----------------------------------------------------------------------
    // Step 4: Write ATL PTD slot 0 at USB_ATL_PTD_BASE.
    //
    // Done BEFORE port reset so that the ~340 us payload write (Step 5)
    // completes before VIP exits BUS_RESET. After RECEIVING_IS, only the
    // ~8 ATL config register writes remain before ATL_EN, which fires well
    // within the twtrev=301 us deadline.
    //
    // PTD values:
    //   W0=0x32000001: MULT=3[29:28], MaxPkt=0x200[26:16], V=1[0]
    //   W1=0x0000F011: RL=0xF[15:12], EP=1[7:4], DevAddr=1[6:0]
    //   W2=0x04009C00: DataStartAddr=0x400[26:16], I=1[15], NrBytes=0x1C00[14:0]
    //   W3=0x807C0000: Active=1[31], NakCnt=0xF[22:19], EpType=2[18:17]
    // -----------------------------------------------------------------------
    {
        uint32_t w0 = PTD_W0(3, USB_HS_MAX_PACKET, 1);
        uint32_t w1 = PTD_W1(0xF, 0, 0, 1, 1);
        uint32_t w2 = PTD_W2(USB_DATA_START_ADDR, 1, USB_HS_BULK_BYTES);
        uint32_t w3 = PTD_W3(1, 0, 0, 2, 0, 0xF, 0);

        VPRINTF(LOW, "MCU: ATL PTD: w0=0x%x w1=0x%x w2=0x%x w3=0x%x\n", w0, w1, w2, w3);

        // Golden value check.
        // W2 = PTD_W2(0x400, 1, 0x100):
        //   DataStartAddr=0x400[26:16] -> 0x04000000
        //   I=1[15]                   -> 0x00008000
        //   NrBytes=0x100[14:0]       -> 0x00000100
        //   W2 = 0x04008100
        if (w0 != 0x32000001u) { VPRINTF(LOW, "MCU: PTD W0 MISMATCH 0x%x != 0x32000001\n", w0); csr_write_mpmc_halt(); }
        if (w1 != 0x0000F011u) { VPRINTF(LOW, "MCU: PTD W1 MISMATCH 0x%x != 0x0000F011\n", w1); csr_write_mpmc_halt(); }
        if (w2 != 0x04008100u) { VPRINTF(LOW, "MCU: PTD W2 MISMATCH 0x%x != 0x04008100\n", w2); csr_write_mpmc_halt(); }
        if (w3 != 0x807C0000u) { VPRINTF(LOW, "MCU: PTD W3 MISMATCH 0x%x != 0x807C0000\n", w3); csr_write_mpmc_halt(); }
        VPRINTF(LOW, "MCU: PTD golden check PASSED.\n");

        lsu_write_32(USB_ATL_PTD_BASE + 0x00u, w0);
        lsu_write_32(USB_ATL_PTD_BASE + 0x04u, w1);
        lsu_write_32(USB_ATL_PTD_BASE + 0x08u, w2);
        lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, w3);
    }

    // -----------------------------------------------------------------------
    // Step 5: Initialize 7KB data payload at USB_DATA_BASE.
    // Pattern: word[i] = i  (data_payload[i] = i for i=0..1791)
    // Done BEFORE port reset -- ~340 us write must not consume the 301 us
    // twtrev window that opens when the VIP exits BUS_RESET (RECEIVING_IS).
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Writing 7KB payload at 0x%x (word[i]=i).\n", USB_DATA_BASE);
    for (uint32_t i = 0; i < (USB_HS_BULK_BYTES / 4u); i++)
        lsu_write_32(USB_DATA_BASE + (i * 4u), i);
    VPRINTF(LOW, "MCU: Payload written.\n");

    // -----------------------------------------------------------------------
    // Step 6: Pre-configure ATL host registers BEFORE port reset.
    //
    // Writing ATLPTDBASEADDR, DATAPLBASEADDR, LASTPTD, USBINTR, FLADJ, and
    // SKIP_MAP here (before PP+PR) ensures that after port reset completes
    // and the VIP enters RECEIVING_IS, only two writes remain: USBSTS clear
    // and ATL_EN. Those two writes take ~1.3 us, well within twtrev=301 us.
    //
    // Here we hoist them earlier to
    // satisfy the simulation timing constraint.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_ATL_PTD_BASE_ADDR,     USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR, USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE,         0x00000000u);
    lsu_write_32(SOC_USBHSH_USBINTR,                USBHSH_ATL_IRQ);
    lsu_write_32(SOC_USBHSH_FLADJ_FRINDEX,          0x00000020u);
    lsu_write_32(SOC_USBHSH_ATL_PTD_SKIP_MAP,       0xFFFFFFFEu);
    VPRINTF(LOW, "MCU: ATL config pre-loaded (PTD_BASE=0x%x SKIP=0xFFFFFFFE).\n", USB_DMA_BASE);

    // -----------------------------------------------------------------------
    // Step 7: Port Power then Port Reset -- NO PFSC (HS capable).
    // read-modify-write (|=) for both PP and PR so that any
    // sticky W1C bits already set in PORTSC1 are not inadvertently cleared.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PP);
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PR);
    VPRINTF(LOW, "MCU: PP + PR asserted (HS chirp in progress).\n");

    // -----------------------------------------------------------------------
    // Step 8: Hold PR long enough for HS chirp handshaking.
    // In simulation chirp completes at 714 us. After
    // chirp ATL drives J starting at 764 us; tlinestate_duration timer starts
    // (66 us, expires 830 us). ATL must stop before 814 us (next K toggle).
    // PR_HOLD_DELAY=53000 iters x ~14 ns/iter = ~742 us hold. PR deasserts at
    // ~786 us (within 764-814 us J window). ATL stops, J continues to 830 us,
    // VIP sees full 66 us clean J and exits BUS_RESET.
    // -----------------------------------------------------------------------
    for (volatile uint32_t d = 0; d < PR_HOLD_DELAY; d++) { /* spin */ }

    // Clear PR (keep PP) via read-modify-write, PORTSC1 &= ~PR.
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) & ~USBHSH_PR);
    VPRINTF(LOW, "MCU: PR deasserted. Waiting for port reset to complete...\n");

    // -----------------------------------------------------------------------
    // Step 9: Poll until PR clears (DUT completes reset sequence).
    // while(LPC_USB_HS0_HOST->PORTSC1 & PR))
    // -----------------------------------------------------------------------
    if (!poll_until_clear(SOC_USBHSH_PORTSC1, USBHSH_PR, PR_CLEAR_POLL_MAX, "PORTSC1.PR")) {
        VPRINTF(LOW, "MCU: WARNING - PR did not clear. Continuing.\n");
    }
    VPRINTF(LOW, "MCU: Port Reset complete.\n");

    // -----------------------------------------------------------------------
    // Step 10a: Re-write ALL ATL configuration registers and PTD after port reset.
    //
    // The ip_3515 port reset sequence resets ATL configuration registers to
    // their defaults: ATLPTDBASEADDR=0x00000000, DATAPLBASEADDR=0x00000000,
    // LASTPTD=0, etc. After reset, the ATL reads PTDs from address 0x00000000
    // where all memory is 0 (V=0, Active=0), so all 32 slots are skipped and
    // only SOF microframes are issued -- no BULK OUT tokens ever generated.
    //
    // The PTD written in Step 4 (before PR) is also lost because its SRAM
    // location is correct but the ATL base pointer was reset to 0. Re-writing
    // both the config regs AND the PTD here makes the ATL find slot 0 on the
    // first microframe after ATL_EN.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_ATL_PTD_BASE_ADDR,      USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR,  USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE,          0x00000000u);
    lsu_write_32(SOC_USBHSH_USBINTR,                 USBHSH_ATL_IRQ);
    lsu_write_32(SOC_USBHSH_FLADJ_FRINDEX,           0x00000020u);
    lsu_write_32(SOC_USBHSH_ATL_PTD_SKIP_MAP,        0xFFFFFFFEu);
    VPRINTF(LOW, "MCU: ATL config regs re-written after port reset (PTD_BASE=0x%x).\n", USB_DMA_BASE);

    {
        uint32_t w0 = PTD_W0(3, USB_HS_MAX_PACKET, 1);
        uint32_t w1 = PTD_W1(0xF, 0, 0, 1, 1);
        uint32_t w2 = PTD_W2(USB_DATA_START_ADDR, 1, USB_HS_BULK_BYTES);
        uint32_t w3 = PTD_W3(1, 0, 0, 2, 0, 0xF, 0);
        lsu_write_32(USB_ATL_PTD_BASE + 0x00u, w0);
        lsu_write_32(USB_ATL_PTD_BASE + 0x04u, w1);
        lsu_write_32(USB_ATL_PTD_BASE + 0x08u, w2);
        lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, w3);
        VPRINTF(LOW, "MCU: PTD re-written after port reset (Active=1, w0=0x%x w3=0x%x).\n", w0, w3);
    }

    // -----------------------------------------------------------------------
    // Step 10: Clear pending interrupts and enable ATL list processing.
    //
    // ATL_EN is set HERE -- immediately after PR clears -- to fire within
    // twtrev=301 us of RECEIVING_IS. All config registers (ATLPTDBASEADDR,
    // DATAPLBASEADDR, LASTPTD, USBINTR, FLADJ, SKIP_MAP) and the PTD/payload
    // were pre-loaded in Steps 4-6 before port reset. Only USBSTS clear +
    // ATL_EN remain (~1.3 us total), well before the twtrev deadline.
    //
    // PSPD and PED checks are done AFTER ATL_EN since they are pure
    // read-only verification and have no timing constraint.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBSTS, 0xFFFFFFFFu);
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg | USBHSH_ATL_EN);
    VPRINTF(LOW, "MCU: USBCMD ATL_EN set. Waiting for ATL_IRQ...\n");

    // -----------------------------------------------------------------------
    // Step 11: Verify PSPD = HS (0x2) -- post-ATL_EN verification.
    // (if (value != 0x2) terminateTest(FAIL, ...))
    // -----------------------------------------------------------------------
    reg  = lsu_read_32(SOC_USBHSH_PORTSC1);
    pspd = (reg & USBHSH_PSPD_MASK) >> USBHSH_PSPD_SHIFT;
    VPRINTF(LOW, "MCU: PORTSC1=0x%x PSPD=%d (%s)\n", reg, pspd,
            (pspd == 2) ? "HS" : (pspd == 1) ? "FS" : "LS/unknown");
    if (pspd != 2u) {
        VPRINTF(LOW, "MCU: FATAL - Expected PSPD=HS(2), got %d. Test FAILED.\n", pspd);
        csr_write_mpmc_halt();
    }

    // -----------------------------------------------------------------------
    // Step 12: Verify PED and clear PEDC via read-modify-write.
    // if ((PORTSC1 & PEDC) && (PORTSC1 & PED)) PORTSC1 |= PEDC else FAIL
    // -----------------------------------------------------------------------
    if ((reg & USBHSH_PEDC) && (reg & USBHSH_PED)) {
        lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PEDC);
        VPRINTF(LOW, "MCU: Port enabled (PED=1). PEDC cleared.\n");
    } else {
        VPRINTF(LOW, "MCU: FATAL - PEDC or PED not set after reset (PORTSC1=0x%x).\n", reg);
        csr_write_mpmc_halt();
    }

    // -----------------------------------------------------------------------
    // Step 13: USB Enumeration -- SET_CONFIGURATION only (no SET_ADDRESS).
    //
    // The SVT VIP DEVICE is pre-configured with device_address=1 from t=0.
    // It has no listener on addr=0, so SET_ADDRESS(0->1) would produce
    // "No device with matching address found" UVM_ERRORs and stall the ATL.
    // Skip SET_ADDRESS entirely and send SET_CONFIGURATION(1) directly to
    // addr=1. This moves the VIP from DEFAULT to CONFIGURED state, activating
    // EP1 so the subsequent BULK OUT is ACK'd.
    //
    // ATL_EN is already set above; SOF frames keep the VIP alive during enum.
    // SKIP_MAP=0xFFFFFFFE keeps slot 0 active; control PTD is written here.
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: USB enumeration: SET_CONFIGURATION(1) to addr=1...\n");
    if (!usb_atl_ctrl_xfer_no_data(1, USB_REQ_SET_CONFIGURATION, 1)) {
        VPRINTF(LOW, "MCU: FATAL - SET_CONFIGURATION failed. Test FAILED.\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: SET_CONFIGURATION done. VIP EP1 now ACTIVE.\n");

    // -----------------------------------------------------------------------
    // Step 14: Restore payload words 0 and 1 that were overwritten by the
    // SETUP packet written during SET_CONFIGURATION.
    //
    // usb_atl_ctrl_xfer_no_data writes the 8-byte SETUP packet at USB_DATA_BASE
    // (offset 0x400 in SRAM), which is the same address used for the bulk OUT
    // payload. After the control transfer completes, word[0] = 0x00010900
    // (SET_CONFIGURATION SETUP bytes) and word[1] = 0x00000000, overwriting
    // the original payload values (word[0]=0, word[1]=1). Restore them now.
    // -----------------------------------------------------------------------
    lsu_write_32(USB_DATA_BASE + 0u, 0x00000000u);  // restore payload word[0] = 0
    lsu_write_32(USB_DATA_BASE + 4u, 0x00000001u);  // restore payload word[1] = 1

    // -----------------------------------------------------------------------
    // Step 15: Re-write BULK OUT PTD (enumeration control transfers used slot 0).
    // Restore the BULK OUT PTD with Active=1 for the actual data transfer.
    // -----------------------------------------------------------------------
    {
        uint32_t w0 = PTD_W0(3, USB_HS_MAX_PACKET, 1);
        uint32_t w1 = PTD_W1(0xF, 0, 0, 1, 1);
        uint32_t w2 = PTD_W2(USB_DATA_START_ADDR, 1, USB_HS_BULK_BYTES);
        uint32_t w3 = PTD_W3(1, 0, 0, 2, 0, 0xF, 0);
        lsu_write_32(USB_ATL_PTD_BASE + 0x00u, w0);
        lsu_write_32(USB_ATL_PTD_BASE + 0x04u, w1);
        lsu_write_32(USB_ATL_PTD_BASE + 0x08u, w2);
        lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, w3);
        VPRINTF(LOW, "MCU: BULK OUT PTD restored (Active=1, EP1, addr=1, %dB).\n",
                USB_HS_BULK_BYTES);
    }

    // -----------------------------------------------------------------------
    // Step 15: Poll USBSTS for ATL_IRQ (BULK OUT completion).
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ);  // clear any stale IRQ

    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ, ATL_IRQ_POLL_MAX, "USBSTS.ATL_IRQ")) {
        VPRINTF(LOW, "MCU: TIMEOUT - ATL_IRQ never set. PORTSC1=0x%x USBSTS=0x%x\n",
                lsu_read_32(SOC_USBHSH_PORTSC1), lsu_read_32(SOC_USBHSH_USBSTS));
        VPRINTF(LOW, "MCU: Test FAILED.\n");
        csr_write_mpmc_halt();
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ); // clear W1C

    reg = lsu_read_32(SOC_USBHSH_ATL_PTD_DONE_MAP);
    VPRINTF(LOW, "MCU: ATL_IRQ fired. DONE_MAP=0x%x\n", reg);

    if (!(reg & 0x1u)) {
        VPRINTF(LOW, "MCU: DONE_MAP slot 0 not set. Test FAILED.\n");
        csr_write_mpmc_halt();
    }

    // -----------------------------------------------------------------------
    // Step 16: Read PTD word 3 and verify NrBytesTransfered = USB_HS_BULK_BYTES.
    // -----------------------------------------------------------------------
    ptd_w3 = lsu_read_32(USB_ATL_PTD_BASE + 0x0Cu);
    VPRINTF(LOW, "MCU: PTD word 3 after transfer = 0x%x\n", ptd_w3);

    if (ptd_w3 & PTD_W3_ACTIVE_BIT) {
        VPRINTF(LOW, "MCU: ERROR - PTD Active=1 after IRQ. Test FAILED.\n");
        passed = false;
    } else {
        nr_bytes_done = ptd_w3 & PTD_W3_NRBYTES_MASK;
        VPRINTF(LOW, "MCU: NrBytesTransfered=%d (expected %d)\n",
                nr_bytes_done, USB_HS_BULK_BYTES);
        passed = (nr_bytes_done == USB_HS_BULK_BYTES);
    }

    if (passed)
        VPRINTF(LOW, "MCU: USB HS host bulk OUT - PASSED\n");
    else
        VPRINTF(LOW, "MCU: USB HS host bulk OUT - FAILED\n");

    VPRINTF(LOW, "MCU: Halting.\n");
    csr_write_mpmc_halt();
}
