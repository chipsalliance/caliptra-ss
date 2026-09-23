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
// Description: USB HS host isochronous OUT test firmware for the Caliptra SS.
//
// DUT role: USB HOST (ip_3515 ISO periodic list, SOC_USBHSH_* registers).
// VIP role: USB DEVICE (SVT VIP EP1 ISO OUT, receives 1024B from DUT).
//
// ISO periodic PTD layout (8 DWORDs, from NXP Integration Guide sec 4.1.3.3):
//
//   DW0 (0x00): [31:30]=R [29:28]=Mult[1:0] [27]=R [26:16]=MaxPacketLength[10:0]
//               [15:8]=uFrame[7:0] [7]=J [6]=R [5:1]=NextPTDPointer[4:0] [0]=V
//   DW1 (0x04): [31:18]=R [17:16]=SE[1:0] [15:12]=RL[3:0] [11]=S
//               [10:4]=DeviceAddress[6:0] [3:0]=EP[3:0]
//   DW2 (0x08): [31:16]=DataStartAddress[15:0] [15]=I [14:0]=NrBytesToTransfer[14:0]
//   DW3 (0x0C): [31]=A [30]=H [29]=B [28]=X [27]=R [26]=P [25]=DT
//               [24:23]=Cerr[1:0] [22:19]=NakCnt[3:0] [18:17]=EPType[1:0]
//               [16:15]=Token[1:0] [14:0]=NrBytesTransferred[14:0]
//   DW4 (0x10): [31:29]=Status7 [28:26]=Status6 [25:23]=Status5 [22:20]=Status4
//               [19:17]=Status3 [16:14]=Status2 [13:11]=Status1 [10:8]=Status0
//               [7:0]=uSA[7:0]
//   DW5 (0x14): [31:24]=ISO_IN_2[7:0] [23:12]=ISO_IN_1[11:0] [11:0]=ISO_IN_0[11:0]
//   DW6 (0x18): [31:28]=ISO_IN_5[3:0] [27:16]=ISO_IN_4[11:0]
//               [15:4]=ISO_IN_3[11:0] [3:0]=ISO_IN_2[11:8]
//   DW7 (0x1C): [31:20]=ISO_IN_7[11:0] [19:8]=ISO_IN_6[11:0] [7:0]=ISO_IN_5[7:0]
//
// Test flow:
//   1.  Boot MCU, HCRESET, set HOST mode, RS.
//   2.  Write ISO PTD slot 0 at USB SRAM base (0x20010000).
//   3.  Initialize 1024-byte payload at USB_DATA_BASE (SRAM+0x400): word[i]=i.
//   4.  SET_CONFIGURATION(1) to addr=1 via ATL CTRL PTD (enumerate VIP EP1).
//   5.  Re-configure ISO list registers (ISO_PTD_BASE, ISO_SKIP, LAST_PTD).
//   6.  Enable ISO list (USBCMD ISO_EN, USBINTR ISO_IRQ).
//   7.  Poll USBSTS ISO_IRQ. Verify ISO_PTD_DONE_MAP bit 0 set.
//   8.  Read DW3 NrBytesTransferred = 1024. Print PASSED.

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
// Timeout constants
// ---------------------------------------------------------------------------
#define HCRESET_POLL_MAX      20000u
#define PR_HOLD_DELAY         53000u
#define PR_CLEAR_POLL_MAX     200000u
#define PED_POLL_MAX          200000u
#define ISO_IRQ_POLL_MAX      500000u
#define CTRL_IRQ_POLL_MAX     200000u

// ---------------------------------------------------------------------------
// USBHSH register bit fields
// ---------------------------------------------------------------------------
#define USBHSH_RS             (1u << 0)
#define USBHSH_HCRESET        (1u << 1)
#define USBHSH_ATL_EN         (1u << 8)
#define USBHSH_ISO_EN         (1u << 9)
#define USBHSH_ATL_IRQ        (1u << 16)
#define USBHSH_ISO_IRQ        (1u << 17)
#define USBHSH_PP             (1u << 12)
#define USBHSH_PR             (1u << 8)
#define USBHSH_PED            (1u << 2)
#define USBHSH_PEDC           (1u << 3)
#define USBHSH_PSPD_SHIFT     20u
#define USBHSH_PSPD_MASK      (3u << USBHSH_PSPD_SHIFT)
#define USBHSH_PORT_MODE_HOST 0u

// USB standard request codes
#define USB_REQ_SET_CONFIGURATION  0x09u

// ---------------------------------------------------------------------------
// USB SRAM layout
//   0x20010000 + 0x000: ISO PTD slot 0 OUT (32 bytes, 0x000-0x01F)
//   0x20010000 + 0x020: ISO PTD slot 1 IN  (32 bytes, 0x020-0x03F)
//   0x20010000 + 0x400: ISO OUT payload    (1024 bytes, word[i]=i)
//   0x20010000 + 0x800: ISO IN  rx buffer  (1024 bytes, written by controller)
//
//   ATL PTD area also at 0x20010000 but only used transiently for enumeration.
//   ISO PTD slot 0 occupies bytes 0x000-0x01F (32 bytes). ATL slot 0 is
//   bytes 0x000-0x00F (16 bytes). They overlap in slot 0 but enumeration
//   (ATL) finishes before ISO starts, so this is safe.
// ---------------------------------------------------------------------------
#define USB_DMA_BASE           0x20010000u
#define USB_ISO_PTD_BASE       (USB_DMA_BASE)
#define USB_ATL_PTD_BASE       (USB_DMA_BASE)
#define USB_DATA_BASE          (USB_DMA_BASE + 0x400u)
#define USB_DATA_START_ADDR    0x400u
#define USB_IN_DATA_BASE       (USB_DMA_BASE + 0x800u)
#define USB_IN_DATA_START_ADDR 0x800u
#define USB_HS_ISO_BYTES       1024u
#define USB_HS_ISO_MAXPKT      1024u
#define USB_ATL_MAXPKT         512u

// ---------------------------------------------------------------------------
// ISO PTD DW macros (periodic list, regular HS transactions)
//
// DW0: [29:28]=Mult, [26:16]=MaxPacketLength, [15:8]=uFrame, [0]=V
// DW1: [17:16]=SE, [15:12]=RL, [11]=S, [10:4]=DevAddr, [3:0]=EP
// DW2: [31:16]=DataStartAddr, [15]=I, [14:0]=NrBytesToTransfer
// DW3: [31]=A, [24:23]=Cerr, [22:19]=NakCnt, [18:17]=EPType, [16:15]=Token,
//      [14:0]=NrBytesTransferred
// DW4: [7:0]=uSA
// ---------------------------------------------------------------------------
#define ISO_PTD_DW0(mult, maxpkt, uframe, v) \
    (((uint32_t)(mult)   << 28) | \
     ((uint32_t)(maxpkt) << 16) | \
     ((uint32_t)(uframe) <<  8) | \
     ((uint32_t)(v)      <<  0))

#define ISO_PTD_DW1(se, rl, s, devaddr, ep) \
    (((uint32_t)(se)      << 16) | \
     ((uint32_t)(rl)      << 12) | \
     ((uint32_t)(s)       << 11) | \
     ((uint32_t)(devaddr) <<  4) | \
     ((uint32_t)(ep)      <<  0))

#define ISO_PTD_DW2(datastartaddr, i_flag, nrbytes) \
    (((uint32_t)(datastartaddr) << 16) | \
     ((uint32_t)(i_flag)        << 15) | \
     ((uint32_t)(nrbytes)       <<  0))

// EPType: 00=Control, 01=ISO, 10=Bulk, 11=Interrupt
// Token:  00=OUT, 01=IN, 10=SETUP
#define ISO_PTD_DW3(active, cerr, nakcnt, eptype, token, nrbytesdone) \
    (((uint32_t)(active)     << 31) | \
     ((uint32_t)(cerr)       << 23) | \
     ((uint32_t)(nakcnt)     << 19) | \
     ((uint32_t)(eptype)     << 17) | \
     ((uint32_t)(token)      << 15) | \
     ((uint32_t)(nrbytesdone)<<  0))

#define ISO_PTD_DW4(usa) \
    ((uint32_t)(usa))

#define ISO_PTD_DW3_ACTIVE_BIT    (1u << 31)
#define ISO_PTD_DW3_HALT_BIT      (1u << 30)   // H: halted (error)
#define ISO_PTD_DW3_BABBLE_BIT    (1u << 29)   // B: babble detected
#define ISO_PTD_DW3_XERR_BIT      (1u << 28)   // X: transaction error
#define ISO_PTD_DW3_NRBYTES_MASK  0x00007FFFu

// DW4 per-uSOF status for regular HS ISO (non-split, section 4.1.3.3):
// Layout: [7:0]=uSA, [10:8]=Status0, [13:11]=Status1, [16:14]=Status2,
//         [19:17]=Status3, [22:20]=Status4, [25:23]=Status5,
//         [28:26]=Status6, [31:29]=Status7.
// For regular HS (non-split) ISO transfers: 000=OK/no-error, 010+=error.
// The 001=success encoding is used only for split transactions (sec 4.1.3.4).
// So we only check that no status field is >= 010 (error).
#define ISO_PTD_DW4_USA_MASK        0x000000FFu
#define ISO_PTD_DW4_STATUS_SHIFT(n) (8u + (uint32_t)(n)*3u)
#define ISO_PTD_DW4_STATUS_MASK     0x7u
#define ISO_PTD_DW4_STATUS_ERROR    0x2u   // any value >= 2 is an error

// DW5 ISO_IN byte count fields (per-uSOF received byte counts for ISO IN):
// [11:0]=ISO_IN_0, [23:12]=ISO_IN_1, [31:24]=ISO_IN_2[7:0] (partial).
// Full ISO_IN_2 = DW5[31:24] | DW6[3:0]<<8.
// DW6: [15:4]=ISO_IN_3[11:0], [27:16]=ISO_IN_4[11:0], [31:28]=ISO_IN_5[3:0].
// DW7: [7:0]=ISO_IN_5[11:4], [19:8]=ISO_IN_6[11:0], [31:20]=ISO_IN_7[11:0].

// ---------------------------------------------------------------------------
// ATL PTD macros (reused for CTRL enumeration, same as bulk out test)
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

#define PTD_W3_ACTIVE_BIT     (1u << 31)
#define CTRL_PTD_W0           PTD_W0(1, 64, 1)
#define CTRL_PTD_W2_SETUP     PTD_W2(USB_DATA_START_ADDR, 1, 8)
#define CTRL_PTD_W3_SETUP     PTD_W3(1, 0, 0, 0, 2, 0xF, 0)

// Forward declarations of poll helpers (defined later in this file).
static bool poll_until_clear(uint32_t addr, uint32_t mask,
                              uint32_t max_iter, const char *lbl);
static bool poll_until_set(uint32_t addr, uint32_t mask,
                            uint32_t max_iter, const char *lbl);

// ---------------------------------------------------------------------------
// iso_out_run -- perform one ISO OUT transfer on slot 0.
//
// Writes the active ISO OUT PTD (slot 0), configures ISO list registers,
// enables ISO_EN, polls ISO_IRQ, then checks DW3 completion status.
// Disables ISO_EN before returning so the caller can safely re-arm.
//
// Parameters:
//   iter  -- iteration number (1-based) used only in log messages.
//
// Returns true on success, false on any error.
// ---------------------------------------------------------------------------
static bool iso_out_run(uint32_t iter)
{
    uint32_t reg;
    uint32_t dw3;
    uint32_t nr_bytes_done;

    // Write active ISO OUT PTD into slot 0 (offset 0x000, 32 bytes).
    // Token=00 (OUT), EPType=01 (ISO), Active=1, V=1.
    {
        uint32_t dw0 = ISO_PTD_DW0(1, USB_HS_ISO_MAXPKT, 0x00, 1);  // V=1
        uint32_t dw1 = ISO_PTD_DW1(0, 0, 0, 1, 1);                  // DevAddr=1, EP=1
        uint32_t dw2 = ISO_PTD_DW2(USB_DATA_START_ADDR, 1, USB_HS_ISO_BYTES);
        uint32_t dw3_act = ISO_PTD_DW3(1, 0, 0, 1, 0, 0);           // A=1, ISO, OUT
        uint32_t dw4 = ISO_PTD_DW4(0xFF);

        VPRINTF(LOW,
            "MCU: ISO OUT iter%d PTD: dw0=0x%x dw1=0x%x dw2=0x%x dw3=0x%x dw4=0x%x\n",
            iter, dw0, dw1, dw2, dw3_act, dw4);

        lsu_write_32(USB_ISO_PTD_BASE + 0x00u, dw0);
        lsu_write_32(USB_ISO_PTD_BASE + 0x04u, dw1);
        lsu_write_32(USB_ISO_PTD_BASE + 0x08u, dw2);
        lsu_write_32(USB_ISO_PTD_BASE + 0x0Cu, dw3_act);
        lsu_write_32(USB_ISO_PTD_BASE + 0x10u, dw4);
        lsu_write_32(USB_ISO_PTD_BASE + 0x14u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x18u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x1Cu, 0u);
    }

    // Configure ISO list registers for slot 0 only.
    lsu_write_32(SOC_USBHSH_ISO_PTD_BASE_ADDR,
                 (USB_DMA_BASE & 0xFFFFFC00u) | (0u << 5));
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR, USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE, 0x00000000u);  // ISO_LAST=0
    lsu_write_32(SOC_USBHSH_ISO_PTD_SKIP_MAP, 0xFFFFFFFEu); // skip all except slot 0
    lsu_write_32(SOC_USBHSH_USBINTR, USBHSH_ISO_IRQ);

    VPRINTF(LOW, "MCU: ISO OUT iter%d config: SKIP=0xFFFFFFFE LAST_PTD=0x%x\n",
            iter, lsu_read_32(SOC_USBHSH_LAST_PTD_INUSE));

    // Clear stale IRQ then enable ISO list.
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ);
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg | USBHSH_ISO_EN);
    VPRINTF(LOW, "MCU: ISO OUT iter%d: ISO_EN set. Waiting for ISO_IRQ...\n", iter);

    // Poll ISO_IRQ.
    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ,
                        ISO_IRQ_POLL_MAX, "USBSTS.ISO_IRQ(OUT)")) {
        VPRINTF(LOW, "MCU: TIMEOUT - ISO_IRQ(OUT) iter%d. USBSTS=0x%x\n",
                iter, lsu_read_32(SOC_USBHSH_USBSTS));
        return false;
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ);

    reg = lsu_read_32(SOC_USBHSH_ISO_PTD_DONE_MAP);
    VPRINTF(LOW, "MCU: ISO OUT iter%d IRQ fired. DONE_MAP=0x%x\n", iter, reg);

    if (!(reg & 0x1u)) {
        VPRINTF(LOW, "MCU: ERROR - ISO_DONE_MAP slot0 not set iter%d (map=0x%x).\n",
                iter, reg);
        return false;
    }

    // Check DW3: Active must be clear, NrBytesTransferred must equal 1024.
    dw3 = lsu_read_32(USB_ISO_PTD_BASE + 0x0Cu);
    VPRINTF(LOW, "MCU: ISO OUT iter%d DW3=0x%x\n", iter, dw3);

    if (dw3 & ISO_PTD_DW3_ACTIVE_BIT) {
        VPRINTF(LOW, "MCU: ERROR - ISO OUT iter%d DW3 Active=1 after IRQ.\n", iter);
        return false;
    }

    nr_bytes_done = dw3 & ISO_PTD_DW3_NRBYTES_MASK;
    VPRINTF(LOW, "MCU: ISO OUT iter%d NrBytesTransferred=%d (expected %d)\n",
            iter, nr_bytes_done, USB_HS_ISO_BYTES);
    if (nr_bytes_done != USB_HS_ISO_BYTES) {
        VPRINTF(LOW, "MCU: ERROR - ISO OUT iter%d byte count mismatch.\n", iter);
        return false;
    }

    // Disable ISO_EN so caller can re-arm or switch direction.
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg & ~USBHSH_ISO_EN);

    VPRINTF(LOW, "MCU: ISO OUT iter%d PASSED.\n", iter);
    return true;
}

// ---------------------------------------------------------------------------
// iso_in_run -- perform one ISO IN transfer on slot 1.
//
// Writes the active ISO IN PTD (slot 1), configures ISO list registers,
// enables ISO_EN, polls ISO_IRQ, then performs full DW3/DW4/DW5-DW7 checks.
// Disables ISO_EN before returning so the caller can safely re-arm.
//
// Parameters:
//   iter  -- iteration number (1-based) used only in log messages.
//
// Returns true on success, false on any error.
// ---------------------------------------------------------------------------
static bool iso_in_run(uint32_t iter)
{
    uint32_t reg;
    uint32_t dw3;
    uint32_t nr_bytes_done;
    uint32_t dw4_in, dw5_in, dw6_in, dw7_in;
    uint32_t usof_n;
    uint32_t status_n;
    bool     any_err    = false;
    uint32_t iso_in_sum = 0;

    // Write active ISO IN PTD into slot 1 (offset 0x020, 32 bytes).
    // Token=01 (IN), EPType=01 (ISO), Active=1, V=1, EP=2.
    {
        uint32_t dw0_in = ISO_PTD_DW0(1, USB_HS_ISO_MAXPKT, 0x00, 1);   // V=1
        uint32_t dw1_in = ISO_PTD_DW1(0, 0, 0, 1, 2);                   // DevAddr=1, EP=2
        uint32_t dw2_in = ISO_PTD_DW2(USB_IN_DATA_START_ADDR, 1, USB_HS_ISO_BYTES);
        uint32_t dw3_in = ISO_PTD_DW3(1, 0, 0, 1, 1, 0);                // A=1, ISO, IN
        uint32_t dw4_init = ISO_PTD_DW4(0xFF);

        VPRINTF(LOW,
            "MCU: ISO IN iter%d PTD: dw0=0x%x dw1=0x%x dw2=0x%x dw3=0x%x dw4=0x%x\n",
            iter, dw0_in, dw1_in, dw2_in, dw3_in, dw4_init);

        lsu_write_32(USB_ISO_PTD_BASE + 0x20u, dw0_in);
        lsu_write_32(USB_ISO_PTD_BASE + 0x24u, dw1_in);
        lsu_write_32(USB_ISO_PTD_BASE + 0x28u, dw2_in);
        lsu_write_32(USB_ISO_PTD_BASE + 0x2Cu, dw3_in);
        lsu_write_32(USB_ISO_PTD_BASE + 0x30u, dw4_init);
        lsu_write_32(USB_ISO_PTD_BASE + 0x34u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x38u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x3Cu, 0u);
    }

    // Configure ISO list registers for slot 1 only.
    lsu_write_32(SOC_USBHSH_ISO_PTD_BASE_ADDR,
                 (USB_DMA_BASE & 0xFFFFFC00u) | (0u << 5));
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR, USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE, (1u << 8));   // ISO_LAST=1
    lsu_write_32(SOC_USBHSH_ISO_PTD_SKIP_MAP, 0xFFFFFFFDu); // skip slot 0, run slot 1
    lsu_write_32(SOC_USBHSH_USBINTR, USBHSH_ISO_IRQ);

    VPRINTF(LOW, "MCU: ISO IN iter%d config: SKIP=0xFFFFFFFD LAST_PTD=0x%x\n",
            iter, lsu_read_32(SOC_USBHSH_LAST_PTD_INUSE));

    // Clear stale IRQ then enable ISO list.
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ);
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg | USBHSH_ISO_EN);
    VPRINTF(LOW, "MCU: ISO IN iter%d: ISO_EN set. Waiting for ISO_IRQ...\n", iter);

    // Poll ISO_IRQ.
    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ,
                        ISO_IRQ_POLL_MAX, "USBSTS.ISO_IRQ(IN)")) {
        VPRINTF(LOW, "MCU: TIMEOUT - ISO_IRQ(IN) iter%d. USBSTS=0x%x\n",
                iter, lsu_read_32(SOC_USBHSH_USBSTS));
        return false;
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ISO_IRQ);

    reg = lsu_read_32(SOC_USBHSH_ISO_PTD_DONE_MAP);
    VPRINTF(LOW, "MCU: ISO IN iter%d IRQ fired. DONE_MAP=0x%x\n", iter, reg);

    if (!(reg & 0x2u)) {
        VPRINTF(LOW, "MCU: ERROR - ISO_DONE_MAP slot1 not set iter%d (map=0x%x).\n",
                iter, reg);
        return false;
    }

    // Read completion PTD DWORDs.
    dw3    = lsu_read_32(USB_ISO_PTD_BASE + 0x2Cu);
    dw4_in = lsu_read_32(USB_ISO_PTD_BASE + 0x30u);
    dw5_in = lsu_read_32(USB_ISO_PTD_BASE + 0x34u);
    dw6_in = lsu_read_32(USB_ISO_PTD_BASE + 0x38u);
    dw7_in = lsu_read_32(USB_ISO_PTD_BASE + 0x3Cu);

    VPRINTF(LOW,
        "MCU: ISO IN iter%d PTD: DW3=0x%x DW4=0x%x DW5=0x%x DW6=0x%x DW7=0x%x\n",
        iter, dw3, dw4_in, dw5_in, dw6_in, dw7_in);

    // Check DW3 Active bit.
    if (dw3 & ISO_PTD_DW3_ACTIVE_BIT) {
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d DW3 Active=1 after IRQ.\n", iter);
        return false;
    }

    // Check DW3 error flags.
    if (dw3 & ISO_PTD_DW3_HALT_BIT)
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d DW3 Halt set (0x%x).\n", iter, dw3);
    if (dw3 & ISO_PTD_DW3_BABBLE_BIT)
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d DW3 Babble set (0x%x).\n", iter, dw3);
    if (dw3 & ISO_PTD_DW3_XERR_BIT)
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d DW3 XactErr set (0x%x).\n", iter, dw3);
    if (dw3 & (ISO_PTD_DW3_HALT_BIT | ISO_PTD_DW3_BABBLE_BIT | ISO_PTD_DW3_XERR_BIT))
        return false;

    // Check DW3 NrBytesTransferred.
    nr_bytes_done = dw3 & ISO_PTD_DW3_NRBYTES_MASK;
    VPRINTF(LOW, "MCU: ISO IN iter%d NrBytesTransferred=%d (expected %d)\n",
            iter, nr_bytes_done, USB_HS_ISO_BYTES);
    if (nr_bytes_done != USB_HS_ISO_BYTES) {
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d byte count mismatch.\n", iter);
        return false;
    }

    // Check DW4 per-uSOF status fields.
    // For regular HS ISO (non-split, sec 4.1.3.3): 000=OK, 010+=error.
    for (usof_n = 0; usof_n < 8u; usof_n++) {
        status_n = (dw4_in >> ISO_PTD_DW4_STATUS_SHIFT(usof_n)) &
                   ISO_PTD_DW4_STATUS_MASK;
        if (status_n >= ISO_PTD_DW4_STATUS_ERROR) {
            VPRINTF(LOW,
                "MCU: ERROR - ISO IN iter%d DW4 uSOF%d Status=0x%x (error).\n",
                iter, usof_n, status_n);
            any_err = true;
        }
    }
    VPRINTF(LOW, "MCU: ISO IN iter%d DW4 uSOF check: err=%d DW4=0x%x\n",
            iter, (int)any_err, dw4_in);
    if (any_err)
        return false;

    // Check DW5-DW7 ISO_IN per-uSOF byte counts: sum must equal 1024.
    {
        uint32_t iso_in[8];
        iso_in[0] =  dw5_in        & 0xFFFu;
        iso_in[1] = (dw5_in >> 12) & 0xFFFu;
        iso_in[2] = ((dw5_in >> 24) & 0xFFu) | (((dw6_in >>  0) & 0xFu) << 8);
        iso_in[3] = (dw6_in >>  4) & 0xFFFu;
        iso_in[4] = (dw6_in >> 16) & 0xFFFu;
        iso_in[5] = ((dw6_in >> 28) & 0xFu)  | (((dw7_in >>  0) & 0xFFu) << 4);
        iso_in[6] = (dw7_in >>  8) & 0xFFFu;
        iso_in[7] = (dw7_in >> 20) & 0xFFFu;
        for (uint32_t k = 0; k < 8u; k++) {
            iso_in_sum += iso_in[k];
            if (iso_in[k] > 0u)
                VPRINTF(LOW, "MCU: ISO IN iter%d ISO_IN_%d = %d bytes\n",
                        iter, k, iso_in[k]);
        }
    }
    VPRINTF(LOW, "MCU: ISO IN iter%d DW5-DW7 byte sum=%d (expected %d)\n",
            iter, iso_in_sum, USB_HS_ISO_BYTES);
    if (iso_in_sum != USB_HS_ISO_BYTES) {
        VPRINTF(LOW, "MCU: ERROR - ISO IN iter%d byte count sum mismatch.\n", iter);
        return false;
    }

    // Disable ISO_EN so caller can re-arm or end test.
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg & ~USBHSH_ISO_EN);

    VPRINTF(LOW, "MCU: ISO IN iter%d PASSED.\n", iter);
    return true;
}

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static bool poll_until_clear(uint32_t addr, uint32_t mask,
                              uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (!(lsu_read_32(addr) & mask)) return true;
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT %s clear (addr=0x%x)\n", lbl, addr);
    return false;
}

static bool poll_until_set(uint32_t addr, uint32_t mask,
                            uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (lsu_read_32(addr) & mask) return true;
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT %s set (addr=0x%x)\n", lbl, addr);
    return false;
}

// ---------------------------------------------------------------------------
// usb_atl_ctrl_xfer_no_data -- SET_CONFIGURATION via ATL slot 0
// Identical to the bulk OUT test: SETUP PTD only (ATL auto-handles STATUS).
// ---------------------------------------------------------------------------
static bool usb_atl_ctrl_xfer_no_data(uint8_t dev_addr, uint8_t request,
                                       uint16_t wValue)
{
    uint32_t setup_w0 = ((uint32_t)(wValue & 0xFFu) << 16) |
                        ((uint32_t)(request)         <<  8) |
                        0x00u;
    lsu_write_32(USB_DATA_BASE + 0u, setup_w0);
    lsu_write_32(USB_DATA_BASE + 4u, 0x00000000u);

    VPRINTF(LOW, "MCU: CTRL SETUP addr=%d req=0x%x wValue=0x%x\n",
            dev_addr, request, wValue);

    lsu_write_32(USB_ATL_PTD_BASE + 0x00u, CTRL_PTD_W0);
    lsu_write_32(USB_ATL_PTD_BASE + 0x04u, PTD_W1(0, 0, 0, 0, dev_addr));
    lsu_write_32(USB_ATL_PTD_BASE + 0x08u, CTRL_PTD_W2_SETUP);
    lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, CTRL_PTD_W3_SETUP);
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ);

    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ,
                        CTRL_IRQ_POLL_MAX, "CTRL_SETUP_IRQ")) {
        VPRINTF(LOW, "MCU: CTRL SETUP timeout\n");
        return false;
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_ATL_IRQ);

    {
        uint32_t done = lsu_read_32(SOC_USBHSH_ATL_PTD_DONE_MAP);
        uint32_t w3   = lsu_read_32(USB_ATL_PTD_BASE + 0x0Cu);
        VPRINTF(LOW, "MCU: CTRL IRQ check: DONE_MAP=0x%x PTD_W3=0x%x\n",
                done, w3);
        if (!(done & 0x1u)) {
            VPRINTF(LOW, "MCU: CTRL DONE_MAP slot0 not set\n");
            return false;
        }
        if (w3 & PTD_W3_ACTIVE_BIT) {
            VPRINTF(LOW, "MCU: CTRL PTD Active=1 after IRQ\n");
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

    VPRINTF(LOW,
        "=================\n"
        "MCU: USB HS host ISO OUT test (DUT=HOST HS, VIP=DEVICE)\n"
        "=================\n\n");

    boot_mcu();

    mcu_cptra_advance_brkpoint();
    VPRINTF(LOW, "MCU: Caliptra brkpoint advanced. Starting USB init.\n");

    // -----------------------------------------------------------------------
    // Step 1: HCRESET
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD,
                 lsu_read_32(SOC_USBHSH_USBCMD) | USBHSH_HCRESET);
    if (!poll_until_clear(SOC_USBHSH_USBCMD, USBHSH_HCRESET,
                          HCRESET_POLL_MAX, "HCRESET")) {
        VPRINTF(LOW, "MCU: FATAL - HCRESET did not clear.\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: HCRESET complete.\n");

    // -----------------------------------------------------------------------
    // Step 2: HOST mode, RS
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTMODE, USBHSH_PORT_MODE_HOST);
    VPRINTF(LOW, "MCU: PORTMODE = HOST.\n");

    lsu_write_32(SOC_USBHSH_USBCMD, USBHSH_RS);
    VPRINTF(LOW, "MCU: USBCMD RS set.\n");

    // -----------------------------------------------------------------------
    // Step 3: Write ISO PTD slot 0 (INACTIVE, V=0) before port reset.
    //   uFrame[7:3]=0 (frame 0), uSA=0xFF (every uSOF of that frame).
    //   Set V=0 now; set Active=1 and V=1 after enumeration.
    // -----------------------------------------------------------------------
    {
        uint32_t dw0 = ISO_PTD_DW0(1, USB_HS_ISO_MAXPKT, 0x00, 0);
        uint32_t dw1 = ISO_PTD_DW1(0, 0, 0, 1, 1);
        uint32_t dw2 = ISO_PTD_DW2(USB_DATA_START_ADDR, 1, USB_HS_ISO_BYTES);
        uint32_t dw3_v = ISO_PTD_DW3(0, 0, 0, 1, 0, 0);
        uint32_t dw4 = ISO_PTD_DW4(0xFF);

        VPRINTF(LOW,
            "MCU: ISO PTD (inactive): dw0=0x%x dw1=0x%x dw2=0x%x dw3=0x%x dw4=0x%x\n",
            dw0, dw1, dw2, dw3_v, dw4);

        lsu_write_32(USB_ISO_PTD_BASE + 0x00u, dw0);
        lsu_write_32(USB_ISO_PTD_BASE + 0x04u, dw1);
        lsu_write_32(USB_ISO_PTD_BASE + 0x08u, dw2);
        lsu_write_32(USB_ISO_PTD_BASE + 0x0Cu, dw3_v);
        lsu_write_32(USB_ISO_PTD_BASE + 0x10u, dw4);
        lsu_write_32(USB_ISO_PTD_BASE + 0x14u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x18u, 0u);
        lsu_write_32(USB_ISO_PTD_BASE + 0x1Cu, 0u);
    }

    // -----------------------------------------------------------------------
    // Step 4: Initialize 1024-byte payload: word[i] = i
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Writing 1024B payload at 0x%x (word[i]=i).\n",
            USB_DATA_BASE);
    for (uint32_t i = 0; i < (USB_HS_ISO_BYTES / 4u); i++)
        lsu_write_32(USB_DATA_BASE + (i * 4u), i);
    VPRINTF(LOW, "MCU: Payload written.\n");

    // -----------------------------------------------------------------------
    // Step 5: Pre-configure ATL registers for enumeration CTRL PTD.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_ATL_PTD_BASE_ADDR,      USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR,  USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE,          0x00000000u);
    lsu_write_32(SOC_USBHSH_USBINTR,                 USBHSH_ATL_IRQ);
    lsu_write_32(SOC_USBHSH_FLADJ_FRINDEX,           0x00000020u);
    lsu_write_32(SOC_USBHSH_ATL_PTD_SKIP_MAP,        0xFFFFFFFEu);
    VPRINTF(LOW, "MCU: ATL config pre-loaded.\n");

    // -----------------------------------------------------------------------
    // Step 6: Port Power + Port Reset (HS chirp)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTSC1,
                 lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PP);
    lsu_write_32(SOC_USBHSH_PORTSC1,
                 lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PR);
    VPRINTF(LOW, "MCU: PP + PR asserted (HS chirp in progress).\n");

    for (volatile uint32_t d = 0; d < PR_HOLD_DELAY; d++) { /* spin */ }

    lsu_write_32(SOC_USBHSH_PORTSC1,
                 lsu_read_32(SOC_USBHSH_PORTSC1) & ~USBHSH_PR);
    VPRINTF(LOW, "MCU: PR deasserted.\n");

    if (!poll_until_clear(SOC_USBHSH_PORTSC1, USBHSH_PR,
                          PR_CLEAR_POLL_MAX, "PORTSC1.PR"))
        VPRINTF(LOW, "MCU: WARNING - PR did not self-clear.\n");
    VPRINTF(LOW, "MCU: Port Reset complete.\n");

    // -----------------------------------------------------------------------
    // Step 7: Re-write ATL config after port reset, then enable ATL+ISO.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_ATL_PTD_BASE_ADDR,      USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_DATA_PAYLOAD_BASE_ADDR,  USB_DMA_BASE);
    lsu_write_32(SOC_USBHSH_LAST_PTD_INUSE,          0x00000000u);
    lsu_write_32(SOC_USBHSH_USBINTR,                 USBHSH_ATL_IRQ);
    lsu_write_32(SOC_USBHSH_FLADJ_FRINDEX,           0x00000020u);
    lsu_write_32(SOC_USBHSH_ATL_PTD_SKIP_MAP,        0xFFFFFFFEu);
    VPRINTF(LOW, "MCU: ATL config re-written after port reset.\n");

    // Re-write ATL CTRL PTD placeholder (V=1, Active=1) so slot 0 is ready
    // for enumeration. Actual PTD words are overwritten in ctrl_xfer below.
    lsu_write_32(USB_ATL_PTD_BASE + 0x00u, CTRL_PTD_W0);
    lsu_write_32(USB_ATL_PTD_BASE + 0x04u, PTD_W1(0, 0, 0, 0, 1));
    lsu_write_32(USB_ATL_PTD_BASE + 0x08u, CTRL_PTD_W2_SETUP);
    lsu_write_32(USB_ATL_PTD_BASE + 0x0Cu, CTRL_PTD_W3_SETUP);
    VPRINTF(LOW, "MCU: ATL CTRL PTD pre-written.\n");

    // -----------------------------------------------------------------------
    // Enable ATL before PSPD/PED verification -- matches bulk_out.c Step 10.
    // twtrev is set to 10ms in the test so timing is not critical, but
    // keeping the same ordering as bulk_out.c (clear USBSTS -> ATL_EN ->
    // then PSPD/PED read-only checks) avoids any unnecessary delay between
    // port reset complete and ATL list processing start.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBSTS, 0xFFFFFFFFu);
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg | USBHSH_ATL_EN);
    VPRINTF(LOW, "MCU: ATL_EN set for enumeration.\n");

    // Verify PSPD (post-ATL_EN, same order as bulk_out.c)
    reg  = lsu_read_32(SOC_USBHSH_PORTSC1);
    pspd = (reg & USBHSH_PSPD_MASK) >> USBHSH_PSPD_SHIFT;
    VPRINTF(LOW, "MCU: PORTSC1=0x%x PSPD=%d (%s)\n", reg, pspd,
            (pspd == 2) ? "HS" : (pspd == 1) ? "FS" : "LS/unknown");
    if (pspd != 2u) {
        VPRINTF(LOW, "MCU: FATAL - Expected PSPD=HS(2), got %d.\n", pspd);
        csr_write_mpmc_halt();
    }

    // Verify PED and clear PEDC (fatal if not set, same as bulk_out.c).
    if ((reg & USBHSH_PEDC) && (reg & USBHSH_PED)) {
        lsu_write_32(SOC_USBHSH_PORTSC1,
                     lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PEDC);
        VPRINTF(LOW, "MCU: Port enabled (PED=1). PEDC cleared.\n");
    } else {
        VPRINTF(LOW, "MCU: FATAL - PEDC or PED not set (PORTSC1=0x%x).\n", reg);
        csr_write_mpmc_halt();
    }

    // -----------------------------------------------------------------------
    // Step 8: Enumerate - SET_CONFIGURATION(1) to addr=1
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: SET_CONFIGURATION(1) to addr=1...\n");
    if (!usb_atl_ctrl_xfer_no_data(1, USB_REQ_SET_CONFIGURATION, 1)) {
        VPRINTF(LOW, "MCU: FATAL - SET_CONFIGURATION failed.\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: SET_CONFIGURATION done. VIP EP1 ISO now ACTIVE.\n");

    // Restore payload words 0/1 overwritten by SETUP packet
    lsu_write_32(USB_DATA_BASE + 0u, 0x00000000u);
    lsu_write_32(USB_DATA_BASE + 4u, 0x00000001u);

    // -----------------------------------------------------------------------
    // Step 9: Switch to ISO list.
    //   Disable ATL; the iso_out_run() helper will write the PTD, configure
    //   registers, enable ISO_EN, poll IRQ, check status, and disable ISO_EN.
    // -----------------------------------------------------------------------
    reg = lsu_read_32(SOC_USBHSH_USBCMD);
    lsu_write_32(SOC_USBHSH_USBCMD, reg & ~USBHSH_ATL_EN);
    VPRINTF(LOW, "MCU: ATL_EN cleared, switching to ISO list.\n");

    // -----------------------------------------------------------------------
    // Steps 10-11: 2 iterations of ISO OUT (slot 0, EP1 Token=OUT).
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: === ISO OUT iteration 1 ===\n");
    if (!iso_out_run(1)) {
        VPRINTF(LOW, "MCU: USB HS host ISO OUT+IN 2x2 - FAILED (OUT iter1)\n");
        csr_write_mpmc_halt();
    }

    VPRINTF(LOW, "MCU: === ISO OUT iteration 2 ===\n");
    if (!iso_out_run(2)) {
        VPRINTF(LOW, "MCU: USB HS host ISO OUT+IN 2x2 - FAILED (OUT iter2)\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Both ISO OUT iterations PASSED.\n");

    // -----------------------------------------------------------------------
    // Steps 12-15: 2 iterations of ISO IN (slot 1, EP2 Token=IN).
    //   Full check per iteration: DW3 error flags, NrBytesTransferred,
    //   DW4 uSOF status, DW5-DW7 byte count sum.
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: === ISO IN iteration 1 ===\n");
    if (!iso_in_run(1)) {
        VPRINTF(LOW, "MCU: USB HS host ISO OUT+IN 2x2 - FAILED (IN iter1)\n");
        csr_write_mpmc_halt();
    }

    VPRINTF(LOW, "MCU: === ISO IN iteration 2 ===\n");
    if (!iso_in_run(2)) {
        VPRINTF(LOW, "MCU: USB HS host ISO OUT+IN 2x2 - FAILED (IN iter2)\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Both ISO IN iterations PASSED.\n");

    VPRINTF(LOW, "MCU: USB HS host ISO OUT+IN 2x2 - PASSED\n");
    VPRINTF(LOW, "MCU: Halting.\n");
    csr_write_mpmc_halt();
}
