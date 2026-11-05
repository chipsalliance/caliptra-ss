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
// Shared types and address-map constants for USB compound functional coverage.
//
// This package is compiled into BOTH the subsystem bench (caliptra_ss_top_tb)
// and the compound unit bench (usb_top_tb). The coverage interfaces that use
// it are bound by MODULE NAME, never by hierarchy path, so the resulting
// covergroup names and bin names are identical in both benches and URG can
// merge the two coverage databases without manual mapping.
//
// Every constant below is taken from the RTL / SystemRDL, not from the
// programmer's guide prose:
//   usb_compound_pkg.sv         combo-port aperture bases and limits
//   usb_compound_ahb_decoder.sv aligned-32-bit accept rule, error response
//   usb_hub.rdl                 hub word map (CONTROL is word 12, bit 0 = ENABLE)
//   usbhsd.rdl                  device CSR word map
package usb_cov_pkg;

  // ---------------------------------------------------------------------------
  // Combo-port regions
  // ---------------------------------------------------------------------------
  // Combo-port-local byte offsets. DEV0 CSR 0x000-0x03F, a decode hole up to
  // 0x7FF, recovery 0x800-0xFFF, hub from 0x1000. The hub aperture is rounded
  // up to a power of two, so the words at or above C_HUB_FIFO_SIZE form a
  // padding sub-region that reads zero and returns OKAY rather than an error.
  localparam int unsigned COMBO_DEV0_CSR_BASE  = 32'h0000_0000;
  localparam int unsigned COMBO_DEV0_CSR_LIMIT = 32'h0000_0040;
  localparam int unsigned COMBO_RECOVERY_BASE  = 32'h0000_0800;
  localparam int unsigned COMBO_RECOVERY_LIMIT = 32'h0000_1000;
  localparam int unsigned COMBO_HUB_BASE       = 32'h0000_1000;

  typedef enum int {
    COMBO_REGION_DEV0_CSR,   // the 16-word device 0 control/status bank
    COMBO_REGION_HOLE,       // unmapped: must produce the two-phase AHB error
    COMBO_REGION_RECOVERY,   // OCP recovery register aperture
    COMBO_REGION_HUB_IMPL,   // implemented hub words 0 .. C_HUB_FIFO_SIZE-1
    COMBO_REGION_HUB_PAD     // hub aperture padding: reads zero, OKAY
  } combo_region_e;

  // ---------------------------------------------------------------------------
  // Hub bank word classes
  // ---------------------------------------------------------------------------
  // The hub bank is one flat word array, but the words are not functionally
  // equivalent: three of them are registers and one is a table pointer, so
  // coverage is collected per class instead of per word.
  localparam int unsigned HUB_WORD_CONTROL    = 12;  // byte offset 0x30
  localparam int unsigned HUB_WORD_LPM        = 13;  // byte offset 0x34
  localparam int unsigned HUB_WORD_DEV_LINK   = 14;  // byte offset 0x38
  localparam int unsigned HUB_WORD_ULPIDEBUG  = 15;  // byte offset 0x3c
  localparam int unsigned HUB_WORD_DESC_HIGH  = 16;  // first descriptor-high word

  typedef enum int {
    HUB_WORD_CLASS_DESC_LOW,    // words 0-11, self-initialized from C_EP0_ROM
    HUB_WORD_CLASS_CONTROL,     // always writable, even while the table is locked
    HUB_WORD_CLASS_LPM,
    HUB_WORD_CLASS_DEV_LINK,    // SETUP-match table link pointer
    HUB_WORD_CLASS_ULPIDEBUG,
    HUB_WORD_CLASS_DESC_HIGH,   // descriptors and SETUP-match entries
    HUB_WORD_CLASS_OUT_OF_RANGE // at or above C_HUB_FIFO_SIZE
  } hub_word_class_e;

  // Hub CONTROL register bit positions. Note ENABLE is bit 0; the programmer's
  // guide claim of bit 7 does not match the RTL.
  localparam int unsigned HUB_CTRL_BIT_ENABLE          = 0;
  localparam int unsigned HUB_CTRL_BIT_FORCE_NEEDCLK   = 9;
  localparam int unsigned HUB_CTRL_BIT_FORCE_VBUS      = 10;
  localparam int unsigned HUB_CTRL_BIT_LPM_SUP         = 11;
  localparam int unsigned HUB_CTRL_BIT_DCON            = 16;
  localparam int unsigned HUB_CTRL_BIT_SELF_POWERED    = 18;
  localparam int unsigned HUB_CTRL_BIT_FORCE_FULLSPEED = 21;
  localparam int unsigned HUB_CTRL_LSB_SPEED           = 22;  // [23:22], read only
  localparam int unsigned HUB_CTRL_BIT_VBUS_DEBOUNCED  = 28;  // read only

  // ---------------------------------------------------------------------------
  // Device CSR word map
  // ---------------------------------------------------------------------------
  // Only haddr[5:2] is decoded, so the bank is exactly 16 words and any higher
  // offset aliases back into it.
  typedef enum int {
    DEV_CSR_DEVCMDSTAT   = 0,
    DEV_CSR_INFO         = 1,
    DEV_CSR_EPLISTSTART  = 2,
    DEV_CSR_DATABUFSTART = 3,
    DEV_CSR_LPM          = 4,
    DEV_CSR_EPSKIP       = 5,
    DEV_CSR_EPINUSE      = 6,
    DEV_CSR_EPBUFCFG     = 7,
    DEV_CSR_INTSTAT      = 8,
    DEV_CSR_INTEN        = 9,
    DEV_CSR_INTSETSTAT   = 10,
    DEV_CSR_INTROUTE     = 11,
    DEV_CSR_CONFIG       = 12,
    DEV_CSR_EPTOGGLE     = 13,
    DEV_CSR_RESERVED     = 14,
    DEV_CSR_ULPIDEBUG    = 15
  } dev_csr_word_e;

  // DEVCMDSTAT bit positions used by the status and configuration coverage.
  localparam int unsigned DEVCMDSTAT_BIT_DEV_EN          = 7;
  localparam int unsigned DEVCMDSTAT_BIT_SETUP           = 8;
  localparam int unsigned DEVCMDSTAT_BIT_FORCE_NEEDCLK   = 9;
  localparam int unsigned DEVCMDSTAT_BIT_FORCE_VBUS      = 10;
  localparam int unsigned DEVCMDSTAT_BIT_LPM_SUP         = 11;
  localparam int unsigned DEVCMDSTAT_BIT_DCON            = 16;
  localparam int unsigned DEVCMDSTAT_BIT_DSUS            = 17;
  localparam int unsigned DEVCMDSTAT_BIT_LPM_SUS         = 19;
  localparam int unsigned DEVCMDSTAT_BIT_LPM_REWP        = 20;
  localparam int unsigned DEVCMDSTAT_BIT_FORCE_FULLSPEED = 21;
  localparam int unsigned DEVCMDSTAT_LSB_SPEED           = 22;  // [23:22]
  localparam int unsigned DEVCMDSTAT_BIT_DCON_C          = 24;
  localparam int unsigned DEVCMDSTAT_BIT_DSUS_C          = 25;
  localparam int unsigned DEVCMDSTAT_BIT_DRES_C          = 26;
  localparam int unsigned DEVCMDSTAT_BIT_VBUS_DEBOUNCED  = 28;

  // ---------------------------------------------------------------------------
  // Common enumerations
  // ---------------------------------------------------------------------------
  typedef enum int { ACCESS_READ, ACCESS_WRITE } access_dir_e;

  // Response class as seen by the upstream manager, collapsed to the two
  // architecturally distinct outcomes.
  typedef enum int { RESP_CLASS_OKAY, RESP_CLASS_ERROR } resp_class_e;

  // Shape qualification applied by the combo decoder before it selects any
  // downstream endpoint.
  typedef enum int {
    ACCESS_SHAPE_WORD_ALIGNED,   // hsize == 2 and haddr[1:0] == 0: the only accepted shape
    ACCESS_SHAPE_BAD_SIZE,
    ACCESS_SHAPE_UNALIGNED
  } access_shape_e;

  // Which of the three logical USB functions a device-side resource belongs
  // to. The hub is hardware, DEV0 and DEV1 are firmware owned.
  typedef enum int { USB_FUNC_HUB, USB_FUNC_DEV0, USB_FUNC_DEV1 } usb_function_e;

  // Negotiated link speed as reported in the Speed field.
  typedef enum logic [1:0] {
    LINK_SPEED_RESERVED = 2'b00,
    LINK_SPEED_FS       = 2'b01,
    LINK_SPEED_HS       = 2'b10,
    LINK_SPEED_SS       = 2'b11
  } link_speed_e;

  // ---------------------------------------------------------------------------
  // Decode helpers
  // ---------------------------------------------------------------------------
  // Classify a combo-port-local byte address. hub_words is the configured
  // C_HUB_FIFO_SIZE and hub_aperture_bytes is its power-of-two rounded size,
  // so the padding sub-region can be told apart from the implemented words.
  function automatic combo_region_e combo_region(
      input logic [31:0]  byte_addr,
      input int unsigned  hub_words,
      input int unsigned  hub_aperture_bytes);
    if (byte_addr < COMBO_DEV0_CSR_LIMIT) begin
      return COMBO_REGION_DEV0_CSR;
    end
    if (byte_addr < COMBO_RECOVERY_BASE) begin
      return COMBO_REGION_HOLE;
    end
    if (byte_addr < COMBO_RECOVERY_LIMIT) begin
      return COMBO_REGION_RECOVERY;
    end
    if (byte_addr < (COMBO_HUB_BASE + (hub_words * 4))) begin
      return COMBO_REGION_HUB_IMPL;
    end
    if (byte_addr < (COMBO_HUB_BASE + hub_aperture_bytes)) begin
      return COMBO_REGION_HUB_PAD;
    end
    // Above the rounded aperture the decoder sees no hit at all.
    return COMBO_REGION_HOLE;
  endfunction

  function automatic hub_word_class_e hub_word_class(
      input int unsigned word_addr,
      input int unsigned hub_words);
    if (word_addr >= hub_words)          return HUB_WORD_CLASS_OUT_OF_RANGE;
    if (word_addr <  HUB_WORD_CONTROL)   return HUB_WORD_CLASS_DESC_LOW;
    if (word_addr == HUB_WORD_CONTROL)   return HUB_WORD_CLASS_CONTROL;
    if (word_addr == HUB_WORD_LPM)       return HUB_WORD_CLASS_LPM;
    if (word_addr == HUB_WORD_DEV_LINK)  return HUB_WORD_CLASS_DEV_LINK;
    if (word_addr == HUB_WORD_ULPIDEBUG) return HUB_WORD_CLASS_ULPIDEBUG;
    return HUB_WORD_CLASS_DESC_HIGH;
  endfunction

  function automatic access_shape_e access_shape(
      input logic [2:0]  hsize,
      input logic [1:0]  low_addr);
    if (hsize != 3'd2)     return ACCESS_SHAPE_BAD_SIZE;
    if (low_addr != 2'd0)  return ACCESS_SHAPE_UNALIGNED;
    return ACCESS_SHAPE_WORD_ALIGNED;
  endfunction

  function automatic resp_class_e resp_class(input logic [1:0] hresp);
    return (hresp == 2'b00) ? RESP_CLASS_OKAY : RESP_CLASS_ERROR;
  endfunction

  // ---------------------------------------------------------------------------
  // Device link power state
  // ---------------------------------------------------------------------------
  // Derived from the three DEVCMDSTAT status bits the register actually returns
  // to firmware: DCON (bit 16), DSUS (bit 17) and LPM_SUS (bit 19). L1 is
  // checked before L2 because the IP shares DSUS_C between the two state
  // changes and can present both suspend bits together while in L1.
  typedef enum int {
    LINK_STATE_DISCONNECTED,
    LINK_STATE_L0_ACTIVE,
    LINK_STATE_L1_SLEEP,
    LINK_STATE_L2_SUSPEND
  } link_state_e;

  function automatic link_state_e link_state(
      input logic dcon,
      input logic dsus,
      input logic lpm_sus);
    if (!dcon)   return LINK_STATE_DISCONNECTED;
    if (lpm_sus) return LINK_STATE_L1_SLEEP;
    if (dsus)    return LINK_STATE_L2_SUSPEND;
    return LINK_STATE_L0_ACTIVE;
  endfunction

  // How a low-power state was left. Device-initiated wakeup is the hard path
  // and the one the *_dev_wakeup tests exist to reach; a bus reset exit is a
  // legal but distinct recovery.
  typedef enum int {
    LP_EXIT_NONE,
    LP_EXIT_HOST_RESUME,
    LP_EXIT_DEVICE_WAKEUP,
    LP_EXIT_BUSRESET,
    LP_EXIT_VBUS_LOSS
  } lp_exit_cause_e;

  // ---------------------------------------------------------------------------
  // Endpoint and transfer classification (PIE sourced)
  // ---------------------------------------------------------------------------
  // Endpoint 0 is always the control endpoint; the IP reports isochronous
  // endpoints with a dedicated flag and everything else is a bulk/interrupt
  // style endpoint, which the transaction layer treats identically.
  typedef enum int {
    EP_KIND_CONTROL,
    EP_KIND_ISO,
    EP_KIND_BULK_INT
  } ep_kind_e;

  function automatic ep_kind_e ep_kind(
      input logic [3:0] ep_num,
      input logic       is_iso);
    if (ep_num == 4'd0) return EP_KIND_CONTROL;
    if (is_iso)         return EP_KIND_ISO;
    return EP_KIND_BULK_INT;
  endfunction

  typedef enum int { EP_DIR_OUT, EP_DIR_IN } ep_dir_e;

  // Transaction outcome as the PIE reports it. NAK is checked first because
  // pie_sentNAK is a flow-control response rather than a failure, and the IP
  // can raise it alongside the end-of-transfer handshake.
  typedef enum int {
    XFER_OUTCOME_SUCCESS,
    XFER_OUTCOME_NAK,
    XFER_OUTCOME_ERROR
  } xfer_outcome_e;

  function automatic xfer_outcome_e xfer_outcome(
      input logic success,
      input logic error,
      input logic sent_nak);
    if (sent_nak) return XFER_OUTCOME_NAK;
    if (error)    return XFER_OUTCOME_ERROR;
    return XFER_OUTCOME_SUCCESS;
  endfunction

  // Payload size classes, bucketed at the architectural packet boundaries the
  // DMA actually clamps against.
  //
  // The IP does NOT carry a max-packet byte count on an observable port. The
  // DMA recomputes it per transaction in its CHECK_EPINFO state from the
  // negotiated speed, the periodic flag, the rate-feedback flag and the
  // endpoint number:
  //
  //   HS, EP0                     -> 64
  //   HS, periodic, rf_tv = 0     -> 3072   (high bandwidth ISO)
  //   HS, periodic, rf_tv = 1     -> 1024   (high bandwidth interrupt)
  //   HS, otherwise               -> 512    (bulk / interrupt)
  //   FS, periodic, rf_tv = 0     -> 1023   (FS ISO)
  //   FS, otherwise               -> 64
  //
  // epinfo_periodic and epinfo_rf_tv live inside usb_dma, which sits in an
  // unnamed generate block and is therefore not reachable by cross-module
  // reference, so the per-endpoint limit cannot be reconstructed in the
  // observer. Bucketing on the absolute boundaries instead keeps every class
  // meaningful without inventing a limit: whichever limit applies, it is one
  // of these values, so a transfer landing exactly on one is the interesting
  // boundary case and the cross with ep_kind/speed says which limit was in
  // force.
  typedef enum int {
    XFER_SIZE_ZLP,          // zero-length packet: a protocol event in itself
    XFER_SIZE_ONE,
    XFER_SIZE_SMALL,        // 2 .. 63
    XFER_SIZE_64,           // EP0 and FS bulk/interrupt limit
    XFER_SIZE_65_511,
    XFER_SIZE_512,          // HS bulk/interrupt limit
    XFER_SIZE_513_1022,
    XFER_SIZE_1023,         // FS ISO limit
    XFER_SIZE_1024,         // HS high-bandwidth interrupt limit
    XFER_SIZE_ABOVE_1024    // up to the 3072 HS high-bandwidth ISO limit
  } xfer_size_class_e;

  function automatic xfer_size_class_e xfer_size_class(input int unsigned nbytes);
    if (nbytes == 0)    return XFER_SIZE_ZLP;
    if (nbytes == 1)    return XFER_SIZE_ONE;
    if (nbytes <  64)   return XFER_SIZE_SMALL;
    if (nbytes == 64)   return XFER_SIZE_64;
    if (nbytes <  512)  return XFER_SIZE_65_511;
    if (nbytes == 512)  return XFER_SIZE_512;
    if (nbytes <  1023) return XFER_SIZE_513_1022;
    if (nbytes == 1023) return XFER_SIZE_1023;
    if (nbytes == 1024) return XFER_SIZE_1024;
    return XFER_SIZE_ABOVE_1024;
  endfunction

  // ---------------------------------------------------------------------------
  // Compound function selection
  // ---------------------------------------------------------------------------
  // The PIE is a single shared instance time-multiplexed across the hub and
  // the two software devices, and it exports the current selection as an
  // integer. usbreg_deviceenabled uses the same numbering, so these indices
  // are the one source of truth for attributing PIE traffic to a function.
  localparam int unsigned USB_SEL_HUB  = 0;
  localparam int unsigned USB_SEL_DEV0 = 1;
  localparam int unsigned USB_SEL_DEV1 = 2;

endpackage : usb_cov_pkg

// File contains AI-generated response based on internal company sources
