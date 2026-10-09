// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// you may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Apply picosecond defaults at the SVT include boundary, then explicitly
// restore the bench's nanosecond default rather than inherit the vendor
// files' final timescale.
`timescale 1ps/1ps
`include "svt_usb.uvm.pkg"
`include "svt_mphy.uvm.pkg"
`timescale 1ns/1ps
// Shared Caliptra AXI width defines, as used by caliptra_ss_top_tb.
`include "config_defines.svh"

package usb_tb_pkg;
  timeunit 1ns;
  timeprecision 1ps;

  import uvm_pkg::*;
  import aaxi_pkg::*;
  import aaxi_pkg_xactor::*;
  import svt_uvm_pkg::*;
  import svt_usb_uvm_pkg::*;
  import usb_combo_ral_pkg::*;
  import usb_dev1_csr_ral_pkg::*;
  import usb_dev0_mem_ral_pkg::*;
  import usb_dev1_mem_ral_pkg::*;
  import usb_ral_config_pkg::*;
  import usb_compound_pkg::*;
  `include "uvm_macros.svh"

  // AXI interface widths match the USB axi_if instances in caliptra_ss_top_tb.
  localparam int unsigned USB_AXI_ADDR_WIDTH = 64;
  localparam int unsigned USB_AXI_DATA_WIDTH = 32;
  localparam int unsigned USB_PACKET_RAM_DATA_WIDTH = 64;
  localparam int unsigned USB_DEV0_RAM_DEPTH = 8192;
  localparam int unsigned USB_DEV1_RAM_DEPTH = 8192;
  localparam int unsigned USB_HUB_FIFO_SIZE = 172;
  localparam int unsigned USB_DEV0_NBPHYSEP = 28;
  localparam int unsigned USB_DEV1_NBPHYSEP = 28;
  localparam logic [31:0] USB_DEV0_ROUTE_MASK = (32'hffff_ffff >> (30 - USB_DEV0_NBPHYSEP)) | 32'hc000_0000;
  localparam logic [31:0] USB_DEV1_ROUTE_MASK = (32'hffff_ffff >> (30 - USB_DEV1_NBPHYSEP)) | 32'hc000_0000;
  localparam int unsigned USB_EPUB = 32;
  localparam int unsigned USB_DAUB = 32;
  localparam int unsigned USB_DALB = 17;
  localparam logic [31:0] USB_EPFIFO_PAGE = 32'h0008_0000;
  localparam logic [31:0] USB_DATAFIFO_PAGE = 32'h0008_0000;
  localparam int unsigned USB_SINGLE_BUFFER_SUPPORTED = 1;
  localparam int unsigned USB_DOUBLE_BUFFER_SUPPORTED = 1;
  localparam int unsigned USB_TOGGLE_REG_READABLE = 1;

  // Mirror the wrapper's port-local byte geometry. HUB depth counts 32-bit
  // words; round it to a power-of-two aperture and add two byte-offset bits.
  // Keep the exclusive HUB limit in the map package's 33-bit address sizing
  // before deriving the COMBO width.
  localparam int unsigned USB_COMBO_LOCAL_ADDR_WIDTH =
      $clog2(33'(usb_compound_pkg::HUB_BASE_ADDR +
                 (33'd1 << ($clog2(USB_HUB_FIFO_SIZE) + 2))));
  // Packet SRAM depths count 64-bit rows, requiring three byte-offset bits.
  // DEV1 CSR uses the shared map package's byte-address width directly.
  localparam int unsigned USB_DEV0_MEM_LOCAL_ADDR_WIDTH = $clog2(USB_DEV0_RAM_DEPTH) + 3;
  localparam int unsigned USB_DEV1_CSR_LOCAL_ADDR_WIDTH = usb_compound_pkg::DEV_CSR_ADDR_WIDTH;
  localparam int unsigned USB_DEV1_MEM_LOCAL_ADDR_WIDTH = $clog2(USB_DEV1_RAM_DEPTH) + 3;

  localparam int USB_TARGET_COUNT = 5;
  localparam int USB_TB_AXI_USER_WIDTH = `CALIPTRA_AXI_USER_WIDTH;
  // AXI USER allowlist depth per policy; matches caliptra_ss_top_tb
  // USB_*_NUM_PRIV_AXI_USERS_TB and is shared by the wrapper and TB control interface.
  localparam int unsigned USB_COMBO_NUM_PRIV_AXI_USERS = 2;
  localparam int unsigned USB_DEV1_NUM_PRIV_AXI_USERS = 2;
  // One AXI USER value and the two allowlists usb_tb_ctrl_if drives.
  typedef bit [USB_TB_AXI_USER_WIDTH-1:0] usb_axi_user_t;
  typedef usb_axi_user_t usb_combo_allowlist_t[USB_COMBO_NUM_PRIV_AXI_USERS];
  typedef usb_axi_user_t usb_dev1_allowlist_t[USB_DEV1_NUM_PRIV_AXI_USERS];
  // usb_top_tb checks this against the Avery interface ID width, which
  // includes its default interconnect ID padding.
  localparam int USB_TB_AXI_ID_WIDTH = `CALIPTRA_AXI_ID_WIDTH;

  // Defaults only. The live values are the matching usb_env_cfg fields and
  // usb_base_test::test_timeout; see those for how a test, a parent
  // component, or the command line overrides them.
  localparam time USB_DEFAULT_RESET_TIMEOUT = 5us;
  localparam time USB_DEFAULT_TRANSFER_TIMEOUT = 10us;
  localparam time USB_DEFAULT_VBUS_TIMEOUT = 500us;
  localparam time USB_DEFAULT_LINK_TIMEOUT = 750us;
  localparam time USB_DEFAULT_CONTROL_TRANSFER_TIMEOUT = 100us;
  localparam time USB_DEFAULT_TEST_TIMEOUT = 1ms;

  // Address the host assigns with SET_ADDRESS during enumeration.
  localparam bit [6:0] USB_DEFAULT_DEVICE_ADDRESS = 7'd1;

  // Global event names published by usb_utmi_packet_monitor. A sequence resets
  // and waits on the event it needs immediately before starting stimulus.
  localparam string USB_UTMI_OUT_TOKEN_EVENT = "usb_utmi_out_token_seen";
  localparam string USB_UTMI_DATA_PACKET_EVENT = "usb_utmi_data_packet_seen";

  // Compare deadlines at the package's 1ps precision, without rounding to
  // whole nanoseconds or depending on floating-point equality.
  function automatic time usb_time_ps(realtime value);
    return time'(value / 1ps);
  endfunction

  typedef enum int {
    USB_HUB,
    USB_DEV0_CSR,
    USB_DEV0_SRAM,
    USB_DEV1_CSR,
    USB_DEV1_SRAM
  } usb_target_e;

  // Bench-local endpoint identity, independent of Synopsys VIP types.
  // USB 2.0 endpoint direction (endpoint address bit 7 "Direction"),
  // named from the host's perspective.
  typedef enum int {
    USB_DIRECTION_OUT,
    USB_DIRECTION_IN
  } usb_direction_e;

  // USB 2.0 transfer type (endpoint descriptor bmAttributes "Transfer Type").
  // Distinct from the DEV0 endpoint-list "Endpoint Type" (T) bit, which
  // selects generic versus periodic handling.
  typedef enum int {
    USB_TRANSFER_TYPE_CONTROL,
    USB_TRANSFER_TYPE_BULK,
    USB_TRANSFER_TYPE_INTERRUPT,
    USB_TRANSFER_TYPE_ISOCHRONOUS
  } usb_transfer_type_e;

  // One DEV0 endpoint-list command/status word (USB2 Programmer's Guide 4.2.2
  // and 4.2.3). The list lives in packet memory, which the RAL models as a
  // field-less uvm_mem, so the layout is captured here instead. On EP0 entries
  // ep_type and disabled are reserved; the SETUP entry uses only buffer_offset.
  typedef struct packed {
    logic        active;        // [31] hardware owns the buffer
    logic        disabled;      // [30] generic endpoints only
    logic        stall;         // [29]
    logic        toggle_reset;  // [28]
    logic        toggle_value;  // [27] TV, or RF for periodic endpoints
    logic        ep_type;       // [26] 0 generic, 1 periodic
    logic [14:0] nbytes;        // [25:11] byte count, decremented by hardware
    logic [10:0] buffer_offset; // [10:0] buffer address in 64-byte units
  } usb_ep_entry_t;

  typedef struct {
    int unsigned writes;
    int unsigned reads;
    int unsigned comparisons;
  } usb_target_stats_t;

  function automatic string usb_target_name(usb_target_e target);
    case (target)
      USB_HUB:       return "HUB";
      USB_DEV0_CSR:  return "DEV0CSR";
      USB_DEV0_SRAM: return "DEV0SRAM";
      USB_DEV1_CSR:  return "DEV1CSR";
      USB_DEV1_SRAM: return "DEV1SRAM";
      default:       return "INVALID";
    endcase
  endfunction

  // Central AXI manager timing policy, in AXI clocks. usb_env applies the
  // RREADY/BREADY periods to every manager; usb_axi_apply_delay_policy()
  // applies the VALID gaps to every native and RAL request. READY low periods
  // longer than three clocks can fill a bridge's three-entry R FIFO.
  localparam int unsigned USB_AXI_READY_LOW_MIN = 0;
  localparam int unsigned USB_AXI_READY_LOW_MAX = 8;
  localparam int unsigned USB_AXI_READY_HIGH_MIN = 1;
  localparam int unsigned USB_AXI_READY_HIGH_MAX = 4;
  localparam int unsigned USB_AXI_VALID_GAP_MAX = 2;
  // Every manager may have this many AXI transactions in flight. Sequences
  // that overlap requests rely on it; blocking sequences are unaffected.
  localparam int unsigned USB_AXI_MAX_OUTSTANDING = 10;

  // Randomize one request's VALID gaps. With randomization off, leave any
  // directed delays untouched and draw no random numbers.
  function automatic void usb_axi_apply_delay_policy(aaxi_master_tr transaction, bit randomize_delays);
    if (!randomize_delays) begin
      return;
    end
    transaction.ar_valid_delay = 16'($urandom_range(USB_AXI_VALID_GAP_MAX));
    transaction.aw_valid_delay = 16'($urandom_range(USB_AXI_VALID_GAP_MAX));
    // Positive values delay the first W beat relative to AW.
    transaction.adw_valid_delay = int'($urandom_range(USB_AXI_VALID_GAP_MAX));
    // Index 0 is unused. Fill every beat because callers may raise LEN later.
    foreach (transaction.dw_valid_delay[beat]) begin
      if (beat > 0) begin
        transaction.dw_valid_delay[beat] = 16'($urandom_range(USB_AXI_VALID_GAP_MAX));
      end
    end
  endfunction

  `include "ral/usb_reg_model.svh"
  `include "ral/usb_axi_user_override.svh"
  `include "ral/usb_axi_reg_adapter.svh"
  `include "env/usb_endpoint_cfg.svh"
  `include "env/usb_env_cfg.svh"
  `include "env/usb_vip_cfg_builder.svh"
  `include "env/usb_packet_monitor_callback.svh"
  `include "env/usb_virtual_sequencer.svh"
  `include "env/usb_env.svh"
  `include "sequences/usb_base_seq.svh"
  `include "sequences/usb_axi_read_backpressure_seq.svh"
  `include "sequences/usb_axi_write_backpressure_seq.svh"
  `include "sequences/usb_axi_filter_seq.svh"
  `include "sequences/usb_axi_stress_seq.svh"
  `include "sequences/usb_endpoint_rw_seq.svh"
  `include "sequences/usb_host_base_seq.svh"
  `include "sequences/usb_bulk_out_host_seq.svh"
  `include "sequences/usb_bulk_in_host_seq.svh"
  `include "sequences/usb_iso_host_seq.svh"
  `include "sequences/usb_interrupt_host_seq.svh"
  `include "sequences/usb_init_host_seq.svh"
  `include "sequences/usb_init_seq.svh"
  `include "sequences/usb_unsupported_request_host_seq.svh"
  `include "sequences/usb_unsupported_request_seq.svh"
  `include "sequences/usb_resume_recovery_seq.svh"
  `include "sequences/usb_l2_host_resume_host_seq.svh"
  `include "sequences/usb_l2_host_resume_seq.svh"
  `include "sequences/usb_l1_host_resume_host_seq.svh"
  `include "sequences/usb_l1_host_resume_seq.svh"
  `include "sequences/usb_double_buffer_bulk_seq.svh"
  `include "sequences/usb_high_bandwidth_iso_seq.svh"
  `include "sequences/usb_high_bandwidth_interrupt_seq.svh"
  `include "sequences/usb_bulk_ping_seq.svh"
  `include "sequences/usb_bad_crc5_seq.svh"
  `include "sequences/usb_dev_skip_host_seq.svh"
  `include "sequences/usb_dev_skip_seq.svh"
  `include "sequences/usb_dev_skip_during_rx_seq.svh"
  `include "tests/usb_base_test.svh"
  `include "tests/usb_axi_read_backpressure_test.svh"
  `include "tests/usb_axi_write_backpressure_test.svh"
  `include "tests/usb_axi_filter_test.svh"
  `include "tests/usb_axi_stress_test.svh"
  `include "tests/usb_endpoint_rw_test.svh"
  `include "tests/usb_init_test.svh"
  `include "tests/usb_unsupported_request_test.svh"
  `include "tests/usb_l2_host_resume_test.svh"
  `include "tests/usb_l1_host_resume_test.svh"
  `include "tests/usb_double_buffer_bulk_test.svh"
  `include "tests/usb_high_bandwidth_iso_test.svh"
  `include "tests/usb_high_bandwidth_interrupt_test.svh"
  `include "tests/usb_bulk_ping_test.svh"
  `include "tests/usb_bad_crc5_test.svh"
  `include "tests/usb_dev_skip_test.svh"
  `include "tests/usb_dev_skip_during_rx_test.svh"
  `include "tests/usb_utility_timeout_test.svh"
endpackage
