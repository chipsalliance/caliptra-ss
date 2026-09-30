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
  // usb_top_tb checks this against the Avery interface ID width, which
  // includes its default interconnect ID padding.
  localparam int USB_TB_AXI_ID_WIDTH = `CALIPTRA_AXI_ID_WIDTH;
  localparam time USB_RESET_TIMEOUT = 5us;
  localparam time USB_TRANSFER_TIMEOUT = 10us;
  localparam time USB_TEST_TIMEOUT = 1ms;
  localparam time USB_INIT_TEST_TIMEOUT = 2ms;

  typedef enum int {
    USB_HUB,
    USB_DEV0_CSR,
    USB_DEV0_SRAM,
    USB_DEV1_CSR,
    USB_DEV1_SRAM
  } usb_target_e;

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
  `include "env/usb_env_cfg.svh"
  `include "env/usb_virtual_sequencer.svh"
  `include "env/usb_env.svh"
  `include "sequences/usb_base_seq.svh"
  `include "sequences/usb_axi_read_backpressure_seq.svh"
  `include "sequences/usb_axi_write_backpressure_seq.svh"
  `include "sequences/usb_axi_filter_seq.svh"
  `include "sequences/usb_axi_stress_seq.svh"
  `include "sequences/usb_endpoint_rw_seq.svh"
  `include "sequences/usb_init_host_seq.svh"
  `include "sequences/usb_init_seq.svh"
  `include "tests/usb_base_test.svh"
  `include "tests/usb_axi_read_backpressure_test.svh"
  `include "tests/usb_axi_write_backpressure_test.svh"
  `include "tests/usb_axi_filter_test.svh"
  `include "tests/usb_axi_stress_test.svh"
  `include "tests/usb_endpoint_rw_test.svh"
  `include "tests/usb_init_test.svh"
endpackage
