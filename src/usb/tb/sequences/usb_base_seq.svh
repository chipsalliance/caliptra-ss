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
// Shared base for every device-side USB sequence. It provides the generic
// mechanics so a scenario sequence expresses only what it is proving. The
// class body is split by function into included files:
//
//   - usb_base_seq_access.svh: native 32-bit AXI transfers, COMBO register
//     accesses through RAL, 64-bit packet-memory rows, and RAL field geometry.
//   - usb_base_seq_endpoint.svh: DEV0 endpoint-list entry encode/decode,
//     endpoint-configuration-driven entry addressing, per-endpoint
//     INTEN/INTSTAT/EPSKIP control, and bounded CSR polling.
//
// Scenarios extend this class directly. A scenario that needs another one as a
// precondition (for example enumeration) starts it as a child sequence rather
// than inheriting from it.
class usb_base_seq extends uvm_sequence;
  `uvm_object_utils(usb_base_seq)
  `uvm_declare_p_sequencer(usb_virtual_sequencer)

  localparam logic [31:0] HUB_BASE_ADDR = 32'(usb_compound_pkg::HUB_BASE_ADDR);

  // Default pacing for bounded CSR polls. A caller that needs a different
  // bound passes its own values rather than changing these.
  localparam time EP_POLL_INTERVAL = 100ns;
  localparam time EP_PROGRESS_REPORT_INTERVAL = 20us;

  usb_target_stats_t target_stats[USB_TARGET_COUNT];
  int unsigned ral_memory_writes[USB_TARGET_COUNT];
  int unsigned ral_memory_reads[USB_TARGET_COUNT];

  // Create a sequence with cleared native-access and RAL-memory counters.
  function new(string name = "usb_base_seq");
    super.new(name);
    initialize_target_stats();
  endfunction

  // Fail before sequence traffic starts if the virtual sequencer lacks the
  // register model or any required Avery manager, even for an unused target.
  virtual task pre_start();
    super.pre_start();
    if (p_sequencer == null ||
        p_sequencer.reg_model == null ||
        p_sequencer.cfg == null ||
        p_sequencer.combo_sequencer == null ||
        p_sequencer.dev0_memory_sequencer == null ||
        p_sequencer.dev1_csr_sequencer == null ||
        p_sequencer.dev1_memory_sequencer == null) begin
      `uvm_fatal("USB_SEQ", "USB virtual sequencer is missing required RAL, configuration, or Avery handles")
    end
  endtask

  // Bench-wide bound for one native or RAL access, from usb_env_cfg.
  function time transfer_timeout();
    return p_sequencer.cfg.transfer_timeout;
  endfunction

  // DEV0 endpoint list base in packet memory, from usb_env_cfg;
  // usb_init_seq programs EPLISTSTART to match.
  function logic [31:0] endpoint_list_base();
    return p_sequencer.cfg.endpoint_list_base;
  endfunction

  // Clear accumulated per-target traffic and comparison counts without
  // changing the DUT, register model, or sequencer configuration.
  function void initialize_target_stats();
    foreach (target_stats[target_index]) begin
      target_stats[target_index] = '{default: 0};
      ral_memory_writes[target_index] = 0;
      ral_memory_reads[target_index] = 0;
    end
  endfunction

  `include "sequences/usb_base_seq_access.svh"
  `include "sequences/usb_base_seq_endpoint.svh"
endclass
