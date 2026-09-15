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
// Check register and packet-memory access across all five standalone USB AXI
// targets while USB protocol traffic is disabled; this is not a USB packet test.
// The sequence follows this ordered flow:
//
//   1. Read and save the disabled device/HUB state that must be restored.
//   2. Exercise DEV0 CSR, HUB storage, both packet SRAMs, and DEV1 CSR through
//      native single-beat Avery transactions.
//   3. Re-read selected locations on every target to detect cross-device aliasing
//      and corruption of adjacent 32-bit halves of 64-bit SRAM rows.
//   4. Restore the saved CSR/HUB state and check exact native access totals.
//   5. Cross-check both packet SRAMs in both directions through RAL and native
//      accesses, then check the additional per-target totals.
//
// usb_base_seq supplies checked native and RAL accesses. Only the saved route
// fields and HUB descriptor words are restored; SRAM test locations retain
// the written patterns. Completion is published only after readback, isolation,
// restoration, and accounting checks pass, with Avery protocol monitors active.
class usb_endpoint_rw_seq extends usb_base_seq;
  `uvm_object_utils(usb_endpoint_rw_seq)

  // Fixed locations cover the first words, adjacent halves, and final SRAM row.
  localparam int unsigned SRAM_LOCATION_COUNT = 5;
  localparam logic [31:0] HUB_CONTROL_ADDR = HUB_BASE_ADDR + 32'h3c;
  localparam logic [31:0] DEVICE_ROUTE_ADDR = 32'h2c;
  localparam logic [31:0] DEV0_ROUTE_MASK = USB_DEV0_ROUTE_MASK;
  localparam logic [31:0] DEV1_ROUTE_MASK = USB_DEV1_ROUTE_MASK;
  localparam int unsigned RAL_MEMORY_LOCATION_COUNT = 4;

  // Native and RAL counters form the final completion contract.
  bit completed;
  int unsigned ral_memory_comparisons[USB_TARGET_COUNT];

  logic [63:0] dev0_ral_pattern_a[RAL_MEMORY_LOCATION_COUNT] = '{
    64'h0123_4567_89ab_cdef,
    64'h1357_9bdf_2468_ace0,
    64'h55aa_0ff0_c33c_9669,
    64'hfedc_ba98_7654_3210
  };
  logic [63:0] dev1_ral_pattern_a[RAL_MEMORY_LOCATION_COUNT] = '{
    64'h89ab_cdef_0123_4567,
    64'h2468_ace0_1357_9bdf,
    64'h9669_c33c_0ff0_55aa,
    64'h7654_3210_fedc_ba98
  };
  logic [63:0] dev0_ral_pattern_b[RAL_MEMORY_LOCATION_COUNT] = '{
    64'ha55a_3cc3_5aa5_c33c,
    64'h0f0f_f0f0_9696_6969,
    64'h1122_3344_5566_7788,
    64'hdead_beef_cafe_f00d
  };
  logic [63:0] dev1_ral_pattern_b[RAL_MEMORY_LOCATION_COUNT] = '{
    64'h5aa5_c33c_a55a_3cc3,
    64'h9696_6969_0f0f_f0f0,
    64'h8877_6655_4433_2211,
    64'hcafe_f00d_dead_beef
  };

  logic [31:0] dev0_sram_data[SRAM_LOCATION_COUNT] = '{
    32'h1357_9bdf,
    32'h2468_ace1,
    32'h1029_3847,
    32'h89ab_cdef,
    32'hfedc_ba98
  };
  logic [31:0] dev1_sram_data[SRAM_LOCATION_COUNT] = '{
    32'he3b6_491c,
    32'hd489_7e22,
    32'he0c8_ea84,
    32'h794a_1f2c,
    32'h0e3d_685b
  };

  // Construct the sequence and let usb_base_seq initialize its access counters.
  // No DUT traffic runs here; body() resets run accounting and executes the test.
  function new(string name = "usb_endpoint_rw_seq");
    super.new(name);
  endfunction

  // Translate a native-test slot (0..4) to a target-local byte offset: the first
  // three words or either half of the final SRAM row. Derive end locations from
  // the selected SRAM's configured size; an unsupported slot is fatal.
  function logic [31:0] sram_offset(usb_target_e target, int unsigned location_index);
    case (location_index)
      0: return 32'h000;
      1: return 32'h004;
      2: return 32'h008;
      3: return sram_implemented_bytes(target) - 8;
      4: return sram_implemented_bytes(target) - 4;
      default: begin
        `uvm_fatal("USB_SEQ", "Invalid SRAM location index")
        return '0;
      end
    endcase
  endfunction

  // Translate a RAL-test slot (0..3) to a 64-bit memory-row index, not a byte
  // offset. Select rows 0, 1, midpoint, and last using the target's configured
  // depth so both memories get boundary coverage. An unsupported slot is fatal.
  function int unsigned ral_memory_index(usb_target_e target, int unsigned location_index);
    int unsigned row_count;

    row_count = sram_implemented_bytes(target) / 8;
    case (location_index)
      0: return 0;
      1: return 1;
      2: return row_count / 2;
      3: return row_count - 1;
      default: begin
        `uvm_fatal("USB_SEQ", "Invalid RAL memory location index")
        return 0;
      end
    endcase
  endfunction

  // Read the selected 64-bit row through RAL and require an exact match to
  // expected_data, failing on mismatch. The base helper counts the RAL read;
  // this task separately counts a passing comparison without native counters.
  task expect_ral_memory(usb_target_e target, int unsigned index, logic [63:0] expected_data);
    logic [63:0] actual_data;

    ral_memory_read(target, index, actual_data);
    if (actual_data !== expected_data) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL index %0d expected 0x%016h, got 0x%016h", usb_target_name(target), index, expected_data, actual_data))
    end
    ral_memory_comparisons[target]++;
  endtask

  // Cross-check row addressing, word order, and device isolation at the four
  // selected rows in each SRAM. Write distinct pattern A rows through RAL and
  // compare both halves natively, then write pattern B halves natively and
  // compare complete rows through RAL. Native offsets are row * 8 and row * 8 + 4.
  // Leave pattern B in memory and accumulate counts for the completion check.
  task exercise_ral_memory_paths();
    logic [31:0] low_address;

    `uvm_info("USB_RAL_MEMORY", "Starting bidirectional RAL/native checks on both packet memories", UVM_LOW)
    for (int unsigned location = 0; location < RAL_MEMORY_LOCATION_COUNT; location++) begin
      ral_memory_write(USB_DEV0_SRAM, ral_memory_index(USB_DEV0_SRAM, location), dev0_ral_pattern_a[location]);
      ral_memory_write(USB_DEV1_SRAM, ral_memory_index(USB_DEV1_SRAM, location), dev1_ral_pattern_a[location]);
    end

    for (int unsigned location = 0; location < RAL_MEMORY_LOCATION_COUNT; location++) begin
      low_address = ral_memory_index(USB_DEV0_SRAM, location) * 8;
      expect32(USB_DEV0_SRAM, low_address, dev0_ral_pattern_a[location][31:0]);
      expect32(USB_DEV0_SRAM, low_address + 4, dev0_ral_pattern_a[location][63:32]);
      low_address = ral_memory_index(USB_DEV1_SRAM, location) * 8;
      expect32(USB_DEV1_SRAM, low_address, dev1_ral_pattern_a[location][31:0]);
      expect32(USB_DEV1_SRAM, low_address + 4, dev1_ral_pattern_a[location][63:32]);
    end

    for (int unsigned location = 0; location < RAL_MEMORY_LOCATION_COUNT; location++) begin
      low_address = ral_memory_index(USB_DEV0_SRAM, location) * 8;
      write32(USB_DEV0_SRAM, low_address, dev0_ral_pattern_b[location][31:0]);
      write32(USB_DEV0_SRAM, low_address + 4, dev0_ral_pattern_b[location][63:32]);
      low_address = ral_memory_index(USB_DEV1_SRAM, location) * 8;
      write32(USB_DEV1_SRAM, low_address, dev1_ral_pattern_b[location][31:0]);
      write32(USB_DEV1_SRAM, low_address + 4, dev1_ral_pattern_b[location][63:32]);
    end

    for (int unsigned location = 0; location < RAL_MEMORY_LOCATION_COUNT; location++) begin
      expect_ral_memory(USB_DEV0_SRAM, ral_memory_index(USB_DEV0_SRAM, location), dev0_ral_pattern_b[location]);
      expect_ral_memory(USB_DEV1_SRAM, ral_memory_index(USB_DEV1_SRAM, location), dev1_ral_pattern_b[location]);
    end
  endtask

  // Require one RAL write/read/comparison and two explicit native word
  // writes/reads/comparisons per selected row on this SRAM. RAL totals are
  // absolute; native totals are deltas from the supplied smoke-test baseline.
  // RAL-generated bus transfers are not native counter increments. Fail on any
  // count mismatch; otherwise log the totals without changing completed.
  function void verify_ral_memory_complete(usb_target_e target, usb_target_stats_t baseline);
    if (ral_memory_writes[target] != RAL_MEMORY_LOCATION_COUNT ||
        ral_memory_reads[target] != RAL_MEMORY_LOCATION_COUNT ||
        ral_memory_comparisons[target] != RAL_MEMORY_LOCATION_COUNT ||
        target_stats[target].writes - baseline.writes != RAL_MEMORY_LOCATION_COUNT * 2 ||
        target_stats[target].reads - baseline.reads != RAL_MEMORY_LOCATION_COUNT * 2 ||
        target_stats[target].comparisons - baseline.comparisons != RAL_MEMORY_LOCATION_COUNT * 2) begin
      `uvm_fatal(
        "USB_RAL_COUNTS",
        $sformatf(
          "%s incomplete: RAL w/r/c=%0d/%0d/%0d native delta w/r/c=%0d/%0d/%0d",
          usb_target_name(target),
          ral_memory_writes[target],
          ral_memory_reads[target],
          ral_memory_comparisons[target],
          target_stats[target].writes - baseline.writes,
          target_stats[target].reads - baseline.reads,
          target_stats[target].comparisons - baseline.comparisons
        )
      )
    end
    `uvm_info(
      "USB_RAL_TARGET_DONE",
      $sformatf(
        "%s RAL w/r/c=%0d/%0d/%0d native delta w/r/c=%0d/%0d/%0d",
        usb_target_name(target),
        ral_memory_writes[target],
        ral_memory_reads[target],
        ral_memory_comparisons[target],
        target_stats[target].writes - baseline.writes,
        target_stats[target].reads - baseline.reads,
        target_stats[target].comparisons - baseline.comparisons
      ),
      UVM_LOW
    )
  endfunction

  // Check masked reset/disabled-state bits at CSR offsets 0x00 and 0x24 and the
  // configured endpoint count at 0x30, then save the route word for restoration.
  // route_mask selects the bits checked at 0x24. This verifies initial state;
  // it does not reset or disable the controller, and all accesses count natively.
  task check_device_reset_state(usb_target_e target, logic [31:0] route_mask, logic [4:0] endpoint_count, output logic [31:0] saved_route);
    expect32(target, 32'h00, '0, 32'h0001_0080);
    expect32(target, 32'h24, '0, route_mask);
    expect32(target, 32'h30, endpoint_count, 32'h1f);
    read32(target, DEVICE_ROUTE_ADDR, saved_route);
  endtask

  // Enforce the disabled-state precondition for both devices and the HUB, using
  // each device's configured route mask and endpoint count. Save both route
  // words and HUB descriptor words 2 and 3 before destructive writes.
  // Packet SRAM contents are deliberately not captured or restored.
  task capture_initial_state(output logic [31:0] saved_dev0_route, output logic [31:0] saved_dev1_route, output logic [31:0] saved_hub_word2, output logic [31:0] saved_hub_word3);
    check_device_reset_state(USB_DEV0_CSR, DEV0_ROUTE_MASK, 5'(USB_DEV0_NBPHYSEP), saved_dev0_route);
    check_device_reset_state(USB_DEV1_CSR, DEV1_ROUTE_MASK, 5'(USB_DEV1_NBPHYSEP), saved_dev1_route);
    expect32(USB_HUB, HUB_CONTROL_ADDR, '0, 32'h0001_0001);
    read32(USB_HUB, HUB_BASE_ADDR + 32'h08, saved_hub_word2);
    read32(USB_HUB, HUB_BASE_ADDR + 32'h0c, saved_hub_word3);
    `uvm_info("USB_SEQ", "Disabled device and HUB state confirmed", UVM_LOW)
  endtask

  // Exercise DEV0 routing through the shared COMBO manager using two native
  // write/readback patterns, comparing only DEV0_ROUTE_MASK bits. Leave the
  // second pattern installed for the later cross-target isolation check.
  task exercise_dev0_csr();
    write32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, 32'h4000_a55a);
    expect32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, 32'h4000_a55a, DEV0_ROUTE_MASK);
    write32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, 32'h8000_5aa5);
    expect32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, 32'h8000_5aa5, DEV0_ROUTE_MASK);
  endtask

  // Verify that HUB descriptor words 2 and 3 independently retain native writes:
  // seed both, overwrite word 2, and confirm word 3 is unchanged. Assume
  // capture_initial_state() already checked HUB enable and DCON are clear;
  // this task does not modify control bits or restore the descriptor words.
  task exercise_hub_storage();
    `uvm_info("USB_HUB", "Testing descriptor words 2 and 3 while HUB enable and DCON are clear", UVM_LOW)
    write32(USB_HUB, HUB_BASE_ADDR + 32'h08, 32'h96a5_3cc3);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h08, 32'h96a5_3cc3);
    write32(USB_HUB, HUB_BASE_ADDR + 32'h0c, 32'h5ac3_6996);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h0c, 32'h5ac3_6996);
    write32(USB_HUB, HUB_BASE_ADDR + 32'h08, 32'hc35a_a569);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h08, 32'hc35a_a569);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h0c, 32'h5ac3_6996);
  endtask

  // Exercise DEV1 routing through its dedicated manager using two native
  // write/readback patterns, comparing only DEV1_ROUTE_MASK bits. Leave the
  // second pattern installed for the later cross-target isolation check.
  task exercise_dev1_csr();
    write32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, 32'h8000_2569);
    expect32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, 32'h8000_2569, DEV1_ROUTE_MASK);
    write32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, 32'h4000_1a96);
    expect32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, 32'h4000_1a96, DEV1_ROUTE_MASK);
  endtask

  // Check native word addressing at the first three words and both halves of
  // the final SRAM row, including preservation of a previously written neighbor.
  // Then modify each half of the first row and verify the other half is intact.
  // Update expected_data[0] and [1] in place for later isolation checks; neither
  // the modified patterns nor the original SRAM contents are restored here.
  task exercise_sram(usb_target_e target, ref logic [31:0] expected_data[SRAM_LOCATION_COUNT]);
    `uvm_info("USB_SRAM", $sformatf("Starting %s first, adjacent, and final-row half checks", usb_target_name(target)), UVM_LOW)
    for (int unsigned location_index = 0; location_index < SRAM_LOCATION_COUNT; location_index++) begin
      write32(target, sram_offset(target, location_index), expected_data[location_index]);
      expect32(target, sram_offset(target, location_index), expected_data[location_index]);
      if (location_index == 1) begin
        expect32(target, sram_offset(target, 0), expected_data[0]);
      end
      if (location_index == 4) begin
        expect32(target, sram_offset(target, 3), expected_data[3]);
      end
    end

    expected_data[0] ^= 32'h55aa_0ff0;
    write32(target, sram_offset(target, 0), expected_data[0]);
    expect32(target, sram_offset(target, 0), expected_data[0]);
    expect32(target, sram_offset(target, 1), expected_data[1]);

    expected_data[1] ^= 32'haa55_f00f;
    write32(target, sram_offset(target, 1), expected_data[1]);
    expect32(target, sram_offset(target, 1), expected_data[1]);
    expect32(target, sram_offset(target, 0), expected_data[0]);
    `uvm_info("USB_SRAM", $sformatf("Completed %s half-preservation and final-address checks", usb_target_name(target)), UVM_LOW)
  endtask

  // After all native target exercises, re-read the retained route/HUB patterns
  // and sampled SRAM words to detect corruption caused by writes to other
  // targets or locations. Requires the exercise tasks' final patterns, including
  // their updated SRAM expectation arrays; run before restoration or RAL writes.
  task check_cross_target_independence();
    expect32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, 32'h8000_5aa5, DEV0_ROUTE_MASK);
    expect32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, 32'h4000_1a96, DEV1_ROUTE_MASK);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h08, 32'hc35a_a569);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h0c, 32'h5ac3_6996);

    for (int unsigned location_index = 0; location_index < SRAM_LOCATION_COUNT; location_index++) begin
      expect32(USB_DEV0_SRAM, sram_offset(USB_DEV0_SRAM, location_index), dev0_sram_data[location_index]);
      expect32(USB_DEV1_SRAM, sram_offset(USB_DEV1_SRAM, location_index), dev1_sram_data[location_index]);
    end
  endtask

  // Restore the captured route bits selected by each device's mask and both
  // complete HUB descriptor words, then verify native readback. Route writes
  // clear bits outside the mask and comparisons ignore them. SRAM patterns are
  // left intact; restoration accesses contribute to native completion totals.
  task restore_initial_state(logic [31:0] saved_dev0_route, logic [31:0] saved_dev1_route, logic [31:0] saved_hub_word2, logic [31:0] saved_hub_word3);
    write32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, saved_dev0_route & DEV0_ROUTE_MASK);
    expect32(USB_DEV0_CSR, DEVICE_ROUTE_ADDR, saved_dev0_route, DEV0_ROUTE_MASK);
    write32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, saved_dev1_route & DEV1_ROUTE_MASK);
    expect32(USB_DEV1_CSR, DEVICE_ROUTE_ADDR, saved_dev1_route, DEV1_ROUTE_MASK);
    write32(USB_HUB, HUB_BASE_ADDR + 32'h08, saved_hub_word2);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h08, saved_hub_word2);
    write32(USB_HUB, HUB_BASE_ADDR + 32'h0c, saved_hub_word3);
    expect32(USB_HUB, HUB_BASE_ADDR + 32'h0c, saved_hub_word3);
  endtask

  // Require a target's accumulated native writes, reads, and passing comparisons
  // to equal the caller's expected totals, detecting skipped or extra accesses.
  // Fail on mismatch or log success; do not reset counters or set completed.
  function void verify_target_complete(usb_target_e target, int unsigned expected_writes, int unsigned expected_reads, int unsigned expected_comparisons);
    usb_target_stats_t stats;

    stats = target_stats[target];
    if (stats.writes != expected_writes ||
        stats.reads != expected_reads ||
        stats.comparisons != expected_comparisons) begin
      `uvm_fatal(
        "USB_COUNTS",
        $sformatf(
          "%s incomplete: writes=%0d/%0d reads=%0d/%0d comparisons=%0d/%0d",
          usb_target_name(target),
          stats.writes,
          expected_writes,
          stats.reads,
          expected_reads,
          stats.comparisons,
          expected_comparisons
        )
      )
    end
    `uvm_info("USB_TARGET_DONE", $sformatf("%s writes=%0d reads=%0d comparisons=%0d", usb_target_name(target), stats.writes, stats.reads, stats.comparisons), UVM_LOW)
  endfunction

  // Run the full disabled-controller smoke test, clearing completed and all
  // access/comparison counters first. Capture state, exercise all native targets,
  // check isolation, restore saved route/HUB fields, and require exact totals.
  // Use the resulting SRAM counts as baselines for bidirectional RAL/native
  // checks; set completed only after both SRAM completion contracts pass.
  // SRAM test contents remain overwritten, and fatal failures can stop the
  // sequence before restoration; this is not an unconditional cleanup path.
  task body();
    logic [31:0] saved_dev0_route;
    logic [31:0] saved_dev1_route;
    logic [31:0] saved_hub_word2;
    logic [31:0] saved_hub_word3;
    usb_target_stats_t dev0_sram_baseline;
    usb_target_stats_t dev1_sram_baseline;

    completed = 1'b0;
    initialize_target_stats();
    foreach (ral_memory_comparisons[target_index]) begin
      ral_memory_comparisons[target_index] = 0;
    end
    `uvm_info("USB_SEQ", "Starting five-target aligned single-beat AXI smoke", UVM_LOW)

    // Preserve reset state before the native target exercise mutates it.
    capture_initial_state(saved_dev0_route, saved_dev1_route, saved_hub_word2, saved_hub_word3);

    // Exercise each functional target through its native Avery manager.
    exercise_dev0_csr();
    exercise_hub_storage();
    exercise_sram(USB_DEV0_SRAM, dev0_sram_data);
    exercise_dev1_csr();
    exercise_sram(USB_DEV1_SRAM, dev1_sram_data);

    `uvm_info("USB_SEQ", "Rechecking all functional targets after cross-device writes", UVM_LOW)
    check_cross_target_independence();
    restore_initial_state(saved_dev0_route, saved_dev1_route, saved_hub_word2, saved_hub_word3);

    // Exact totals prove that every intended native operation completed.
    verify_target_complete(USB_HUB, 5, 11, 9);
    verify_target_complete(USB_DEV0_CSR, 3, 8, 7);
    verify_target_complete(USB_DEV0_SRAM, 7, 16, 16);
    verify_target_complete(USB_DEV1_CSR, 3, 8, 7);
    verify_target_complete(USB_DEV1_SRAM, 7, 16, 16);

    // Cross the abstraction boundary in both directions without folding the
    // earlier native counts into the RAL-specific completion contract.
    dev0_sram_baseline = target_stats[USB_DEV0_SRAM];
    dev1_sram_baseline = target_stats[USB_DEV1_SRAM];
    exercise_ral_memory_paths();
    verify_ral_memory_complete(USB_DEV0_SRAM, dev0_sram_baseline);
    verify_ral_memory_complete(USB_DEV1_SRAM, dev1_sram_baseline);

    completed = 1'b1;
    `uvm_info("USB_SEQ", "Native target checks and bidirectional packet-memory RAL checks passed", UVM_LOW)
  endtask
endclass
