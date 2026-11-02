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

// Fill each bridge's two-entry B FIFO while a third write is pending, then
// check responses and data. A 4-beat stalled read of a COMBO decode hole covers
// the read path's two-cycle ERROR capture under R backpressure.
class usb_axi_write_backpressure_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_write_backpressure_seq)

  localparam int unsigned STALL_CYCLES = 64;
  localparam int unsigned HOLE_READ_BEATS = 4;
  // COMBO bytes 0x040-0x7ff lie between DEV0 CSR and recovery.
  localparam logic [31:0] COMBO_DECODE_HOLE = 32'h0000_0400;
  localparam logic [31:0] SRAM_SCRATCH = 32'h0000_2000;
  // Two AXI clocks between launches fix AW order without serializing writes.
  localparam time LAUNCH_GAP = 5ns;
  bit completed;

  function new(string name = "usb_axi_write_backpressure_seq");
    super.new(name);
  endfunction

  // Build one full-strobe INCR write whose beat N carries first_data + N.
  // The decode hole is outside the checked CSR window, so it skips
  // check_address().
  protected function aaxi_master_tr build_write(usb_target_e target, logic [31:0] offset, int unsigned beats, logic [31:0] first_data, bit decode_hole);
    aaxi_master_tr transaction;
    logic [31:0] beat_data;

    if (!decode_hole) begin
      check_address(target, offset + 32'(4 * (beats - 1)));
    end
    transaction = create_transaction(target, offset, 1'b1, first_data, usb_axi_user_override::with_value('0));
    transaction.len = beats - 1;
    transaction.data.delete();
    transaction.strobes.delete();
    transaction.wuser_A = new[beats];
    for (int unsigned beat = 0; beat < beats; beat++) begin
      beat_data = first_data + 32'(beat);
      for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
        transaction.data.push_back(beat_data[byte_index * 8 +: 8]);
        transaction.strobes.push_back(1'b1);
      end
      transaction.wuser_A[beat] = '0;
    end
    // Hold BREADY low after each BVALID so completed responses occupy B.
    transaction.b_valid_ready_delay = 16'(STALL_CYCLES);
    return transaction;
  endfunction

  // Launch all writes with overlapping lifetimes, wait for every completion,
  // and require the expected B response on each.
  protected task run_concurrent_writes(string label, usb_target_e target, aaxi_master_tr writes[$], aaxi_resp_type expected_resp);
    usb_axi_single_request_seq children[$];

    `uvm_info("USB_WRITE_BACKPRESSURE", $sformatf("%s: launching %0d overlapping writes with BREADY held %0d clocks after each BVALID", label, writes.size(), STALL_CYCLES), UVM_LOW)
    foreach (writes[index]) begin
      children.push_back(usb_axi_single_request_seq::type_id::create($sformatf("%s_write%0d", label, index)));
      children[index].target = target;
      children[index].transaction = writes[index];
    end
    foreach (children[index]) begin
      automatic int unsigned child_index = index;
      fork
        children[child_index].start(p_sequencer, this);
      join_none
      #(LAUNCH_GAP);
    end
    wait fork;
    foreach (writes[index]) begin
      if (writes[index].resp !== expected_resp) begin
        `uvm_fatal("USB_WRITE_BACKPRESSURE", $sformatf("%s write %0d addr=0x%08h response=0x%0h, expected 0x%0h", label, index, writes[index].addr, writes[index].resp, expected_resp))
      end
    end
    `uvm_info("USB_WRITE_BACKPRESSURE", $sformatf("%s: all %0d write responses were 0x%0h", label, writes.size(), expected_resp), UVM_LOW)
  endtask

  // W1: three single-beat SRAM writes; the third meets a full B FIFO.
  protected task run_sram_single_beats();
    aaxi_master_tr writes[$];

    for (int unsigned index = 0; index < 3; index++) begin
      writes.push_back(build_write(USB_DEV0_SRAM, SRAM_SCRATCH + 32'(4 * index), 1, 32'hA5A5_0010 + 32'(index), 1'b0));
    end
    run_concurrent_writes("W1", USB_DEV0_SRAM, writes, AAXI_RESP_OKAY);
    for (int unsigned index = 0; index < 3; index++) begin
      expect32(USB_DEV0_SRAM, SRAM_SCRATCH + 32'(4 * index), 32'hA5A5_0010 + 32'(index));
    end
  endtask

  // W2: the third write is a 4-beat burst. Its earlier beats need no B slot;
  // only its final beat meets the full B FIFO.
  protected task run_sram_final_burst();
    aaxi_master_tr writes[$];

    writes.push_back(build_write(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h20, 1, 32'h5A5A_0020, 1'b0));
    writes.push_back(build_write(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h24, 1, 32'h5A5A_0024, 1'b0));
    writes.push_back(build_write(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h30, 4, 32'h5A5A_0030, 1'b0));
    run_concurrent_writes("W2", USB_DEV0_SRAM, writes, AAXI_RESP_OKAY);
    expect32(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h20, 32'h5A5A_0020);
    expect32(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h24, 32'h5A5A_0024);
    for (int unsigned beat = 0; beat < 4; beat++) begin
      expect32(USB_DEV0_SRAM, SRAM_SCRATCH + 32'h30 + 32'(4 * beat), 32'h5A5A_0030 + 32'(beat));
    end
  endtask

  // W3: decoder ERROR on all three COMBO writes, the third under a full B FIFO.
  protected task run_decode_hole_writes();
    aaxi_master_tr writes[$];

    for (int unsigned index = 0; index < 3; index++) begin
      writes.push_back(build_write(USB_DEV0_CSR, COMBO_DECODE_HOLE, 1, 32'hDEAD_0000 + 32'(index), 1'b1));
    end
    run_concurrent_writes("W3", USB_DEV0_CSR, writes, AAXI_RESP_SLVERR);
  endtask

  // R-ERR: a stalled 4-beat FIXED read of the decode hole fills R before its
  // last beat; every beat must still report SLVERR.
  protected task run_decode_hole_read();
    aaxi_master_tr transaction;

    transaction = create_transaction(USB_DEV0_CSR, COMBO_DECODE_HOLE, 1'b0, '0, usb_axi_user_override::with_value('0));
    transaction.len = HOLE_READ_BEATS - 1;
    transaction.burst = AAXI_BURST_FIXED;
    transaction.ar_handshake_rready_delay = 16'(STALL_CYCLES);
    `uvm_info("USB_WRITE_BACKPRESSURE", $sformatf("R-ERR: %0d-beat FIXED read of decode hole 0x%08h with initial RREADY delay %0d clocks", HOLE_READ_BEATS, transaction.addr, STALL_CYCLES), UVM_LOW)
    execute_transaction(USB_DEV0_CSR, 32'(transaction.addr), 1'b0, transaction);
    if (transaction.rresp_Q.size() != HOLE_READ_BEATS) begin
      `uvm_fatal("USB_WRITE_BACKPRESSURE", $sformatf("R-ERR returned %0d responses, expected %0d", transaction.rresp_Q.size(), HOLE_READ_BEATS))
    end
    foreach (transaction.rresp_Q[beat]) begin
      if (transaction.rresp_Q[beat] !== AAXI_RESP_SLVERR) begin
        `uvm_fatal("USB_WRITE_BACKPRESSURE", $sformatf("R-ERR beat %0d response=0x%0h, expected SLVERR", beat, transaction.rresp_Q[beat]))
      end
    end
    `uvm_info("USB_WRITE_BACKPRESSURE", "R-ERR: all read beats reported SLVERR", UVM_LOW)
  endtask

  task body();
    completed = 1'b0;
    run_sram_single_beats();
    run_sram_final_burst();
    run_decode_hole_writes();
    run_decode_hole_read();
    completed = 1'b1;
    `uvm_info("USB_WRITE_BACKPRESSURE", "W1, W2, W3, and R-ERR completed with the expected responses and data", UVM_LOW)
  endtask
endclass
