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

// Read the real recovery capability register with and without R backpressure.
// Four beats exceed the current COMBO bridge's three-entry response FIFO.
// Every beat must return the register's RAL reset value with OKAY.
class usb_axi_read_backpressure_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_read_backpressure_seq)

  localparam int unsigned READ_BEATS = 4;
  localparam int unsigned STALL_CYCLES = 64;
  bit completed;

  function new(string name = "usb_axi_read_backpressure_seq");
    super.new(name);
  endfunction

  // Issue one FIXED read using the VIP's native first-RREADY delay, then
  // check that every beat returned the constant with an OKAY response.
  protected task read_capability(int unsigned stall_cycles);
    aaxi_master_tr transaction;
    logic [31:0] address;
    logic [31:0] expected;
    logic [31:0] actual;

    address = 32'(p_sequencer.reg_model.combo.recovery.PROT_CAP_0.get_address(p_sequencer.reg_model.combo_map));
    expected = 32'(p_sequencer.reg_model.combo.recovery.PROT_CAP_0.get_reset());
    transaction = create_transaction(USB_DEV0_CSR, '0, 1'b0, '0, usb_axi_user_override::with_value('0));
    transaction.addr = address;
    transaction.len = READ_BEATS - 1;
    transaction.burst = AAXI_BURST_FIXED;
    transaction.ar_handshake_rready_delay = 16'(stall_cycles);
    `uvm_info("USB_READ_BACKPRESSURE", $sformatf("Starting %0d-beat FIXED read: address=0x%08h initial RREADY delay=%0d clocks", READ_BEATS, address, stall_cycles), UVM_LOW)
    execute_transaction(USB_DEV0_CSR, address, 1'b0, transaction);

    if (transaction.rresp_Q.size() != READ_BEATS || transaction.data.size() != READ_BEATS * 4) begin
      `uvm_fatal("USB_READ_BACKPRESSURE", $sformatf("Read returned %0d responses and %0d bytes, expected %0d and %0d", transaction.rresp_Q.size(), transaction.data.size(), READ_BEATS, READ_BEATS * 4))
    end
    for (int unsigned beat = 0; beat < READ_BEATS; beat++) begin
      for (int unsigned lane = 0; lane < 4; lane++) begin
        actual[lane * 8 +: 8] = transaction.data[beat * 4 + lane];
      end
      if (transaction.rresp_Q[beat] !== AAXI_RESP_OKAY || actual !== expected) begin
        `uvm_fatal("USB_READ_DATA_LOSS", $sformatf("RREADY delay %0d: beat %0d/%0d address=0x%08h actual=0x%08h expected=0x%08h response=0x%0h (expected OKAY)", stall_cycles, beat + 1, READ_BEATS, address, actual, expected, transaction.rresp_Q[beat]))
      end
    end
    `uvm_info("USB_READ_BACKPRESSURE", $sformatf("Read passed: initial RREADY delay=%0d clocks, %0d beats of 0x%08h", stall_cycles, READ_BEATS, expected), UVM_LOW)
  endtask

  // Establish an unstalled control, then change only response backpressure.
  // The test disables central delay randomization, so RREADY follows VIP
  // defaults except for each read's explicit initial delay.
  task body();
    completed = 1'b0;
    `uvm_info("USB_READ_BACKPRESSURE", "Starting recovery read retention test; no writes or USB enumeration", UVM_LOW)
    read_capability(0);
    read_capability(STALL_CYCLES);
    completed = 1'b1;
    `uvm_info("USB_READ_BACKPRESSURE", "Both reads returned all eight expected beats", UVM_LOW)
  endtask
endclass
