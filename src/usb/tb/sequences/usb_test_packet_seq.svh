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

// Enters TEST_PACKET mode and verifies the complete UTMI byte stream.
class usb_test_packet_seq extends usb_base_seq;
  `uvm_object_utils(usb_test_packet_seq)

  localparam int unsigned TEST_PACKET_BYTES = 56;
  localparam logic [2:0] TEST_PACKET_MODE = 3'b100;

  bit completed;
  time packet_timeout = 100us;

  function new(string name = "usb_test_packet_seq");
    super.new(name);
  endfunction

  // Return one byte from the USB 2.0 high-speed test packet pattern.
  function byte unsigned expected_byte(int unsigned index);
    if (index == 0) return 8'hc3;
    if (index inside {[1:9]}) return 8'h00;
    if (index inside {[10:17]}) return 8'haa;
    if (index inside {[18:25]}) return 8'hee;
    if (index == 26) return 8'hfe;
    if (index inside {[27:37]}) return 8'hff;
    case (index)
      38: return 8'h7f;
      39: return 8'hbf;
      40: return 8'hdf;
      41: return 8'hef;
      42: return 8'hf7;
      43: return 8'hfb;
      44: return 8'hfd;
      45: return 8'hfc;
      46: return 8'h7e;
      47: return 8'hbf;
      48: return 8'hdf;
      49: return 8'hef;
      50: return 8'hf7;
      51: return 8'hfb;
      52: return 8'hfd;
      53: return 8'h7e;
      54: return 8'hb6;
      55: return 8'hce;
      default: return 8'h00;
    endcase
  endfunction

  // Validate packet size and every passively observed byte, including CRC16.
  function void check_test_packet(usb_utmi_tx_packet packet);
    if (packet == null) begin
      `uvm_fatal("USB_TEST_PACKET", "Observed UTMI packet is null")
      return;
    end
    if (packet.bytes.size() != TEST_PACKET_BYTES) begin
      `uvm_fatal(
        "USB_TEST_PACKET",
        $sformatf("Test packet contains %0d bytes, expected %0d", packet.bytes.size(), TEST_PACKET_BYTES)
      )
      return;
    end
    foreach (packet.bytes[index]) begin
      if (packet.bytes[index] !== expected_byte(index)) begin
        `uvm_fatal(
          "USB_TEST_PACKET",
          $sformatf("Test packet byte %0d is 0x%02h, expected 0x%02h", index, packet.bytes[index], expected_byte(index))
        )
      end
    end
    `uvm_info("USB_TEST_PACKET", $sformatf("Verified all %0d test-packet bytes including CRC16", packet.bytes.size()), UVM_LOW)
  endfunction

  // Enumerate, select TEST_PACKET, and consume one passive UTMI observation.
  virtual task body();
    usb_init_seq init_sequence;
    uvm_event tx_packet_event;
    uvm_object observed_object;
    usb_utmi_tx_packet observed_packet;
    logic [31:0] command;
    logic [31:0] test_mode_mask;
    logic [31:0] test_mode_value;
    bit packet_seen;
    bit packet_wait_expired;

    completed = 1'b0;
    `uvm_info("USB_TEST_PACKET", "Starting TEST_PACKET scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_TEST_PACKET", "Enumeration did not complete")
    end

    if (p_sequencer.ctrl_vif == null) begin
      `uvm_fatal("USB_TEST_PACKET", "TEST_PACKET requires the USB control interface")
    end
    tx_packet_event = uvm_event_pool::get_global(USB_UTMI_TX_PACKET_EVENT);
    tx_packet_event.reset();
    test_mode_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE);
    test_mode_value = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.PHY_TEST_MODE, TEST_PACKET_MODE);
    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    command = (command & ~test_mode_mask) | test_mode_value;

    packet_seen = 1'b0;
    packet_wait_expired = 1'b0;
    `uvm_info("USB_TEST_PACKET", $sformatf("Selecting PHY_TEST_MODE=%0d and waiting up to %0t for the test packet", TEST_PACKET_MODE, packet_timeout), UVM_LOW)
    fork
      begin
        tx_packet_event.wait_trigger_data(observed_object);
        packet_seen = 1'b1;
      end
      begin
        #(packet_timeout);
        packet_wait_expired = 1'b1;
      end
    join_none
    ral_write32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    wait (packet_seen || packet_wait_expired);
    disable fork;
    if (!packet_seen) begin
      `uvm_fatal("USB_TEST_PACKET", $sformatf("No DUT UTMI packet was observed within %0t", packet_timeout))
    end
    if (!$cast(observed_packet, observed_object)) begin
      `uvm_fatal("USB_TEST_PACKET", "UTMI packet event carried an unexpected object type")
    end

    ral_read32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, command);
    if ((command & test_mode_mask) !== test_mode_value) begin
      `uvm_fatal("USB_TEST_PACKET", $sformatf("PHY_TEST_MODE readback is 0x%08h, expected field value 0x%08h", command, test_mode_value))
    end
    check_test_packet(observed_packet);
    completed = 1'b1;
    `uvm_info("USB_TEST_PACKET", "TEST_PACKET mode entered and packet contents verified", UVM_LOW)
  endtask
endclass
