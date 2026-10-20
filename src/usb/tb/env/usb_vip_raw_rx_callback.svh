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

// Synopsys USB VIP UVM Class Reference:
// Paths are relative to doc/class_ref/usb_svt_uvm_class_reference/html/.
// callback/class_svt_usb_protocol_callback.html,
// post_usb_20_packet_in_port_get(): after link input, before protocol processing.
// Setting its ref drop argument discards the descriptor without further action.
// Register on host_agent.prot. Arm expect_data() before stimulus, then call
// wait_for_observation() with a timeout. By default normal VIP routing is kept.
// Only raw ISO IN / TEST_PACKET sequences opt into dropping: no VIP protocol
// transfer owns their response, so those sequences check the PHY snapshot.
// Dropping bypasses protocol handling/checks for that one matching packet;
// it does not remove the PHY/link observation. One sequence owns the expectation.
// Do not enable dropping for ordinary transfers or to suppress VIP errors.
class usb_vip_raw_rx_callback extends svt_usb_protocol_callback;
  `uvm_object_utils(usb_vip_raw_rx_callback)

  protected bit expectation_active;
  protected svt_usb_packet::pid_name_enum expected_pid;
  protected int unsigned expected_payload_bytes;
  protected bit drop_expected_from_protocol;
  protected uvm_event packet_observed;

  function new(string name = "usb_vip_raw_rx_callback");
    super.new(name);
    packet_observed = new("packet_observed");
  endfunction

  function void expect_data(
    svt_usb_packet::pid_name_enum pid,
    int unsigned payload_bytes,
    bit drop_from_protocol = 1'b0
  );
    if (expectation_active) begin
      `uvm_fatal("USB_VIP_RAW_RX", "Previous raw DATA expectation is still pending")
    end
    expected_pid = pid;
    expected_payload_bytes = payload_bytes;
    drop_expected_from_protocol = drop_from_protocol;
    packet_observed.reset();
    expectation_active = 1'b1;
  endfunction

  task wait_for_observation(time timeout);
    bit observed;

    observed = 1'b0;
    fork
      begin
        fork
          begin
            packet_observed.wait_on();
            observed = 1'b1;
          end
          begin
            #(timeout);
          end
        join_any
        disable fork;
      end
    join
    if (!observed) begin
      `uvm_fatal("USB_VIP_RAW_RX", $sformatf("Expected raw %s was not observed within %0t", expected_pid.name(), timeout))
    end
  endtask

  virtual function void post_usb_20_packet_in_port_get(
    svt_usb_protocol component,
    int chan_id,
    svt_usb_packet packet,
    ref bit drop
  );
    if (!expectation_active || packet == null) return;
    if (packet.pid_type != svt_usb_packet::DATA ||
        packet.pid_name != expected_pid ||
        packet.get_payload_byte_count() != expected_payload_bytes) begin
      `uvm_error(
        "USB_VIP_RAW_RX",
        $sformatf("Raw packet is %s/%0d bytes, expected %s/%0d bytes",
                  packet.pid_name.name(), packet.get_payload_byte_count(),
                  expected_pid.name(), expected_payload_bytes)
      )
      return;
    end
    // Preserve the incoming drop value unless the sequence explicitly owns
    // protocol bypass for this response; do not undo another VIP callback.
    if (drop_expected_from_protocol) drop = 1'b1;
    expectation_active = 1'b0;
    packet_observed.trigger(packet);
  endfunction
endclass
