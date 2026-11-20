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

// One bounded, independently routed native EPN transfer. Unlike the generic
// single-transfer watch, this does not consume the first broadcast completion.
class usb_ocp_base_epn_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_ocp_base_epn_host_seq)
  usb_endpoint_cfg endpoint;
  usb_ocp_base_env_cfg ocp_cfg;
  usb_ocp_observer observer;
  logic [6:0] address;
  int unsigned device = 1;
  int unsigned phase;
  int unsigned data_tag;
  int unsigned payload_length = 0;
  int unsigned scheduled_microframe;

  function new(string name = "usb_ocp_base_epn_host_seq");
    super.new(name);
  endfunction

  task body();
    svt_usb_transfer tr;
    svt_usb_transfer::transfer_type_enum transfer_type;
    svt_usb_types::speed_enum connected_speed;
    uvm_sequence_item response;
    usb_ocp_event actual;
    usb_ocp_base_epn_profile::bytes_t expected;
    longint unsigned floor;
    logic [3:0] ep_number;
    int size;
    bit native_ok;
    bit negative_native;
    if (endpoint == null || !endpoint.anchor_index_valid || observer == null ||
        ocp_cfg == null || !(device inside {1,2}))
      `uvm_fatal("OCP_EPN_HOST", "Missing discovered endpoint or supported host context")
    resolve_host_context(1);
    connected_speed = usb_cfg.remote_device_cfg[device].connected_bus_speed;
    if (!(connected_speed inside {svt_usb_types::FS,svt_usb_types::HS}))
      `uvm_fatal("OCP_EPN_HOST", "Only discovered FS/HS USB2 endpoints are supported")
    if (device == 2 && address !== usb_cfg.remote_device_cfg[device].device_address)
      `uvm_fatal("OCP_EPN_HOST", "EPN wire address does not match its enumerated native slot")
    expected = usb_ocp_base_epn_profile::ocp_prepare_stream(
      endpoint.direction,phase,payload_length,data_tag);
    size = expected.size();
    if (size < 1 || size > endpoint.max_packet_size)
      `uvm_fatal("OCP_EPN_HOST", "Planned stream exceeds discovered maxpacket")
    ep_number = 4'(endpoint.ep_number);
    case (endpoint.transfer_type)
      USB_TRANSFER_TYPE_BULK: transfer_type = (endpoint.direction == USB_DIRECTION_IN) ?
        svt_usb_transfer::BULK_IN_TRANSFER : svt_usb_transfer::BULK_OUT_TRANSFER;
      USB_TRANSFER_TYPE_INTERRUPT: transfer_type = (endpoint.direction == USB_DIRECTION_IN) ?
        svt_usb_transfer::INTERRUPT_IN_TRANSFER : svt_usb_transfer::INTERRUPT_OUT_TRANSFER;
      USB_TRANSFER_TYPE_ISOCHRONOUS: transfer_type = (endpoint.direction == USB_DIRECTION_IN) ?
        svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER : svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER;
      default: `uvm_fatal("OCP_EPN_HOST", "Unsupported discovered type")
    endcase
    floor = observer.next_order;
    tr = svt_usb_transfer::type_id::create("epn_request");
    start_item(tr,-1,p_sequencer.xfer_sequencer);
    tr.cfg = usb_cfg;
    // Native unfixed selection with address/type/number constrained below
    // avoids assuming a USB2 nonstream-resource queue entry exists at zero.
    // The actual monitor and wire identity must still match discovery.
    if (endpoint.transfer_type != USB_TRANSFER_TYPE_BULK) begin
      tr.reasonable_start_uframe_bus_interval.constraint_mode(0);
    end
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      tr.payload = svt_usb_payload::type_id::create("epn_out_payload");
      tr.payload.USER_DEFINED_ALGORITHM_wt = 1;
      tr.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
    end
    if (!tr.randomize() with {
          xfer_type == local::transfer_type;
          device_address == local::address;
          endpoint_number == local::ep_number;
          device_connected_bus_speed == local::connected_speed;
          payload_intended_byte_count == local::size;
          payload_start_ix == 0;
          schedule_priority == 99;
          // USB2 5.7.3/5.8.3: the exact requested count ends the transfer.
          if (local::size == local::endpoint.max_packet_size &&
              local::endpoint.transfer_type != USB_TRANSFER_TYPE_ISOCHRONOUS)
            aligned_transfer_ends_with_zero_length == 0;
          if (local::endpoint.transfer_type != USB_TRANSFER_TYPE_BULK) {
            start_uframe_bus_interval == int'(local::scheduled_microframe);
            end_uframe_bus_interval == -1;
          }
          if (local::endpoint.transfer_type == USB_TRANSFER_TYPE_ISOCHRONOUS) {
            first_isoc_transaction == 1;
            last_isoc_transaction == 1;
            force_extra_isoc == 0;
          }
        }) `uvm_fatal("OCP_EPN_HOST", "Native EPN randomization failed")
    if (endpoint.direction == USB_DIRECTION_OUT) begin
      if (tr.payload == null || tr.payload.data.size() < size)
        `uvm_fatal("OCP_EPN_HOST", "Native OUT payload allocation is insufficient")
      foreach (expected[i]) tr.payload.data[i] = expected[i];
    end
    `uvm_info("OCP_EPN_SUBMIT",$sformatf(
      "slot=%0d addr=%0d %s phase=%0d bytes=%0d scheduled_uframe=%0d floor=%0d",
      device,address,endpoint.convert2string(),phase,size,scheduled_microframe,floor),UVM_LOW)
    finish_item(tr);
    get_response(response,tr.get_transaction_id());
    if (response == null || response.get_sequence_id() != tr.get_sequence_id() ||
        response.get_transaction_id() != tr.get_transaction_id())
      `uvm_fatal("OCP_EPN_HOST", "Wrong native routed EPN response")
    tr.end_event.wait_on();
    native_ok = (tr.status === svt_sequence_item::ACCEPT && tr.results_status === 0 &&
                 tr.device_connected_bus_speed === connected_speed &&
                 tr.xfer_type === transfer_type && tr.device_address === address &&
                 tr.endpoint_number === ep_number && tr.completed_payload_bytes() === size);
    negative_native = $test$plusargs("usb_ocp_negative_epn_native");
    // Only the private decision changes; native outcome and wire data do not.
    if (negative_native && phase == 1 && endpoint.direction == USB_DIRECTION_OUT)
      native_ok = 0;
    if (!native_ok)
      `uvm_fatal("OCP_EPN_HOST",$sformatf(
        "Completed native EPN outcome rejected phase=%0d dir=%s status=%s results=%h actual_bytes=%0d expected_bytes=%0d negative=%0b",
        phase,endpoint.direction.name(),tr.status.name(),tr.results_status,
        tr.completed_payload_bytes(),size,negative_native))
    observer.ocp_wait_epn_completion(address,ep_number,transfer_type,floor,
                                     ocp_cfg.control_transfer_timeout,actual);
    if (!actual.transfer_ok || actual.results !== 0 ||
        actual.completed_bytes !== size || actual.bytes !== expected)
      `uvm_fatal("OCP_EPN_HOST", "Actual monitor EPN completion differs from planned stream")
    // Actual monitor identity is independent of the submitted UVM item.
    `uvm_info("OCP_EPN_COMPLETE",$sformatf(
      "addr=%0d ep=%0d type=%s monitor_instance=%0d serial=%0d start=%0d end=%0d",
      address,ep_number,transfer_type.name(),actual.vendor_instance,
      actual.transfer_serial,actual.transfer_start_order,actual.order),UVM_LOW)
    completed = 1;
  endtask
endclass
