//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************

// Selects an ordinary periodic layout without duplicating speed-specific tests.
class usb_periodic_test extends usb_base_test;
  `uvm_component_utils(usb_periodic_test)

  localparam int unsigned HS_ISO_MAX_PACKET_BYTES = 1024;
  // USB 2.0 5.6.4/5.11.3: reserve both directions within the 90% FS frame budget.
  localparam int unsigned FS_ISO_PAIRED_PACKET_BYTES = 512;
  usb_transfer_type_e periodic_type = USB_TRANSFER_TYPE_INTERRUPT;

  // HS enumeration and four single-transaction periodic transfers.
  function new(string name = "usb_periodic_test", uvm_component parent = null);
    super.new(name, parent);
    test_timeout = 3ms;
  endfunction

  virtual function time full_speed_timeout();
    return USB_FS_ENUMERATION_BUDGET +
      (periodic_type == USB_TRANSFER_TYPE_ISOCHRONOUS ?
       usb_init_host_seq::ALTERNATE_SELECTION_REQUEST_COUNT * USB_FS_CONTROL_TRANSFER_TIMEOUT : 0) +
      4 * USB_FS_PERIODIC_TRANSFER_TIMEOUT + USB_FS_FRAME_PERIOD;
  endfunction

  // Keep descriptor bInterval=1 and isoc_mult=0; builder maps native metadata.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
    int unsigned mps;
    string mode = "INTERRUPT";

    void'($value$plusargs("usb_periodic_type=%s", mode));
    case (mode)
      "INTERRUPT": periodic_type = USB_TRANSFER_TYPE_INTERRUPT;
      "ISO": periodic_type = USB_TRANSFER_TYPE_ISOCHRONOUS;
      default: `uvm_fatal("USB_PERIODIC_TEST", $sformatf("+usb_periodic_type must be INTERRUPT or ISO, not '%s'", mode))
    endcase
    // USB 2.0 5.6.3/5.7.3: ordinary packets, with no HS high-bandwidth multiplier.
    // Keep interrupt MPS at 64 so it remains legal in the default interface.
    mps = periodic_type == USB_TRANSFER_TYPE_ISOCHRONOUS ?
          (cfg.speed == USB_SPEED_FULL ? FS_ISO_PAIRED_PACKET_BYTES : HS_ISO_MAX_PACKET_BYTES) : `SVT_USB_FS_INTR_MAX_PACKET_SIZE;
    cfg.endpoint_cfgs.delete();
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_periodic_in", 1, USB_DIRECTION_IN, periodic_type, mps, 1, 1'b1, 0, 0)));
    void'(cfg.add_endpoint(usb_endpoint_cfg::create_endpoint("ep1_periodic_out", 1, USB_DIRECTION_OUT, periodic_type, mps, 1, 1'b1, 0, 0)));
  endfunction

  // Keep stimulus and checking in their reusable sequences and native VIP.
  task run_phase(uvm_phase phase);
    usb_periodic_seq sequence_handle;
    phase.raise_objection(this);
    `uvm_info("USB_PERIODIC_TEST", $sformatf("Starting ordinary %s %s scenario", env_cfg.speed.name(), periodic_type.name()), UVM_LOW)
    env.wait_for_reset();
    sequence_handle = usb_periodic_seq::type_id::create("sequence_handle");
    sequence_handle.start(env.virtual_sequencer);
    scenario_completed = sequence_handle.completed;
    `uvm_info("USB_PERIODIC_TEST", "Periodic sequence returned; entering final checks", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
