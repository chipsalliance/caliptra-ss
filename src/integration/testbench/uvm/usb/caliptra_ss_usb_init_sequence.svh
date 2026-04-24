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

`ifndef CALIPTRA_SS_USB_INIT_SEQUENCE_SV
`define CALIPTRA_SS_USB_INIT_SEQUENCE_SV

// =============================================================================
// Basic USB init sequence: GET_DESCRIPTOR followed by SET_ADDRESS.
//
// This exercises the minimum USB enumeration flow that any device must support.
// =============================================================================
class caliptra_ss_usb_init_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_init_sequence)
    `uvm_declare_p_sequencer(svt_usb_transfer_sequencer)

    function new(string name = "caliptra_ss_usb_init_sequence");
        super.new(name);
    endfunction

    virtual task pre_start();
        uvm_phase phase;
        super.pre_start();
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.raise_objection(this);
    endtask

    virtual task post_start();
        uvm_phase phase;
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.drop_objection(this);
    endtask

    virtual task body();
        bit status;
        svt_configuration get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_transfer xfer;

        `uvm_info("body", "Starting USB basic init sequence...", UVM_LOW)

        // Get configuration from sequencer
        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("body", "Unable to cast configuration")

        // -----------------------------------------------------------------
        // Transfer 1: GET_DESCRIPTOR (Device Descriptor) — CONTROL IN
        // -----------------------------------------------------------------
        `uvm_create(xfer)
        xfer.cfg = usb_cfg;
        xfer.fix_anchors(0, 0, 0);
        status = xfer.randomize() with {
            setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
            setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
            setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
            setup_data_brequest                == svt_usb_types::GET_DESCRIPTOR;
            setup_data_w_value                 == 16'h0100; // Device descriptor
            setup_data_w_index                 == 0;
            setup_data_w_length                == 18;       // Device descriptor length
        };
        if (!status)
            `uvm_fatal("body", "GET_DESCRIPTOR randomization failed")
        `uvm_send(xfer)
        `uvm_info("body", "GET_DESCRIPTOR (Device) completed", UVM_LOW)

        // -----------------------------------------------------------------
        // Transfer 2: SET_ADDRESS — CONTROL OUT (no data stage)
        // -----------------------------------------------------------------
        `uvm_create(xfer)
        xfer.cfg = usb_cfg;
        xfer.fix_anchors(0, 0, 0);
        status = xfer.randomize() with {
            setup_data_bmrequesttype_dir       == svt_usb_types::HOST_TO_DEVICE;
            setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
            setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
            setup_data_brequest                == svt_usb_types::SET_ADDRESS;
            setup_data_w_value                 == 16'h0005; // Address 5
            setup_data_w_index                 == 0;
            setup_data_w_length                == 0;
        };
        if (!status)
            `uvm_fatal("body", "SET_ADDRESS randomization failed")
        `uvm_send(xfer)
        `uvm_info("body", "SET_ADDRESS completed", UVM_LOW)

        // -----------------------------------------------------------------
        // Transfer 3: GET_DESCRIPTOR (Configuration Descriptor) — CONTROL IN
        // -----------------------------------------------------------------
        `uvm_create(xfer)
        xfer.cfg = usb_cfg;
        xfer.fix_anchors(0, 0, 0);
        status = xfer.randomize() with {
            setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
            setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
            setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
            setup_data_brequest                == svt_usb_types::GET_DESCRIPTOR;
            setup_data_w_value                 == 16'h0200; // Configuration descriptor
            setup_data_w_index                 == 0;
            setup_data_w_length                == 64;
        };
        if (!status)
            `uvm_fatal("body", "GET_DESCRIPTOR (Config) randomization failed")
        `uvm_send(xfer)
        `uvm_info("body", "GET_DESCRIPTOR (Configuration) completed", UVM_LOW)

        // Wait for VIP to process queued transfers on the UTMI bus.
        // uvm_send returns immediately (the VIP driver queues transfers);
        // without this delay the phase objection drops at time 0 and the
        // simulator exits before any clock edges occur.
        `uvm_info("body", "Waiting for UTMI bus activity...", UVM_LOW)
        #200_000ns;

        `uvm_info("body", "USB basic init sequence complete.", UVM_LOW)
    endtask

endclass

`endif
