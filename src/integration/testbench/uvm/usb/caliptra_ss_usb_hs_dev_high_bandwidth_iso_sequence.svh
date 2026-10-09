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

`ifndef CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_SEQUENCE_SV

// Reproduces SOF-interrupted high-bandwidth ISO IN replay at subsystem level.
class caliptra_ss_usb_hs_dev_high_bandwidth_iso_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_high_bandwidth_iso_sequence)

    localparam int unsigned PACKET_BYTES = 1024;
    localparam int unsigned TRANSACTION_COUNT = 3;
    localparam int unsigned TRANSFER_BYTES =
        PACKET_BYTES * TRANSACTION_COUNT;
    localparam time PACKET_TIMEOUT = 500us;

    function new(
        string name =
            "caliptra_ss_usb_hs_dev_high_bandwidth_iso_sequence");
        super.new(name);
    endfunction

    // Return packet-distinct data so a replay cannot alias a valid packet.
    function bit [7:0] expected_byte(int unsigned byte_index);
        int unsigned packet_index;
        int unsigned packet_offset;
        bit [7:0] packet_base;

        packet_index = byte_index / PACKET_BYTES;
        packet_offset = byte_index % PACKET_BYTES;
        case (packet_index)
            0: packet_base = 8'h10;
            1: packet_base = 8'h50;
            default: packet_base = 8'h90;
        endcase
        return packet_base + 8'(packet_offset);
    endfunction

    // Check the complete host payload and report replay as the test failure.
    function int unsigned check_payload(
        svt_usb_transfer transfer,
        int unsigned expected_offset,
        int unsigned expected_count,
        string label);
        int unsigned mismatch_count;
        int unsigned observed_size;

        mismatch_count = 0;
        observed_size =
            ((transfer == null) || (transfer.payload == null)) ?
            0 : transfer.payload.data.size();
        if (observed_size != expected_count) begin
            `uvm_error(
                "USB_SS_HB_ISO",
                $sformatf(
                    "%s returned %0d bytes, expected %0d",
                    label,
                    observed_size,
                    expected_count))
            return expected_count;
        end

        for (int unsigned index = 0; index < expected_count; index++) begin
            bit [7:0] observed;
            bit [7:0] expected;

            observed = transfer.payload.get_byte_val(index);
            expected = expected_byte(expected_offset + index);
            if (observed !== expected) begin
                if (mismatch_count < 16) begin
                    `uvm_error(
                        "USB_SS_HB_ISO",
                        $sformatf(
                            "%s replay mismatch global byte %0d (packet %0d offset %0d): got 0x%02h expected 0x%02h",
                            label,
                            expected_offset + index,
                            (expected_offset + index) / PACKET_BYTES,
                            (expected_offset + index) % PACKET_BYTES,
                            observed,
                            expected))
                end
                mismatch_count++;
            end
        end
        return mismatch_count;
    endfunction

    // Enumerate the compound device and issue one aligned three-packet transfer.
    virtual task body();
        svt_usb_agent host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status shared_status;
        svt_usb_transfer iso_in_req;
        caliptra_ss_usb_hb_iso_monitor_callback monitor_cb;
        virtual caliptra_ss_usb_utmi_control_if utmi_control_vif;
        bit first_packet_seen;
        int unsigned mismatch_count;

        host_agent_h = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg = resolve_usb_cfg();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_utmi_control_if)::get(
                    null,
                    "uvm_test_top",
                    "usb_utmi_control_if",
                    utmi_control_vif)) begin
            `uvm_fatal(
                "USB_SS_HB_ISO",
                "Unable to get usb_utmi_control_if from config_db")
        end

        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_fatal("USB_SS_HB_ISO", "HS link did not become enabled")
        end
        start_sof_generation();
        #20us;
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info(
            "USB_SS_HB_ISO",
            "Enumeration complete; waiting for firmware to arm 3072-byte EP2 IN",
            UVM_LOW)
        #300us;

        monitor_cb =
            caliptra_ss_usb_hb_iso_monitor_callback::type_id::create(
                "monitor_cb");
        uvm_callbacks#(
            svt_usb_link_monitor,
            svt_usb_link_monitor_callback)::add(
                host_agent_h.link_mon,
                monitor_cb);

        monitor_cb.start_window();
        `uvm_info(
            "USB_SS_HB_ISO",
            "Starting one 3072-byte high-bandwidth ISO IN transfer",
            UVM_NONE)

        first_packet_seen = 1'b0;
        fork
            begin
                do_data_xfer(
                    .agent_h         (host_agent_h),
                    .usb_cfg         (usb_cfg),
                    .xfer_kind       (
                        svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER),
                    .device_addr     (2),
                    .ep_num          (2),
                    .byte_count      (TRANSFER_BYTES),
                    .ep_anchor_idx   (1),
                    .label           ("HS_HB_ISO_IN_EP2"),
                    .req             (iso_in_req),
                    .obj_name        ("hb_iso_in_req"),
                    .single_isoc_txn (1));
            end
            begin
                monitor_cb.wait_for_data_packets(
                    1,
                    PACKET_TIMEOUT,
                    first_packet_seen);
                if (!first_packet_seen) begin
                    `uvm_fatal(
                        "USB_SS_HB_ISO",
                        $sformatf(
                            "No ISO IN data packet observed within %0t",
                            PACKET_TIMEOUT))
                end
                `uvm_info(
                    "USB_SS_HB_ISO",
                    "Observed first 1024-byte packet; injecting valid SOF frame",
                    UVM_NONE)
                monitor_cb.note_injected_sof();
                utmi_control_vif.inject_sof_frame_zero();
                `uvm_info(
                    "USB_SS_HB_ISO",
                    "Injected SOF while high-bandwidth ISO IN remained pending",
                    UVM_NONE)
            end
        join
        monitor_cb.stop_window();

        if (monitor_cb.get_data_packet_count() < TRANSACTION_COUNT) begin
            `uvm_error(
                "USB_SS_HB_ISO",
                $sformatf(
                    "Only %0d/%0d ISO IN packets completed after SOF",
                    monitor_cb.get_data_packet_count(),
                    TRANSACTION_COUNT))
        end
        mismatch_count = check_payload(
            iso_in_req,
            0,
            TRANSFER_BYTES,
            "SOF-interrupted high-bandwidth ISO IN transfer");
        if (mismatch_count != 0) begin
            `uvm_error(
                "USB_SS_HB_ISO",
                $sformatf(
                    "SOF-interrupted ISO IN replayed data: %0d/%0d bytes mismatched",
                    mismatch_count,
                    TRANSFER_BYTES))
        end else begin
            `uvm_info(
                "USB_SS_HB_ISO",
                $sformatf(
                    "SOF-interrupted ISO IN preserved all %0d packet-distinct bytes",
                    TRANSFER_BYTES),
                UVM_LOW)
        end

        // Allow firmware to inspect descriptor writeback and halt.
        #100us;
        `uvm_info(
            "USB_SS_HB_ISO",
            "Subsystem high-bandwidth ISO replay scenario complete",
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HIGH_BANDWIDTH_ISO_SEQUENCE_SV
