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

`ifndef CALIPTRA_SS_USB_HB_ISO_MONITOR_CALLBACK_SV
`define CALIPTRA_SS_USB_HB_ISO_MONITOR_CALLBACK_SV

// Passively records high-bandwidth ISO IN data packets and interrupting SOFs.
class caliptra_ss_usb_hb_iso_monitor_callback
    extends svt_usb_link_monitor_callback;

    `uvm_object_utils(caliptra_ss_usb_hb_iso_monitor_callback)

    protected uvm_event sof_observed;
    protected uvm_event data_packet_observed;
    protected bit window_active;
    protected int unsigned data_packet_count;
    protected int unsigned data_packets_before_sof;
    protected int unsigned interrupting_sof_count;

    function new(string name = "caliptra_ss_usb_hb_iso_monitor_callback");
        super.new(name);
        sof_observed = new("sof_observed");
        data_packet_observed = new("data_packet_observed");
    endfunction

    // Reset all counters and begin a new observation window.
    function void start_window();
        data_packet_count = 0;
        data_packets_before_sof = 0;
        interrupting_sof_count = 0;
        window_active = 1'b1;
        `uvm_info("USB_SS_HB_ISO_MON", "Started high-bandwidth ISO observation window", UVM_LOW)
    endfunction

    // End observation after the transfer completes.
    function void stop_window();
        window_active = 1'b0;
        `uvm_info(
            "USB_SS_HB_ISO_MON",
            $sformatf(
                "Stopped observation window: data_packets=%0d interrupting_sofs=%0d first_sof_after_packets=%0d",
                data_packet_count,
                interrupting_sof_count,
                data_packets_before_sof),
            UVM_LOW)
    endfunction

    // Wait for the next passively observed host SOF.
    task wait_for_sof(time timeout, output bit observed);
        observed = 1'b0;
        sof_observed.reset();
        fork
            begin
                sof_observed.wait_ptrigger();
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable fork;
    endtask

    // Wait until the requested number of device data packets are observed.
    task wait_for_data_packets(
        int unsigned target_count,
        time timeout,
        output bit observed);

        observed = data_packet_count >= target_count;
        if (observed) begin
            return;
        end
        fork
            begin
                do begin
                    data_packet_observed.reset();
                    data_packet_observed.wait_ptrigger();
                end while (data_packet_count < target_count);
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable fork;
    endtask

    // Wait for a SOF that follows at least one observed ISO IN data packet.
    task wait_for_interrupting_sof(time timeout, output bit observed);
        observed = interrupting_sof_count > 0;
        if (observed) begin
            return;
        end
        fork
            begin
                do begin
                    sof_observed.reset();
                    sof_observed.wait_ptrigger();
                end while (interrupting_sof_count == 0);
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable fork;
    endtask

    function int unsigned get_data_packet_count();
        return data_packet_count;
    endfunction

    function int unsigned get_data_packets_before_sof();
        return data_packets_before_sof;
    endfunction

    function int unsigned get_interrupting_sof_count();
        return interrupting_sof_count;
    endfunction

    // Record a protocol-valid SOF injected through the UTMI control interface.
    function void note_injected_sof();
        if (!window_active || (data_packet_count == 0)) begin
            `uvm_fatal(
                "USB_SS_HB_ISO_MON",
                "Injected SOF must follow an observed ISO IN data packet")
        end
        if (interrupting_sof_count == 0) begin
            data_packets_before_sof = data_packet_count;
        end
        interrupting_sof_count++;
        `uvm_info(
            "USB_SS_HB_ISO_MON",
            $sformatf(
                "Recorded injected SOF after %0d ISO IN data packet(s)",
                data_packet_count),
            UVM_LOW)
    endfunction

    // Device-to-host DATA packets are observed on the monitor RX path.
    virtual function void usb_20_rx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);

        if (window_active &&
            (pkt != null) &&
            ((pkt.pid_name == svt_usb_packet::DATA0) ||
             (pkt.pid_name == svt_usb_packet::DATA1) ||
             (pkt.pid_name == svt_usb_packet::DATA2) ||
             (pkt.pid_name == svt_usb_packet::MDATA))) begin
            data_packet_count++;
            data_packet_observed.trigger();
        end
    endfunction

    // Host SOFs are observed on the monitor TX path.
    virtual function void usb_20_tx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);

        if ((pkt == null) || (pkt.pid_name != svt_usb_packet::SOF)) begin
            return;
        end
        sof_observed.trigger();
        if (window_active && (data_packet_count > 0)) begin
            if (interrupting_sof_count == 0) begin
                data_packets_before_sof = data_packet_count;
            end
            interrupting_sof_count++;
        end
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HB_ISO_MONITOR_CALLBACK_SV
