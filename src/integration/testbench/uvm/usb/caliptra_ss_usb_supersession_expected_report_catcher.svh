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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_EXPECTED_REPORT_CATCHER_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_EXPECTED_REPORT_CATCHER_SVH
// USB 2.0 8.5.3: corrupted SETUP data receives no handshake. Attribute one
// consequent timing report to the actual host-link reporter, never globally.
class caliptra_ss_usb_supersession_expected_report_catcher extends uvm_report_catcher;
    `uvm_object_utils(caliptra_ss_usb_supersession_expected_report_catcher)
    localparam string EXPECTED_ID =
        "register_fail:LINK 20 TIMING CHECKS:COMMON:tend_to_end_delay_check";
    uvm_report_object link_reporter;
    caliptra_ss_usb_supersession_checker sink;
    svt_usb_transfer bound_transfer;
    svt_usb_packet bound_packet;
    logic [15:0] generation;
    bit armed, installed;
    int matched_reports = 0;
    realtime data_end_at, expires_at;

    function new(string name = "caliptra_ss_usb_supersession_expected_report_catcher");
        super.new(name);
    endfunction

    function void arm(input logic [15:0] gen, input svt_usb_transfer transfer,
                      input svt_usb_packet packet, input realtime data_end,
                      input time response_timeout);
        if ((link_reporter == null) || (sink == null) ||
            (transfer == null) || (packet == null) || installed || armed ||
            !sink.characterizing_generation(gen) ||
            (transfer.device_address !== sink.address) ||
            (transfer.endpoint_number !== 0) ||
            (transfer.xfer_type !== svt_usb_transfer::CONTROL_TRANSFER) ||
            (data_end <= 0) || (data_end > $realtime))
            `uvm_fatal("SUPERSESSION_EXPECTED", "Invalid actual badCRC transmission/report context")
        generation = gen;
        bound_transfer = transfer;
        bound_packet = packet;
        data_end_at = data_end;
        expires_at = data_end + response_timeout;
        matched_reports = 0;
        armed = 1;
        uvm_report_cb::add(link_reporter, this);
        installed = 1;
    endfunction

    virtual function action_e catch();
        if (!armed || !installed || (matched_reports != 0) ||
            (get_client() != link_reporter) ||
            (get_severity() !== UVM_ERROR) || (get_id() != EXPECTED_ID))
            return THROW;
        if ((sink == null) || (bound_packet == null) ||
            (bound_transfer == null) ||
            !sink.characterizing_generation(generation) ||
            !sink.badcrc_silence_context(bound_transfer, bound_packet) ||
            ($realtime <= data_end_at) || ($realtime > expires_at))
            return THROW;
        matched_reports++;
        armed = 0;
        set_message($sformatf(
            "EXPECTED badCRC silence gen=%0d transfer=%0d packet=%0d end=%0t: %s",
            generation, bound_transfer.get_inst_id(), bound_packet.get_inst_id(),
            data_end_at, get_message()));
        set_id("SUPERSESSION_EXPECTED");
        set_severity(UVM_INFO);
        set_verbosity(UVM_NONE);
        set_action(UVM_DISPLAY);
        return THROW;
    endfunction

    function void close();
        armed = 0;
        if (installed) uvm_report_cb::delete(link_reporter, this);
        installed = 0;
        bound_transfer = null;
        bound_packet = null;
    endfunction
endclass
`endif
