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

`ifndef CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_SEQUENCE_SV

// =============================================================================
// USB HS EP-info rate-feedback / descriptor-toggle sequence (hub + USBDC0).
// Suffix / message id: USB_DMA_EPINFO_RATE_FEEDBACK.
//
// Code-coverage stimulus for the READ_EPINFO decode of usb_dma.m.vhdl
// (third_party/usb2 copy). The firmware does the interesting part: before each
// leg it writes one EP5 OUT descriptor word (buffer 0 = lower word, buffer 1 =
// upper word of the 64-bit EP-list read, selected through EPINUSE) with the
// TR / TV-RF / T combination for that leg. This sequence only has to deliver
// one 8-byte BULK OUT per leg and check that each one completes.
//
//   leg  buffer  descriptor bits     usb_dma lines   host PID
//   0    0       TR=0 T=0 RF=1       386, 387        DATA0
//   1    0       TR=1 TV=1           376             DATA1
//   2    1       TR=0 T=0 RF=1       352, 353        DATA0
//   3    1       TR=1 TV=1           341, 342, 346   DATA1
//   4    1       TR=1 TV=0           341, 344, 346   DATA0
//
// The host PID column is the VIP's running bulk OUT toggle: it starts at DATA0
// on the first transfer to this endpoint and flips on every ACK, because
// nothing in this sequence calls reconfigure() after enumeration (see
// caliptra_ss_usb_shared_cfg::add_remote_device_slot for why a reconfigure()
// would reset it). The firmware leg order is chosen so the toggle each fetch
// establishes equals that PID, so every leg is ACKed AND consumed.
//
// VERDICT. Each leg must complete (ACCEPT). The firmware independently checks
// the received payload and Active, and fails the run with TB_CMD_TEST_FAIL
// otherwise. A set/clear path that did not act would make the device ACK and
// DISCARD the packet as a retransmission: the host still sees ACCEPT, but the
// firmware sees no completion, its leg counter stalls, and the NEXT leg here
// is never consumed - so a broken leg shows up as a firmware FAIL and as a
// timeout on the following leg, not as a silent pass.
//
// No report catcher is needed: every packet gets a real ACK and nothing is
// expected to time out, so UVM_ERROR must be 0.
// =============================================================================

class caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence)

    string MSG_ID = "USB_DMA_EPINFO_RATE_FEEDBACK";

    // Must match the firmware (USB_RF_EP, USB_RF_LEG_BYTES, USB_RF_NUM_LEGS).
    localparam int          RF_EP        = 5;
    localparam int          RF_DEV_ADDR  = 2;
    localparam int unsigned RF_LEG_BYTES = 8;
    localparam int          RF_NUM_LEGS  = 5;

    // VIP endpoint_cfg[] index set up by the test class for EP5 BULK OUT.
    localparam int          RF_EP_ANCHOR = 1;

    // Gap between legs. The firmware re-arms the next leg inside its EP5 OUT
    // interrupt handling; if a leg arrives before that, the endpoint only NAKs
    // and the VIP retries, so this is margin, not a correctness requirement.
    localparam realtime     LEG_GAP      = 20us;

    function new(string name = "caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence");
        super.new(name);
    endfunction

    // byte i = 0x10*(leg+1) + i. Must match rf_expected_word() in the firmware.
    protected function void build_leg_payload(int leg, ref bit [7:0] data[]);
        data = new[RF_LEG_BYTES];
        foreach (data[i])
            data[i] = 8'(16 * (leg + 1) + i);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      leg_req;
        bit [7:0]             leg_data[];
        string                leg_names[RF_NUM_LEGS] = '{
            "buf0_rate_feedback", "buf0_set_toggle",
            "buf1_rate_feedback", "buf1_set_toggle", "buf1_clear_toggle"};

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        wait_for_link_enabled(shared_status, "HS host link");
        if (link_wait_timed_out) begin
            `uvm_error(MSG_ID, "Link never reached ENABLED; aborting.")
            return;
        end
        start_sof_generation();
        #20us;

        // Hub at address 1, downstream port 1, USBDC0 at address 2. The
        // firmware arms leg 0 once SET_CONFIGURATION has been accepted.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);
        `uvm_info(MSG_ID, "HS enumeration complete.", UVM_LOW)
        #(LEG_GAP);

        for (int leg = 0; leg < RF_NUM_LEGS; leg++) begin
            build_leg_payload(leg, leg_data);
            `uvm_info(MSG_ID,
                $sformatf("=== LEG %0d: %s - BULK OUT %0d bytes to Dev:%0d EP:%0d ===",
                          leg, leg_names[leg], RF_LEG_BYTES, RF_DEV_ADDR, RF_EP),
                UVM_LOW)

            // fork_wait defaults to 1, so this returns only once the VIP has
            // reported the transfer ended. Do NOT call wait_xfer_done() after
            // it (claude_md note 22 section 7).
            do_data_xfer(
                .agent_h      (host_agent_h),
                .usb_cfg      (usb_cfg),
                .xfer_kind    (svt_usb_transfer::BULK_OUT_TRANSFER),
                .device_addr  (RF_DEV_ADDR),
                .ep_num       (RF_EP),
                .byte_count   (RF_LEG_BYTES),
                .ep_anchor_idx(RF_EP_ANCHOR),
                .label        ($sformatf("RF_LEG%0d_%s", leg, leg_names[leg])),
                .req          (leg_req),
                .obj_name     ($sformatf("rf_leg%0d_req", leg)),
                // HS bulk max packet is 512, so 8 bytes is a short packet and
                // already terminates the transfer: do not set
                // no_zero_length_end (unsatisfiable, see the disabled_ep seq).
                .payload_data (leg_data));

            if (leg_req == null) begin
                `uvm_fatal(MSG_ID, $sformatf("Leg %0d: no transfer item returned.", leg))
            end
            else if (leg_req.status != svt_usb_transfer::ACCEPT ||
                     (leg_req.results_status & ~USB_RESULTS_STATUS_BENIGN_MASK) != 0) begin
                `uvm_error(MSG_ID,
                    $sformatf({"Leg %0d (%s) did not complete: status=%p results_status=0x%0h. ",
                               "Check the firmware 'RF leg %0d armed' line: a missing arm or a ",
                               "toggle that does not match the host PID leaves the endpoint ",
                               "NAKing or silently discarding."},
                              leg, leg_names[leg], leg_req.status, leg_req.results_status, leg))
            end
            else begin
                `uvm_info(MSG_ID,
                    $sformatf("Leg %0d (%s) completed at %0t.", leg, leg_names[leg], $time),
                    UVM_LOW)
            end

            #(LEG_GAP);
        end

        `uvm_info(MSG_ID, "EP-info rate-feedback sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
