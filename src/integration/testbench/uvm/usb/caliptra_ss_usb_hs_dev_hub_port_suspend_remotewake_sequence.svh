

// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and

`ifndef CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_REMOTEWAKE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_REMOTEWAKE_SEQUENCE_SV

// =============================================================================
// USB HS hub downstream PORT_SUSPEND followed by a device REMOTE WAKEUP.
//
// Coverage target: the hub_port_remotewakeup branch in PROC_REQUEST_HANDLING
// (usb_app_hw_hub.m.vhdl). Its inner condition needs hub_port_suspend_int(i) = 1
// when the device raises remote wakeup; only then is hub_port_suspend_change
// set. Suspending the whole upstream bus (caliptra_ss_usb_hs_host_remotewakeup_
// fromdevice) does not set hub_port_suspend_int, so that test cannot reach it.
//
// Flow, with the hub kept ACTIVE the whole time (SOF never stops, there is no
// suspend signalling on the upstream port):
//   1. hub-aware enumeration, port 1 reset and enabled, USBDC0 at address 2
//   2. baseline GetPortStatus: bit 2 (PORT_SUSPEND) = 0, bit 18 = 0
//   3. SetPortFeature(PORT_SUSPEND) on port 1 -> bit 2 = 1, bit 18 = 0
//   4. the MCU firmware sees DEVCMDSTAT.DSUS and requests a remote wakeup on
//      its own (no host to MCU command); the host polls GetPortStatus until
//      bit 2 drops, bounded
//   5. bit 2 = 0 and bit 18 (C_PORT_SUSPEND) = 1 : set by the remote wakeup,
//      not by ClearPortFeature(PORT_SUSPEND), which is never sent in this test
//   6. ClearPortFeature(C_PORT_SUSPEND) -> bit 18 = 0
//   7. GetDescriptor(Device) to USBDC0: the device still answers
//
// Helpers and status-bit checks are inherited from
// caliptra_ss_usb_hs_dev_hub_port_suspend_sequence.
// =============================================================================

class caliptra_ss_usb_hs_dev_hub_port_suspend_remotewake_sequence
        extends caliptra_ss_usb_hs_dev_hub_port_suspend_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_hub_port_suspend_remotewake_sequence)

    // Maximum number of GetPortStatus reads while waiting for the remote wakeup
    // to clear PORT_SUSPEND, and the gap between them. The MCU needs roughly
    // 1500 firmware polls (about 200 us) of stable DSUS before it requests the
    // wakeup, so this window is several times larger than that.
    localparam int unsigned WAKE_POLL_MAX_ATTEMPTS = 40;
    localparam realtime     WAKE_POLL_GAP          = 50us;

    function new(string name = "caliptra_ss_usb_hs_dev_hub_port_suspend_remotewake_sequence");
        super.new(name);
        MSG_ID = "USB_HS_HUB_PSUSP_RW_SEQ";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        bit                   woke;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: link, SOF, hub-aware enumeration (same as the parent).
        wait_for_link_enabled(shared_status, "HS host link");
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        hub_enum_stepA(host_agent_h, usb_cfg);
        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_UT));
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info(MSG_ID, "Initial hub-aware enumeration done (USBDC0 at addr 2).", UVM_LOW)

        // Hub class requests address the hub at address 1.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        // Step 2: baseline.
        get_port_status(host_agent_h, usb_cfg, "baseline");
        check_port_status_bit("baseline", BIT_PORT_SUSPEND,   1'b0, "PORT_SUSPEND");
        check_port_status_bit("baseline", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 3: suspend only the downstream port. The upstream link stays
        // active.
        `uvm_info(MSG_ID,
            $sformatf("Driving SetFeature(PORT_SUSPEND) on downstream port %0d.", PORT_UT),
            UVM_LOW)
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_SET_FEATURE, FEAT_PORT_SUSPEND,
            16'(PORT_UT), 16'h0000, 1, "SetFeature_PORT_SUSPEND", usb_cfg);
        wait_xfer_done(host_agent_h, "SetFeature_PORT_SUSPEND");
        #STATUS_SETTLE;

        get_port_status(host_agent_h, usb_cfg, "postSet");
        check_port_status_bit("postSet", BIT_PORT_SUSPEND,   1'b1, "PORT_SUSPEND");
        check_port_status_bit("postSet", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 4: the firmware requests the remote wakeup. Poll the hub until
        // PORT_SUSPEND drops. Only status reads are sent here; nothing resumes
        // the port from the host side.
        woke = 1'b0;
        for (int attempt = 1; attempt <= WAKE_POLL_MAX_ATTEMPTS && !woke; attempt++) begin
            #WAKE_POLL_GAP;
            get_port_status(host_agent_h, usb_cfg, $sformatf("wakePoll%0d", attempt));
            if (port_status_bit_is(BIT_PORT_SUSPEND, 1'b0)) begin
                woke = 1'b1;
                `uvm_info(MSG_ID,
                    $sformatf("PORT_SUSPEND dropped after %0d GetPortStatus read(s); the device remote wakeup reached the hub.",
                              attempt), UVM_LOW)
            end
        end

        if (!woke) begin
            `uvm_error(MSG_ID,
                $sformatf("PORT_SUSPEND of port %0d never dropped within %0d GetPortStatus reads (%0t apart), so no remote wakeup reached the hub. Check the MCU log for 'remote wakeup driven' and DSUS reports.",
                          PORT_UT, WAKE_POLL_MAX_ATTEMPTS, WAKE_POLL_GAP))
        end

        // Step 5: the wakeup must have latched the change bit. This is the
        // behaviour the inner condition of the hub branch implements.
        get_port_status(host_agent_h, usb_cfg, "postWake");
        check_port_status_bit("postWake", BIT_PORT_SUSPEND,   1'b0, "PORT_SUSPEND");
        check_port_status_bit("postWake", BIT_C_PORT_SUSPEND, 1'b1, "C_PORT_SUSPEND");

        // Step 6: acknowledge the change bit.
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_CLEAR_FEATURE, FEAT_C_PORT_SUSPEND,
            16'(PORT_UT), 16'h0000, 1, "ClearFeature_C_PORT_SUSPEND", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_SUSPEND");
        #STATUS_SETTLE;

        get_port_status(host_agent_h, usb_cfg, "postAck");
        check_port_status_bit("postAck", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 7: the device behind the port still answers traffic.
        #POST_RESUME_SETTLE;
        post_resume_traffic_check(host_agent_h, usb_cfg);

        #100us;
    endtask

    // -------------------------------------------------------------------------
    // Quiet check of one bit of the last GetPortStatus response, used while
    // polling. Returns 0 when the response is missing or short, so a poll that
    // got no data does not end the wait early. The error reporting version is
    // check_port_status_bit() in the parent.
    // -------------------------------------------------------------------------
    function bit port_status_bit_is(int unsigned bit_idx, bit exp_val);
        bit [31:0] status_word;

        if (last_ctrl_seq_item == null)
            return 1'b0;
        if (last_ctrl_seq_item.payload_byte_count() < 4)
            return 1'b0;

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};
        return (status_word[bit_idx] === exp_val);
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_REMOTEWAKE_SEQUENCE_SV
