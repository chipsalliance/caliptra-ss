

// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_SEQUENCE_SV

// =============================================================================
// USB HS hub downstream PORT_SUSPEND sequence (Hub-Enabled mode).
//
// WHAT THIS TEST CHECKS, AND WHAT IT DELIBERATELY DOES NOT
//
// On this IP the hub downstream port suspend feature is status-only by design.
// SetPortFeature(PORT_SUSPEND) latches hub_port_suspend and reports it back in
// the port status word, but the signal never leaves usb_app_hw_hub: it has no
// entity port and no output assignment, there is no per-port downstream traffic
// gate anywhere in the compound, and sync_suspend is a single net shared by both
// device controllers, so a per-port suspend state cannot even be represented.
// This was reviewed with the designer and is an accepted deviation from USB 2.0
// chapter 11, recorded in docs/usb_hub_port_suspend_not_wired_report.md.
//
// The requirement this test therefore verifies is the one that actually exists:
//   1. the port status ladder is correct and write-1-clear behaves, and
//   2. after ClearPortFeature(PORT_SUSPEND) the downstream device is still able
//      to receive and answer traffic.
//
// It does NOT assert that the device controller enters suspend, and it does not
// instantiate or arm caliptra_ss_usb_suspend_resume_checker. That checker is a
// hard pass/fail for caliptra_ss_usb_hs_dev_global_suspend_L2 and
// caliptra_ss_usb_fs_dev_global_suspend_L2, where a missing suspend edge is a real
// defect. Arming it here, in a test where a missing suspend edge is expected,
// would either force a permanently failing regression entry or require relaxing
// a checker that other tests depend on for their verdict. Neither is acceptable,
// so this test simply stays out of it: no ARM event, no observation window, no
// SuspendM dependency at all.
//
// The consequence is stated plainly so nobody mistakes a pass here for proof of
// per-port suspend: a PASS from this test means the hub accepted, reported and
// cleared the feature and the device still works afterwards. Whether any device
// ever actually suspended is out of scope by construction, and is answered
// (negatively) by the gap report.
//
// WHY THE POST-RESUME TRAFFIC CHECK IS THE LOAD-BEARING CHECK
// Without it this test would only read back bits that the hub itself just
// latched, which is close to asking the DUT to confirm its own bookkeeping. The
// post-resume transfer is the part that can genuinely break: it addresses the
// device behind the port that was just suspended and resumed, and it fails if
// the feature left the downstream path, the endpoint state or the device address
// matching in a bad state. This is deliberately not the mistake made in
// usbdc0_powerdown_step(), which advertises a GetPortStatus confirmation in its
// comments and then inspects nothing.
//
// A control transfer is used for that check rather than a bulk transfer because
// the firmware side of this test is a passive EP0 observer: it services EP0
// SETUP/IN/OUT and does not arm EP1 buffers, so a bulk OUT would be NAKed
// forever and would fail for a firmware reason unrelated to port suspend. The
// GetDescriptor(Device) used here is already proven serviceable by this firmware
// because usbdc0_enum_stepC issues the same request during enumeration.
//
// HOW THE STATUS PLANE IS CHECKED
// Every GetPortStatus response is read back from the transfer payload and the
// relevant bits are compared, using check_port_status_bit() below.
//
// The expected ladder follows the RTL and the spec, both of which set the
// change bit on resume rather than on suspend (usb_app_hw_hub.m.vhdl lines
// 220-221 versus 264; all line numbers in this file are at submodule commit
// 7c312db):
//   after SetFeature(PORT_SUSPEND)      bit 2 = 1, bit 18 = 0
//   after ClearFeature(PORT_SUSPEND)    bit 2 = 0, bit 18 = 1
//   after ClearFeature(C_PORT_SUSPEND)  bit 18 = 0
// Checking bit 18 = 0 after the Set is not pedantry: expecting it to be 1
// there would file a phantom bug against spec-correct RTL.
//
// Port status word bit numbering (GEN_HUB_PORT_STATUS, usb_app_hw_hub.m.vhdl):
//   bit  0 connect, bit 1 enable, bit 2 suspend, bit 8 power (hardwired 1),
//   bit 16 C_PORT_CONNECTION, bit 18 C_PORT_SUSPEND, bit 20 C_PORT_RESET.
//
// Flow:
//   1. Wait HS link ENABLED, then start SOF.
//   2. Full hub-aware enumeration: hub at address 1, downstream port 1 up,
//      USBDC0 at address 2 (Steps A + B + C).
//   3. Anchor the VIP on the hub (address 1) for the hub-class requests.
//   4. GetPortStatus baseline: port 1 must report not-suspended.
//   5. SetFeature(PORT_SUSPEND) on port 1, then GetPortStatus: bit 2 = 1.
//   6. Hold the port suspended for PORT_SUSPEND_DWELL with SOF still running.
//   7. ClearFeature(PORT_SUSPEND), then GetPortStatus: bit 2 = 0, bit 18 = 1.
//   8. ClearFeature(C_PORT_SUSPEND), then GetPortStatus: bit 18 = 0.
//   9. Re-anchor to the device at address 2 and require a control transfer to
//      complete and return a valid device descriptor.
//
// SOF runs continuously from step 1 to the end. It is never stopped, so the
// upstream link stays ENABLED and the hub stays enumerated throughout; only the
// downstream port is asked to suspend. That also means this test cannot
// accidentally reproduce the global suspend already covered by
// caliptra_ss_usb_hs_dev_global_suspend_L2.
//
// The 3-step hub-aware enumeration helpers (hub_enum_stepA,
// hub_port_bringup_stepB, usbdc0_enum_stepC) live in
// caliptra_ss_usb_base_sequence.svh.
// =============================================================================

class caliptra_ss_usb_hs_dev_hub_port_suspend_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_hub_port_suspend_sequence)

    string MSG_ID = "USB_HS_HUB_PSUSP_SEQ";

    // Downstream port under test. wIndex is 1-based on the wire; the RTL forms
    // var_port := wIndex - 1, so wIndex 1 is USBDC0 on hub_port_*(0).
    localparam int unsigned PORT_UT = 1;

    // Device address USBDC0 is left at by usbdc0_enum_stepC.
    localparam int unsigned DEV_ADDR = 2;

    // Hub class request codes and feature selectors (USB 2.0 table 11-17).
    localparam bit [7:0]  BREQ_GET_STATUS    = 8'h00;
    localparam bit [7:0]  BREQ_CLEAR_FEATURE = 8'h01;
    localparam bit [7:0]  BREQ_SET_FEATURE   = 8'h03;
    localparam bit [15:0] FEAT_PORT_SUSPEND   = 16'h0002;
    localparam bit [15:0] FEAT_C_PORT_SUSPEND = 16'h0012; // 18

    // Standard GetDescriptor(Device) for the post-resume traffic check.
    localparam bit [7:0]  BREQ_GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DESC_DEVICE_W_VALUE = 16'h0100; // type 1, index 0
    localparam bit [15:0] DEV_DESC_LEN        = 16'h0012; // 18 bytes
    localparam bit [7:0]  DESC_TYPE_DEVICE    = 8'h01;

    // GetPortStatus returns 4 bytes: wPortStatus then wPortChange, both LE.
    localparam bit [15:0] PORT_STATUS_LEN = 16'h0004;

    // Port status word bit positions.
    localparam int unsigned BIT_PORT_SUSPEND   = 2;
    localparam int unsigned BIT_C_PORT_SUSPEND = 18;

    // Settling delay after link-up, before any hub-class traffic. Same value
    // and same reason as the global_suspend_L2 sequence: the VIP link SM walks
    // TRANSMIT -> ENABLED over the first few microseconds after bus reset.
    localparam realtime LINK_SETTLE_DELAY = 500us;

    // Let the port status flop settle and be readable before the confirming
    // GetPortStatus. Only needs to cover the hub's own EP0 turnaround.
    localparam realtime STATUS_SETTLE = 10us;

    // How long the port is left in the suspended state before it is resumed.
    //
    // This is a fixed dwell, not a timeout waiting for something: nothing is
    // expected to happen on this IP, so there is no event to wait for and
    // nothing to time out on. It is sized against the DUT suspend detection
    // timer so that a build which DOES actuate the suspend would have had time
    // to reach it: with G_SIM_CHIRP_TIMERS=1 (how caliptra_ss_top_tb elaborates
    // the DUT) T_SUSPEND_DET is 200 us, so 600 us is 3x that. Against a
    // G_SIM_CHIRP_TIMERS=0 build the spec value is 3.072 ms and this dwell would
    // need raising to stay meaningful.
    localparam realtime PORT_SUSPEND_DWELL = 600us;

    // Settling time after ClearFeature(PORT_SUSPEND) before traffic is sent to
    // the device, so the post-resume check does not race the resume itself.
    localparam realtime POST_RESUME_SETTLE = 100us;

    function new(string name = "caliptra_ss_usb_hs_dev_hub_port_suspend_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: link first, then SOF.
        wait_for_link_enabled(shared_status, "HS host link");
        start_sof_generation();
        #LINK_SETTLE_DELAY;

        // Step 2: hub-aware enumeration (Steps A + B + C).
        hub_enum_stepA(host_agent_h, usb_cfg);
        // port_num is passed by name: the positional parameters of
        // hub_port_bringup_stepB after usb_cfg are suffix and
        // no_queue_and_hold, so passing PORT_UT positionally would land on the
        // wrong argument and silently bring up the default port.
        hub_port_bringup_stepB(.host_agent_h(host_agent_h), .usb_cfg(usb_cfg),
                               .port_num(PORT_UT));
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info(MSG_ID, "Initial hub-aware enumeration done (USBDC0 at addr 2).", UVM_LOW)

        // Step 3: the hub-class port requests address the HUB at address 1.
        // usbdc0_enum_stepC() left the anchor at 2 (USBDC0).
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID, "Anchor set to HUB address 1 for downstream port requests.", UVM_LOW)

        // Step 4: baseline. The port must not already report suspended, or the
        // Set-side check below would be unfalsifiable.
        get_port_status(host_agent_h, usb_cfg, "baseline");
        check_port_status_bit("baseline", BIT_PORT_SUSPEND,   1'b0, "PORT_SUSPEND");
        check_port_status_bit("baseline", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 5: suspend the downstream port.
        `uvm_info(MSG_ID,
            $sformatf("Driving SetFeature(PORT_SUSPEND) on downstream port %0d.", PORT_UT),
            UVM_LOW)
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_SET_FEATURE, FEAT_PORT_SUSPEND,
            16'(PORT_UT), 16'h0000, 1, "SetFeature_PORT_SUSPEND", usb_cfg);
        wait_xfer_done(host_agent_h, "SetFeature_PORT_SUSPEND");
        #STATUS_SETTLE;

        // C_PORT_SUSPEND is expected 0 here: both the spec and the RTL set the
        // change bit on resume, not on suspend.
        get_port_status(host_agent_h, usb_cfg, "postSet");
        check_port_status_bit("postSet", BIT_PORT_SUSPEND,   1'b1, "PORT_SUSPEND");
        check_port_status_bit("postSet", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 6: hold the port suspended. SOF keeps running, so on an IP that
        // gated downstream traffic per port the device would reach its suspend
        // detection timer inside this dwell. See the localparam comment.
        `uvm_info(MSG_ID,
            $sformatf("Holding port %0d suspended for %0t with SOF still running. On this IP no device-side suspend is expected; see docs/usb_hub_port_suspend_not_wired_report.md.",
                      PORT_UT, PORT_SUSPEND_DWELL), UVM_LOW)
        #PORT_SUSPEND_DWELL;

        // Step 7: resume the port. Per the RTL this clears hub_port_suspend and
        // sets hub_port_suspend_change, so bit 2 falls and bit 18 rises.
        `uvm_info(MSG_ID,
            $sformatf("Driving ClearFeature(PORT_SUSPEND) on downstream port %0d.", PORT_UT), UVM_LOW)
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_CLEAR_FEATURE, FEAT_PORT_SUSPEND,
            16'(PORT_UT), 16'h0000, 1, "ClearFeature_PORT_SUSPEND", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_PORT_SUSPEND");
        #STATUS_SETTLE;

        get_port_status(host_agent_h, usb_cfg, "postClear");
        check_port_status_bit("postClear", BIT_PORT_SUSPEND,   1'b0, "PORT_SUSPEND");
        check_port_status_bit("postClear", BIT_C_PORT_SUSPEND, 1'b1, "C_PORT_SUSPEND");

        // Step 8: acknowledge the change bit, and confirm it is write-1-clear
        // via ClearFeature(C_PORT_SUSPEND) as a host would.
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_CLEAR_FEATURE, FEAT_C_PORT_SUSPEND,
            16'(PORT_UT), 16'h0000, 1, "ClearFeature_C_PORT_SUSPEND", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_SUSPEND");
        #STATUS_SETTLE;

        get_port_status(host_agent_h, usb_cfg, "postAck");
        check_port_status_bit("postAck", BIT_C_PORT_SUSPEND, 1'b0, "C_PORT_SUSPEND");

        // Step 9: the requirement that matters. The device behind the port that
        // was just suspended and resumed must still answer traffic.
        #POST_RESUME_SETTLE;
        post_resume_traffic_check(host_agent_h, usb_cfg);

        #100us;

    endtask

    // -------------------------------------------------------------------------
    // Post-resume traffic check.
    //
    // Re-anchors the VIP on the device at address 2 and issues a standard
    // GetDescriptor(Device), then requires a well-formed 18-byte device
    // descriptor back. Both the length and bDescriptorType are checked: a
    // transfer that ended but returned nothing, or returned a short or wrong
    // descriptor, must not count as the device still working.
    //
    // The anchor is restored to the hub address afterwards so this task leaves
    // the VIP in the state the hub-class steps expect, in case the flow above is
    // ever extended past this point.
    // -------------------------------------------------------------------------
    task post_resume_traffic_check(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        int unsigned nbytes;

        usb_cfg.remote_device_cfg[0].device_address = 7'(DEV_ADDR);
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info(MSG_ID,
            $sformatf("Anchor set to device address %0d for the post-resume traffic check.",
                      DEV_ADDR), UVM_LOW)

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, BREQ_GET_DESCRIPTOR, DESC_DEVICE_W_VALUE,
            16'h0000, DEV_DESC_LEN, DEV_ADDR, "PostResume_GetDescriptor", usb_cfg);
        wait_xfer_done(host_agent_h, "PostResume_GetDescriptor");

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                "postResume: no control transfer item captured, so it could not be confirmed that the device still answers traffic after the port was resumed. This check must not be skipped silently.")
        end
        else begin
            nbytes = last_ctrl_seq_item.payload_byte_count();
            if (nbytes < DEV_DESC_LEN) begin
                `uvm_error(MSG_ID,
                    $sformatf("postResume: GetDescriptor(Device) to address %0d returned %0d payload bytes, expected %0d. The device behind hub port %0d is not answering correctly after ClearFeature(PORT_SUSPEND).",
                              DEV_ADDR, nbytes, DEV_DESC_LEN, PORT_UT))
            end
            else if (last_ctrl_seq_item.payload.data[1] !== DESC_TYPE_DEVICE) begin
                `uvm_error(MSG_ID,
                    $sformatf("postResume: GetDescriptor(Device) to address %0d returned bDescriptorType 0x%02x, expected 0x%02x. The device answered but the descriptor is not a device descriptor.",
                              DEV_ADDR, last_ctrl_seq_item.payload.data[1], DESC_TYPE_DEVICE))
            end
            else begin
                `uvm_info(MSG_ID,
                    $sformatf("postResume: device at address %0d returned a valid %0d-byte device descriptor after the port suspend and resume cycle, so it is still able to receive and answer traffic.",
                              DEV_ADDR, nbytes), UVM_LOW)
            end
        end

        // Leave the anchor where the hub-class steps expect it.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
    endtask

    // -------------------------------------------------------------------------
    // GetPortStatus on the port under test. The response lands in
    // last_ctrl_seq_item, which check_port_status_bit() below reads.
    // On entry the VIP anchor must be 1 (HUB).
    // -------------------------------------------------------------------------
    task get_port_status(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg, string tag);
        string label = {"GetPortStatus_", tag};
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, BREQ_GET_STATUS, 16'h0000,
            16'(PORT_UT), PORT_STATUS_LEN, 1, label, usb_cfg);
        wait_xfer_done(host_agent_h, label);
    endtask

    // -------------------------------------------------------------------------
    // Read one bit out of the last GetPortStatus response and compare it.
    //
    // This is what makes the status half of this test a check rather than a
    // comment. do_control_xfer() has no output handle, so the response is
    // taken from the protected last_ctrl_seq_item populated there; it must be
    // called after the matching get_port_status().
    //
    // GetPortStatus returns 4 bytes little-endian: wPortStatus in bytes 0-1 and
    // wPortChange in bytes 2-3. The concatenation below reproduces the RTL
    // hub_status word, so bit numbers 0..31 can be used directly as documented
    // in the header.
    //
    // A short or missing payload is an error, not a silent skip: treating it as
    // "nothing to compare" is precisely how a check becomes vacuous.
    // -------------------------------------------------------------------------
    function void check_port_status_bit(string tag, int unsigned bit_idx,
                                        bit exp_val, string bit_name);
        bit [31:0] status_word;
        int unsigned nbytes;

        if (last_ctrl_seq_item == null) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: no control transfer item captured, so %s could not be checked. This check must not be skipped silently.",
                          tag, bit_name))
            return;
        end

        nbytes = last_ctrl_seq_item.payload_byte_count();
        if (nbytes < 4) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: GetPortStatus returned %0d payload bytes, expected 4, so %s could not be checked.",
                          tag, nbytes, bit_name))
            return;
        end

        status_word = {last_ctrl_seq_item.payload.data[3],
                       last_ctrl_seq_item.payload.data[2],
                       last_ctrl_seq_item.payload.data[1],
                       last_ctrl_seq_item.payload.data[0]};

        if (status_word[bit_idx] !== exp_val) begin
            `uvm_error(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) is %0b, expected %0b. Full status word 0x%08x.",
                          tag, PORT_UT, bit_idx, bit_name,
                          status_word[bit_idx], exp_val, status_word))
        end
        else begin
            `uvm_info(MSG_ID,
                $sformatf("%s: port %0d status bit %0d (%s) = %0b as expected. Full status word 0x%08x.",
                          tag, PORT_UT, bit_idx, bit_name, exp_val, status_word),
                UVM_LOW)
        end
    endfunction

endclass


`endif // CALIPTRA_SS_USB_HS_DEV_HUB_PORT_SUSPEND_SEQUENCE_SV
