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

`ifndef CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_SEQUENCE_SV

// =============================================================================
// USB ENDPOINT_HALT round trip on the hub interrupt IN endpoint.
//
// Enumerates the hub alone (hub_enum_stepA, no downstream port bring-up and no
// USBDC0 enumeration) and then exercises the USB 2.0 section 9.4.5 / 9.4.3 /
// 9.4.1 endpoint feature round trip against the hub at address 1. The scenario
// is intentionally control transfer only, all four steps run on EP0:
//
//   GET_STATUS(ENDPOINT)    -> 0x0000  (Halt clear at reset)
//   SET_FEATURE(ENDPOINT)   -> arm Halt
//   GET_STATUS(ENDPOINT)    -> 0x0001  (Halt set)
//   CLEAR_FEATURE(ENDPOINT) -> release Halt
//   GET_STATUS(ENDPOINT)    -> 0x0000  (Halt clear again)
//
// Request encoding:
//   bmRequestType = 0x02 / 0x82 (STANDARD, recipient = endpoint)
//   bRequest      = 0x03 SET_FEATURE / 0x01 CLEAR_FEATURE / 0x00 GET_STATUS
//   wValue        = 0x0000 (ENDPOINT_HALT feature selector)
//   wIndex        = 0x0081 (direction IN, endpoint number 1)
//   wLength       = 0 for SET/CLEAR_FEATURE, 2 for GET_STATUS
//
// Why endpoint 1 IN and nothing else (all MEASURED from the hub RTL):
//   usb_ep_config_hub_pkg.p.vhdl declares C_NBPHYSEP = 2 and gives device 0
//   (the hub) exactly one non-control endpoint: EPNB = 1, EPDIR = EP_IN,
//   NON_ISO. So EP1 IN is the only Halt-able endpoint on the hub and
//   wIndex = 0x0081 is the only meaningful index.
//
//   func_epconfig_link maps an IN endpoint to offset 4*EPNB+2 and an OUT
//   endpoint to offset 4*EPNB, and the link array is zero filled. EP1 IN maps
//   to offset 6 -> physical endpoint bit 0, but offset 0 (wIndex = 0x0000,
//   EP0 OUT) also reads back physical bit 0 because of that zero fill. The two
//   indices therefore alias, so this sequence uses 0x0081 exclusively and never
//   touches 0x0000: halting EP0 would kill the control pipe it depends on.
//
//   usb_ep0_hub_descr.m.vhdl admits all three endpoint requests for device 0
//   with wIndex mask 0xFF7E against match 0x0000. The mask polarity is MEASURED
//   from usb_ep0_handler.m.vhdl (var_setup_masked := rdata and setup_bytes):
//   a mask bit of 1 means the byte is compared, 0 means don't-care. wIndex bits
//   0 and 7 are therefore don't-care and 0x0081 is admitted. The wValue mask is
//   0xFFFF against match 0x0000, so only feature selector ENDPOINT_HALT is ever
//   accepted.
//
// Observability (MEASURED):
//   The Halt flop itself is usb_ep_config_handler.reg_ep_stall, a VHDL
//   internal signal with no testbench probe. usb_ep0_handler drives
//   ep_set_stall / ep_clear_stall into that module and reads the state back
//   through epconfig_stall, which it returns as bit 0 of the GET_STATUS data
//   stage. The GET_STATUS checks below are therefore a genuine cross module
//   read of the real flop, not a shadow register. CLEAR_FEATURE additionally
//   asserts reg_ep_toggle_reset, as USB 2.0 mandates for a cleared Halt.
//
//   A packet level proof that the halted endpoint also STALLs an IN token is
//   deliberately NOT attempted here. The hub interrupt IN endpoint is declared
//   with no buffer, so an IN probe does not terminate cleanly and lengthens the
//   run for no additional register coverage.
//
// Address map after hub_enum_stepA (see caliptra_ss_usb_base_sequence.svh):
//   hub -> device address 1, and the VIP anchor is already left at address 1,
//   so no re-anchoring is needed before the control transfers.
// =============================================================================

class caliptra_ss_usb_hs_hub_endpoint_halt_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_hub_endpoint_halt_sequence)

    // USB device address assigned to the hub during enumeration.
    localparam int HUB_ADDR = 1;

    // wIndex of every request below: direction IN, endpoint number 1, the only
    // non-control endpoint of the hub.
    localparam bit [15:0] HUB_INT_WINDEX = 16'h0081;

    // Standard request encodings for recipient = endpoint.
    localparam bit [7:0]  BREQ_GET_STATUS           = 8'h00;
    localparam bit [7:0]  BREQ_CLEAR_FEATURE        = 8'h01;
    localparam bit [7:0]  BREQ_SET_FEATURE          = 8'h03;
    localparam bit [15:0] FEATURE_ENDPOINT_HALT     = 16'h0000;

    // Endpoint status word bit 0 is Halt.
    localparam bit [15:0] EP_STATUS_HALT_CLEAR = 16'h0000;
    localparam bit [15:0] EP_STATUS_HALT_SET   = 16'h0001;

    function new(string name = "caliptra_ss_usb_hs_hub_endpoint_halt_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // SET_FEATURE(ENDPOINT, ENDPOINT_HALT) on the hub interrupt IN endpoint.
    // -------------------------------------------------------------------------
    task set_feature_endpoint_halt(svt_usb_agent         host_agent_h,
                                   svt_usb_configuration usb_cfg,
                                   string                label);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
            .brequest_val         (BREQ_SET_FEATURE),
            .wvalue               (FEATURE_ENDPOINT_HALT),
            .windex               (HUB_INT_WINDEX),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // CLEAR_FEATURE(ENDPOINT, ENDPOINT_HALT) on the hub interrupt IN endpoint.
    // Also resets the endpoint data toggle inside usb_ep_config_handler.
    // -------------------------------------------------------------------------
    task clear_feature_endpoint_halt(svt_usb_agent         host_agent_h,
                                     svt_usb_configuration usb_cfg,
                                     string                label);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
            .brequest_val         (BREQ_CLEAR_FEATURE),
            .wvalue               (FEATURE_ENDPOINT_HALT),
            .windex               (HUB_INT_WINDEX),
            .wlength              (16'h0000),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
    endtask

    // -------------------------------------------------------------------------
    // GET_STATUS(ENDPOINT) on the hub interrupt IN endpoint and compare the
    // returned two byte status word. Bit 0 is the Halt state read back from
    // usb_ep_config_handler through epconfig_stall.
    // -------------------------------------------------------------------------
    task get_endpoint_status(svt_usb_agent         host_agent_h,
                             svt_usb_configuration usb_cfg,
                             bit [15:0]            expected,
                             string                label);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_ENDPOINT),
            .brequest_val         (BREQ_GET_STATUS),
            .wvalue               (16'h0000),
            .windex               (HUB_INT_WINDEX),
            .wlength              (16'h0002),
            .device_addr          (HUB_ADDR),
            .label                (label),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label(label));
        usb_data_check_api.check_get_status(.usb_item(last_ctrl_seq_item),
                                            .device_name("hub_endpoint1_in"),
                                            .expected(expected));
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        `uvm_info("USB_HUB_EP_HALT",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_HUB_EP_HALT",
                "Link never reached ENABLED; aborting hub endpoint halt sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED, then
        // let the bus settle before the first SETUP transfer.
        start_sof_generation();
        #20us;

        // Step 3: Enumerate the hub alone at address 1. The downstream ports
        // are deliberately left un-powered: only the hub endpoints matter here.
        hub_enum_stepA(host_agent_h, usb_cfg);

        // Step 4: Baseline. reg_ep_stall resets to 0, so the endpoint must
        // report Halt clear before anything is set.
        get_endpoint_status(host_agent_h, usb_cfg, EP_STATUS_HALT_CLEAR,
                            "GET_STATUS_EP1IN_baseline");

        // Step 5: Arm the Halt feature on endpoint 1 IN.
        set_feature_endpoint_halt(host_agent_h, usb_cfg,
                                  "SET_FEATURE_EP_HALT_EP1IN");

        // Step 6: The status word must now read Halt set.
        get_endpoint_status(host_agent_h, usb_cfg, EP_STATUS_HALT_SET,
                            "GET_STATUS_EP1IN_halted");

        // Step 7: Release the Halt feature. This also resets the endpoint data
        // toggle, as USB 2.0 requires for a cleared Halt.
        clear_feature_endpoint_halt(host_agent_h, usb_cfg,
                                    "CLEAR_FEATURE_EP_HALT_EP1IN");

        // Step 8: The status word must read Halt clear again.
        get_endpoint_status(host_agent_h, usb_cfg, EP_STATUS_HALT_CLEAR,
                            "GET_STATUS_EP1IN_cleared");

        `uvm_info("USB_HUB_EP_HALT",
            "USB hub endpoint halt sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_ENDPOINT_HALT_SEQUENCE_SV
