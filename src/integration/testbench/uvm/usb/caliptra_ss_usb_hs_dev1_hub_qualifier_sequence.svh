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

// -----------------------------------------------------------------------------
// USBDC1 (device1) variant of caliptra_ss_usb_hub_qualifier_sequence.
// Differences from the USBDC0 source:
//   - enumeration brings up hub downstream port 2 (USBDC1) via
//     enumerate_hub_and_usbdc1() instead of enumerate_hub_and_usbdc0();
//   - the matching firmware is built with -DUSB_DEV_SEL=1 so the shared USB
//     library addresses the USBDC1 register/DMA aperture at 0x2001_0000 /
//     0x2001_0100.
// The GetDeviceQualifier transfer targets the hub (address 1) and is unchanged.
// See claude_md/15_usb_dev1_replication.md.
// -----------------------------------------------------------------------------

`ifndef CALIPTRA_SS_USB_HS_DEV1_HUB_QUALIFIER_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV1_HUB_QUALIFIER_SEQUENCE_SV

// =============================================================================
// USB hub device-qualifier sequence for the hub-composite topology (USBDC1).
//
// Enumerates the hub + USBDC1, then issues GetDeviceQualifier for the hub:
// GET_DESCRIPTOR with wValue=0x0600 (DEVICE_QUALIFIER descriptor, index 0),
// wLength=0x000A (10 bytes). The DEVICE_QUALIFIER descriptor describes the
// device characteristics for the other-than-current speed. Per USB 2.0 spec
// 9.6.2 an HS-capable device answers DEVICE_QUALIFIER at both HS and FS, so
// this transfer is kept for both speeds with no speed gating.
//
// Address map after enumeration (see caliptra_ss_usb_base_sequence.svh):
//   hub  -> device address 1
//   dev1 -> device address 2 (behind hub downstream port 2)
// =============================================================================

class caliptra_ss_usb_hs_dev1_hub_qualifier_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev1_hub_qualifier_sequence)

    // USB device addresses assigned during enumeration.
    localparam int HUB_ADDR  = 1;
    localparam int DEV1_ADDR = 2;

    function new(string name = "caliptra_ss_usb_hs_dev1_hub_qualifier_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Re-anchor the VIP host agent onto the target device address before a
    // control transfer. do_control_xfer() calls fix_anchors(0,0,0), which
    // anchors the transfer to remote_device_cfg[0]; svt_usb_transfer ties
    // device_address to that remote device's configured address. After
    // enumerate_hub_and_usbdc1() the anchor is left at dev1 (address 2), so
    // issuing a transfer WITH-constrained to a different address (e.g. the hub
    // at address 1) makes randomize() fail. Setting the configured address to
    // match the target and reconfiguring keeps the two in agreement.
    // -------------------------------------------------------------------------
    task set_anchor_addr(svt_usb_agent         host_agent_h,
                         svt_usb_configuration usb_cfg,
                         int                   addr);
        usb_cfg.remote_device_cfg[0].device_address = addr[6:0];
        host_agent_h.reconfigure(usb_cfg);
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        `uvm_info("USB_HUB_QUALIFIER",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for the host link to reach ENABLED (bounded wait).
        wait_for_link_enabled(shared_status, "host link");
        if (link_wait_timed_out) begin
            `uvm_error("USB_HUB_QUALIFIER",
                "Link never reached ENABLED; aborting hub_qualifier sequence.")
            return;
        end

        // Step 2: Start SOF generation so the link stays out of SUSPENDED.
        start_sof_generation();

        // Step 3: Small settling delay before the first SETUP transfer.
        #20us;

        // Step 4: Enumerate the hub at address 1 and USBDC1 at address 2.
        enumerate_hub_and_usbdc1(host_agent_h, usb_cfg);

        `uvm_info("USB_HUB_QUALIFIER",
            "Enumeration complete. Issuing GetDeviceQualifier for the hub.",
            UVM_LOW)

        // Step 5: GetDeviceQualifier for the hub. GET_DESCRIPTOR with
        // wValue=0x0600 (DEVICE_QUALIFIER descriptor, index 0), wLength=0x000A
        // (10 bytes). After enumerate_hub_and_usbdc1() the VIP anchor is left
        // at dev1 (address 2), so re-anchor onto the hub (address 1) first;
        // otherwise do_control_xfer()'s device_address WITH-constraint would
        // contradict the anchored remote device's address and randomize() would
        // fail.
        set_anchor_addr(host_agent_h, usb_cfg, HUB_ADDR);
        do_control_xfer(
            .bm_request_type_dir  (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type (svt_usb_types::STANDARD),
            .bm_request_type_recip(svt_usb_types::BMREQ_DEVICE),
            .brequest_val         (8'h06),
            .wvalue               (16'h0600),
            .windex               (16'h0000),
            .wlength              (16'h000A),
            .device_addr          (HUB_ADDR),
            .label                ("GET_DEVICE_QUALIFIER_hub"),
            .usb_cfg              (usb_cfg));
        wait_xfer_done(.agent_h(host_agent_h), .label("GET_DEVICE_QUALIFIER_hub"));

        // Step 6: Check the 10-byte DEVICE_QUALIFIER descriptor returned by
        // the hub against the values in the RTL ROM.
        usb_data_check_api.check_device_qualifier(.usb_item(last_ctrl_seq_item),
                                                  .device_name("hub"));

        `uvm_info("USB_HUB_QUALIFIER",
            "USB hub_qualifier sequence complete.", UVM_LOW)

    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV1_HUB_QUALIFIER_SEQUENCE_SV
