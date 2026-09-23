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

`ifndef CALIPTRA_SS_USB_FS_DEV_BULK_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_BULK_OUT_SEQUENCE_SV

// =============================================================================
// USB Full-Speed device bulk OUT sequence (Hub-Enabled mode).
//
// Sequence flow (matches reference janus_usb_host_bfm.sv hub-aware host
// behavior):
//   1. Wait for HS host link ENABLED (after HS chirp).
//   2. Start SOF generation.
//   3. Short settling delay for MCU firmware post-reset EP0 re-arm.
//   4. Enumerate the HUB itself at address 1 (GET_DESC(8)@0 -> SET_ADDRESS(1)
//      -> GET_DESC(18)/GET_DESC(Cfg,9)/GET_DESC(Cfg,25)/GET_DESC(Hub,9)@1 ->
//      SET_CONFIGURATION(1)), then bring up downstream port 1 (where USBDC0
//      is attached) via hub-class requests (GetPortStatus -> ClearFeature
//      (C_PORT_CONNECTION) -> SetFeature(PORT_RESET) -> ClearFeature
//      (C_PORT_RESET)), then enumerate USBDC0 at address 2 (GET_DESC(8)@0 ->
//      SET_ADDRESS(2) -> GET_DESC(18)/GET_CONFIG/SET_CONFIG/GET_CONFIG@2).
//
//      ROOT CAUSE OF device_response_timeout_check_Dev1_EP0: earlier
//      revisions of this sequence tried to address USBDC0 directly as
//      "device 1" (SET_ADDRESS(1) issued straight after GET_STATUS@addr0,
//      with no hub enumeration/port bring-up at all). Since Hub-Enabled
//      mode is active (firmware sets HUB_EN/HUB_CONNECT), the hub entity
//      itself answers at address 0 pre-enumeration and must be enumerated
//      and have its downstream port explicitly brought up (SetFeature
//      (PORT_RESET) etc.) before the hub HW will ever forward SETUP
//      traffic to USBDC0. Skipping this left USBDC0 completely unreachable
//      -> host_agent.prot device_response_timeout on every subsequent
//      transfer nominally addressed to "device 1".
//   5. Send 1024 bytes of bulk OUT data to EP1 (device address 2, i.e. USBDC0
//      post hub-bring-up).
//      Pattern: 32-bit words 0x00000000, 0x00000001, ..., 0x000000FF
//      (256 words x 4 bytes = 1024 bytes, 16 x 64-byte FS bulk packets).
//
//      SIZE LIMIT: the VIP constraint reasonable_fixed_transfer_size_non_isoc_intr
//      in svt_usb_transfer bounds payload_intended_byte_count to
//      (ep_anchor.max_packet_size << 4). At full speed the EP1 bulk max packet
//      size is 64 B, so the largest legal fixed transfer is 64 * 16 = 1024 B.
//      Requesting 2048 B here made the constraint set unsatisfiable and the
//      randomize() in do_data_xfer() aborted with a UVM_FATAL. Keep this value
//      and USB_FS_BULK_TRANSFER_BYTES in the firmware in lock step; note the
//      HS variant of this test may use a larger value because its max packet
//      size is 512 B.
//   6. Allow MCU firmware time to verify the data.
// =============================================================================

`define USB_FS_DEV_BULK_WORDS 256


class caliptra_ss_usb_fs_dev_bulk_out_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_bulk_out_sequence)

    function new(string name = "caliptra_ss_usb_fs_dev_bulk_out_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      bulk_req;
        bit [7:0]             bulk_data[];
        int unsigned          word_val;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // Step 1: Wait for HS link ENABLED.
        wait_for_link_enabled(shared_status, "HS host link");

        // Step 2: Start SOF generation.
        start_sof_generation();

        // Step 3: Settling delay.
        #20us;

        // Step 4: Enumerate the hub at address 1, bring up downstream port 1,
        // then enumerate USBDC0 at address 2 (base-class steps A -> B -> C).
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg);

        `uvm_info("USB_FS_DEV_BULK_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;

        // Step 5: Send 1024 bytes bulk OUT via EP1 (FS, 64-byte packets x 16)
        // to USBDC0 at address 2.
        // Data pattern: word[i] = i for i = 0..255 (COUNT format from original).

        bulk_data = new[`USB_FS_DEV_BULK_WORDS * 4];
        for (int unsigned w = 0; w < `USB_FS_DEV_BULK_WORDS; w++) begin
            word_val = w;
            bulk_data[w*4 + 0] = word_val[7:0];
            bulk_data[w*4 + 1] = word_val[15:8];
            bulk_data[w*4 + 2] = word_val[23:16];
            bulk_data[w*4 + 3] = word_val[31:24];
        end

        // Issue the bulk OUT via the base-class data-transfer helper. It
        // forks the NOTIFY_USB_TRANSFER_ENDED wait before finish_item, which
        // is required for short bulk transfers - see do_data_xfer() in
        // caliptra_ss_usb_base_sequence.svh.
        do_data_xfer(
            .agent_h            (host_agent_h),
            .usb_cfg            (usb_cfg),
            .xfer_kind          (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr        (2),
            .ep_num             (1),
            .byte_count         (`USB_FS_DEV_BULK_WORDS * 4),
            .ep_anchor_idx      (1),
            .label              ("FS_BULK_OUT_EP1"),
            .req                (bulk_req),
            .obj_name           ("bulk_out_req"),
            .payload_data       (bulk_data),
            .no_zero_length_end (1));

        // Step 6: Allow MCU time to verify.
        #50us;

        `uvm_info("USB_FS_DEV_BULK_SEQ", "HS device bulk OUT sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_FS_DEV_BULK_WORDS

`endif // CALIPTRA_SS_USB_FS_DEV_BULK_OUT_SEQUENCE_SV
