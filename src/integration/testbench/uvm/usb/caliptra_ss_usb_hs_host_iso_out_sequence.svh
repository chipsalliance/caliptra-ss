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

`ifndef CALIPTRA_SS_USB_HS_HOST_ISO_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HOST_ISO_OUT_SEQUENCE_SV

// =============================================================================
// USB HS host isochronous OUT+IN sequence -- 2x OUT then 2x IN.
//
// DUT role  : USB HOST  -- ip_3515 ISO periodic list.
//   Stage 1: DUT sends 1024B ISO OUT to VIP EP1 (2 iterations).
//   Stage 2: DUT sends IN token to VIP EP2; VIP returns 1024B (2 iterations).
//
// VIP role  : DEVICE/SERIAL_IF HS agent.
//   EP0=CONTROL, EP1=ISO OUT 1024B, EP2=ISO IN 1024B.
//
// Sequence flow:
//   1. Wait for DEVICE agent link RECEIVING_IS (HS idle after chirp).
//   2. Reconfigure VIP to HS (suppresses FS fallback from BUS_RESET exit).
//   3. Start SVT built-in framework response sequence with
//      isoch_in_payload_size=1024 (fork/join_none).
//   4. Wait for 2 ISO OUT transfers on EP1 addr=1; verify data each time.
//   5. Wait for 2 ISO IN transfers on EP2 addr=1; backdoor-check SRAM each time.
//   6. Allow firmware time to print result.
// =============================================================================

`define USB_HS_HOST_ISO_WORDS  256    // 1024 bytes / 4 bytes per word

class caliptra_ss_usb_hs_host_iso_out_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_host_iso_out_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_host_iso_out_sequence");
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

    // -------------------------------------------------------------------------
    // wait_iso_out -- loop on NOTIFY_USB_TRANSFER_ENDED until we receive
    //   an ISOCHRONOUS_OUT_TRANSFER on EP1 addr=1.  Control transfers on EP0
    //   are silently discarded.  Returns the matching transfer handle.
    // -------------------------------------------------------------------------
    local task wait_iso_out(
        svt_usb_agent    dev_agent_h,
        int unsigned     iter,
        output svt_usb_transfer xfer_out
    );
        uvm_object   obj;
        svt_usb_transfer t;
        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("Waiting for ISO OUT iter %0d on EP1 addr=1...", iter), UVM_LOW)
        do begin
            dev_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger_data(obj);
            if (!$cast(t, obj))
                `uvm_fatal("USB_HS_HOST_ISO_SEQ",
                    "Cannot cast NOTIFY_USB_TRANSFER_ENDED to svt_usb_transfer (ISO OUT)")
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                $sformatf("Transfer ended: type=%s ep=%0d addr=%0d bytes=%0d",
                          t.xfer_type.name(), t.endpoint_number,
                          t.device_address, t.payload.byte_count), UVM_LOW)
        end while (!(t.xfer_type      == svt_usb_transfer::ISOCHRONOUS_OUT_TRANSFER &&
                     t.endpoint_number == 1 &&
                     t.device_address  == 1));
        xfer_out = t;
        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("ISO OUT iter%0d received: ep=%0d addr=%0d bytes=%0d",
                      iter, t.endpoint_number, t.device_address,
                      t.payload.byte_count), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // check_iso_out_data -- verify 1024-byte OUT payload matches word[i]=i.
    // -------------------------------------------------------------------------
    local function void check_iso_out_data(
        svt_usb_transfer xfer,
        int unsigned     iter
    );
        int unsigned num_errors = 0;
        int unsigned num_bytes  = xfer.payload.byte_count;

        if (num_bytes != (`USB_HS_HOST_ISO_WORDS * 4)) begin
            `uvm_error("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO OUT iter%0d: received %0d bytes, expected 1024",
                          iter, num_bytes))
            return;
        end
        for (int unsigned w = 0; w < `USB_HS_HOST_ISO_WORDS; w++) begin
            bit [31:0] got_word;
            got_word = {xfer.payload.get_byte_val(w*4+3),
                        xfer.payload.get_byte_val(w*4+2),
                        xfer.payload.get_byte_val(w*4+1),
                        xfer.payload.get_byte_val(w*4+0)};
            if (got_word !== w[31:0]) begin
                `uvm_error("USB_HS_HOST_ISO_SEQ",
                    $sformatf("ISO OUT iter%0d word[%0d]: got=0x%08X expected=0x%08X",
                              iter, w, got_word, w))
                num_errors++;
                if (num_errors >= 10) begin
                    `uvm_error("USB_HS_HOST_ISO_SEQ", "Too many errors, stopping check.")
                    return;
                end
            end
        end
        if (num_errors == 0)
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO OUT iter%0d data check PASSED: all 1024 bytes match.", iter),
                UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // wait_iso_in -- loop on NOTIFY_USB_TRANSFER_ENDED until we receive
    //   an ISOCHRONOUS_IN_TRANSFER on EP2 addr=1.  Returns the transfer handle.
    // -------------------------------------------------------------------------
    local task wait_iso_in(
        svt_usb_agent    dev_agent_h,
        int unsigned     iter,
        output svt_usb_transfer xfer_in
    );
        uvm_object   obj;
        svt_usb_transfer t;
        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("Waiting for ISO IN iter %0d on EP2 addr=1...", iter), UVM_LOW)
        do begin
            dev_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger_data(obj);
            if (!$cast(t, obj))
                `uvm_fatal("USB_HS_HOST_ISO_SEQ",
                    "Cannot cast NOTIFY_USB_TRANSFER_ENDED to svt_usb_transfer (ISO IN)")
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                $sformatf("Transfer ended: type=%s ep=%0d addr=%0d bytes=%0d",
                          t.xfer_type.name(), t.endpoint_number,
                          t.device_address, t.payload.byte_count), UVM_LOW)
        end while (!(t.xfer_type      == svt_usb_transfer::ISOCHRONOUS_IN_TRANSFER &&
                     t.endpoint_number == 2 &&
                     t.device_address  == 1));
        xfer_in = t;
        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("ISO IN iter%0d sent: ep=%0d addr=%0d bytes=%0d",
                      iter, t.endpoint_number, t.device_address,
                      t.payload.byte_count), UVM_LOW)
        if (t.payload.byte_count != 1024)
            `uvm_error("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO IN iter%0d payload size mismatch: %0d bytes, expected 1024",
                          iter, t.payload.byte_count))
        else
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO IN iter%0d payload size OK: 1024 bytes.", iter), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // check_iso_in_sram -- backdoor read usb_sram[256..383] and compare
    //   against VIP payload bytes for the ISO IN receive buffer (offset 0x800).
    //   Called after a short wait to allow DMA to settle.
    // -------------------------------------------------------------------------
    local task check_iso_in_sram(
        svt_usb_transfer xfer_in,
        int unsigned     iter
    );
        localparam string SRAM_PATH      = "caliptra_ss_top_tb.usb_sram";
        // ISO IN buffer: word index 256 = byte offset 0x800
        localparam int unsigned ISO_IN_WORD_BASE = 256;
        localparam int unsigned ISO_IN_WORDS     = 128;  // 1024 bytes / 8

        int unsigned in_errs = 0;
        logic [63:0] sram_word;
        byte         vip_byte;
        byte         sram_byte;

        // Allow DUT DMA time to finish writing all ISO IN data to SRAM.
        #50us;

        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("ISO IN iter%0d SRAM backdoor check (SRAM[0x800..0xBFF] vs VIP payload)...",
                      iter), UVM_LOW)

        for (int unsigned w = 0; w < ISO_IN_WORDS; w++) begin
            string hdl_path;
            hdl_path = $sformatf("%s[%0d]", SRAM_PATH, ISO_IN_WORD_BASE + w);
            if (!uvm_hdl_read(hdl_path, sram_word)) begin
                `uvm_error("USB_HS_HOST_ISO_SEQ",
                    $sformatf("uvm_hdl_read FAILED for path: %s", hdl_path))
                in_errs++;
                break;
            end
            for (int unsigned b = 0; b < 8; b++) begin
                int unsigned byte_idx;
                byte_idx  = w * 8 + b;
                vip_byte  = xfer_in.payload.get_byte_val(byte_idx);
                sram_byte = sram_word[b*8 +: 8];
                if (sram_byte !== vip_byte) begin
                    `uvm_error("USB_HS_HOST_ISO_SEQ",
                        $sformatf("ISO IN iter%0d byte[%0d]: SRAM=0x%02X VIP=0x%02X (word[%0d] bits[%0d:%0d])",
                                  iter, byte_idx, sram_byte, vip_byte,
                                  ISO_IN_WORD_BASE+w, b*8+7, b*8))
                    in_errs++;
                    if (in_errs >= 10) begin
                        `uvm_error("USB_HS_HOST_ISO_SEQ",
                            $sformatf("ISO IN iter%0d: too many errors, stopping check.", iter))
                        break;
                    end
                end
            end
            if (in_errs >= 10) break;
        end

        if (in_errs == 0)
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO IN iter%0d SRAM backdoor check PASSED: all 1024 bytes match.",
                          iter), UVM_LOW)
        else
            `uvm_error("USB_HS_HOST_ISO_SEQ",
                $sformatf("ISO IN iter%0d SRAM backdoor check FAILED: %0d byte errors.",
                          iter, in_errs))
    endtask

    // -------------------------------------------------------------------------
    // body: main sequence
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent        dev_agent_h;
        uvm_component        parent_comp;
        svt_usb_transfer     iso_out_xfer;
        svt_usb_transfer     iso_in_xfer;

        // -----------------------------------------------------------------------
        // Get the VIP DEVICE agent handle from the sequencer parent.
        // -----------------------------------------------------------------------
        parent_comp = p_sequencer.get_parent();
        if (!$cast(dev_agent_h, parent_comp))
            `uvm_fatal("USB_HS_HOST_ISO_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        if (dev_agent_h.shared_status == null)
            `uvm_fatal("USB_HS_HOST_ISO_SEQ", "dev_agent_h.shared_status is null.")

        // -----------------------------------------------------------------------
        // Step 1: Wait for DEVICE link state RECEIVING_IS (HS idle).
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("Waiting for HS link RECEIVING_IS (current=%s)...",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)
        fork
            begin: WAIT_HS_IDLE
                wait ((dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_IS) ||
                      (dev_agent_h.shared_status.link_usb_20_state ==
                                        svt_usb_types::RECEIVING_J));
                disable REPORT_STATE;
            end
            begin: REPORT_STATE
                forever begin
                    #10us;
                    `uvm_info("USB_HS_HOST_ISO_SEQ",
                        $sformatf("link_usb_20_state = %s",
                                  dev_agent_h.shared_status.link_usb_20_state.name()),
                        UVM_LOW)
                end
            end
        join

        `uvm_info("USB_HS_HOST_ISO_SEQ",
            $sformatf("HS link idle (%s). Ready for ATL enum + ISO OUT/IN.",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 2: Force VIP back to HS after BUS_RESET exit.
        // -----------------------------------------------------------------------
        begin
            svt_configuration        base_cfg;
            svt_usb_agent_configuration recfg;
            dev_agent_h.get_cfg(base_cfg);
            if (!$cast(recfg, base_cfg.clone()))
                `uvm_fatal("USB_HS_HOST_ISO_SEQ",
                    "Cannot cast base_cfg clone to svt_usb_agent_configuration")
            recfg.local_device_cfg[0].connected_bus_speed = svt_usb_types::HS;
            recfg.local_device_cfg[0].high_speed_capable  = 1'b1;
            dev_agent_h.reconfigure(recfg);
            `uvm_info("USB_HS_HOST_ISO_SEQ",
                "Reconfigured VIP device agent to HS.", UVM_LOW)
        end

        // -----------------------------------------------------------------------
        // Step 3: Start SVT built-in device framework response sequence.
        //   isoch_in_payload_size=1024 makes the VIP return 1024B for each
        //   IN token from the DUT HOST (both ISO IN iterations).
        // -----------------------------------------------------------------------
        fork
            begin
                svt_usb_device_framework_standard_request_response_virtual_sequence dev_fw_seq;
                dev_fw_seq =
                    svt_usb_device_framework_standard_request_response_virtual_sequence::type_id::create(
                        "dev_fw_seq");
                dev_fw_seq.isoch_in_payload_size = 1024;
                dev_fw_seq.start(dev_agent_h.virt_sequencer);
            end
        join_none

        // -----------------------------------------------------------------------
        // Step 4: Wait for 2 ISO OUT transfers on EP1 addr=1 and verify data.
        //   Control transfers on EP0 (SET_CONFIGURATION) are silently discarded.
        // -----------------------------------------------------------------------
        wait_iso_out(dev_agent_h, 1, iso_out_xfer);
        check_iso_out_data(iso_out_xfer, 1);

        wait_iso_out(dev_agent_h, 2, iso_out_xfer);
        check_iso_out_data(iso_out_xfer, 2);

        `uvm_info("USB_HS_HOST_ISO_SEQ",
            "Both ISO OUT iterations received and verified.", UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 5: Wait for 2 ISO IN transfers on EP2 addr=1.
        //   After each, backdoor-read USB SRAM at offset 0x800 (word 256..383)
        //   and compare against the VIP payload that was sent.
        // -----------------------------------------------------------------------
        wait_iso_in(dev_agent_h, 1, iso_in_xfer);
        check_iso_in_sram(iso_in_xfer, 1);

        wait_iso_in(dev_agent_h, 2, iso_in_xfer);
        check_iso_in_sram(iso_in_xfer, 2);

        `uvm_info("USB_HS_HOST_ISO_SEQ",
            "Both ISO IN iterations received and SRAM-verified.", UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 6: Allow firmware time to read PTD completion and print result.
        // -----------------------------------------------------------------------
        #200us;

        `uvm_info("USB_HS_HOST_ISO_SEQ",
            "caliptra_ss_usb_hs_host_iso_out_sequence complete (2x ISO OUT + 2x ISO IN).",
            UVM_LOW)
    endtask

endclass

`undef USB_HS_HOST_ISO_WORDS

`endif // CALIPTRA_SS_USB_HS_HOST_ISO_OUT_SEQUENCE_SV
