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

`ifndef CALIPTRA_SS_USB_HS_HOST_BULK_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HOST_BULK_OUT_SEQUENCE_SV

// =============================================================================
// USB HS host bulk OUT sequence.
//
// DUT role  : USB HOST  -- ip_3515 ATL host controller drives 256B bulk OUT.
// VIP role  : DEVICE/UTMI_IF HS agent receives data.
//
// VIP topology:
//   Single svt_usb_agent (component_type=DEVICE, UTMI_IF, HS) installed as
//   cfg.host_cfg.  The VIP autonomously performs HS chirp from its end:
//     - Detects SE0 from DUT (PR=1), waits tdrst=50us, drives chirp-K
//     - After K-J-K-J-K-J exchange, link reaches RECEIVING_IS (HS idle)
//
// VIP link state progression on DEVICE agent (from SVT b2b_phy example):
//   DISCONNECTED -> DEVICE_ATTACHED -> RESETTING -> RECEIVING_IS (HS)
//
// NOTIFY_USB_TRANSFER_ENDED fires on the DEVICE agent protocol layer when
// the 256B BULK OUT from the DUT ATL is fully received.
//
// Sequence flow:
//   1. Wait for DEVICE agent link RECEIVING_IS (HS idle after chirp).
//      Logs state every 10us for debugging.
//   2. Wait for NOTIFY_USB_TRANSFER_ENDED on the DEVICE agent protocol layer.
//   3. Verify received data pattern: word[i] == i, 256 bytes (64 words).
//   4. Report PASS/FAIL.
// =============================================================================

`define USB_HS_HOST_BULK_WORDS  64     // 256 bytes / 4 bytes per word

// No custom device ACK sequence needed.
// Use SVT built-in svt_usb_device_framework_standard_request_response_virtual_sequence
// (`SVT_USB_DEVICE_FRAMEWORK_RESPONSE_SEQUENCE) which correctly handles both
// CONTROL (calls assemble_transfer_response() after SETUP DATA stage) and
// non-CONTROL (calls assemble_non_ctrl_transfer_response()) transfers.
// This prevents the EP0 SM from getting stuck in SETUP_STAGE.

class caliptra_ss_usb_hs_host_bulk_out_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_host_bulk_out_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_host_bulk_out_sequence");
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
    // body: main sequence
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent        dev_agent_h;
        uvm_component        parent_comp;
        svt_usb_transfer      bulk_out_xfer;
        uvm_object            bulk_out_obj;
        int unsigned          expected_word;
        int unsigned          num_errors;
        int unsigned          num_bytes;

        // -----------------------------------------------------------------------
        // Get the VIP DEVICE agent handle from the sequencer parent.
        // -----------------------------------------------------------------------
        parent_comp = p_sequencer.get_parent();
        if (!$cast(dev_agent_h, parent_comp))
            `uvm_fatal("USB_HS_HOST_BULK_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        if (dev_agent_h.shared_status == null)
            `uvm_fatal("USB_HS_HOST_BULK_SEQ", "dev_agent_h.shared_status is null.")

        // -----------------------------------------------------------------------
        // Step 1: Wait for DEVICE link state RECEIVING_IS (HS idle).
        //
        // After HS chirp completes the DEVICE link SM enters RECEIVING_IS
        // (HS SE0 idle, equivalent to ENABLED on the HOST side).
        // RECEIVING_J is the FS idle state; RECEIVING_IS is the HS idle state.
        // (Reference: SVT b2b_phy attach_bulk_xfers_detach_hs_sequence.sv)
        //
        // Periodic state logging every 10us for debugging.
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_BULK_SEQ",
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
                    `uvm_info("USB_HS_HOST_BULK_SEQ",
                        $sformatf("link_usb_20_state = %s",
                                  dev_agent_h.shared_status.link_usb_20_state.name()),
                        UVM_LOW)
                end
            end
        join

        `uvm_info("USB_HS_HOST_BULK_SEQ",
            $sformatf("HS link idle reached (%s). Ready for ATL bulk OUT.",
                      dev_agent_h.shared_status.link_usb_20_state.name()), UVM_LOW)

        // -----------------------------------------------------------------------
        // Force VIP back to HS after BUS_RESET exit.
        //
        // During ATL port reset the bus transitions SE0->K (ATL SOF SYNC) rather
        // than SE0->J. The VIP bus_reset_state handler sees SE0->K and calls
        // set_speed_to_ls_or_fs_on_reset, which programs PERIPHERAL_FULL_SPEED
        // even though chirp KJ succeeded (chirp programs PERIPHERAL_HI_SPEED at
        // ~714us but the FS fallback fires at ~914us and overwrites it).
        // Reconfiguring the device agent to HS here restores PERIPHERAL_HI_SPEED
        // so the protocol layer can decode HS OUT tokens issued by the ATL.
        // -----------------------------------------------------------------------
        begin
            svt_configuration        base_cfg;
            svt_usb_agent_configuration recfg;
            // Use public get_cfg() API instead of accessing the local 'cfg' member.
            dev_agent_h.get_cfg(base_cfg);
            if (!$cast(recfg, base_cfg.clone()))
                `uvm_fatal("USB_HS_HOST_BULK_SEQ",
                    "Cannot cast base_cfg clone to svt_usb_agent_configuration")
            recfg.local_device_cfg[0].connected_bus_speed = svt_usb_types::HS;
            recfg.local_device_cfg[0].high_speed_capable  = 1'b1;
            dev_agent_h.reconfigure(recfg);
            `uvm_info("USB_HS_HOST_BULK_SEQ",
                "Reconfigured VIP device agent to HS (suppresses FS fallback from BUS_RESET exit).",
                UVM_LOW)
        end

        // -----------------------------------------------------------------------
        // Start the SVT built-in device framework response sequence.
        //
        // svt_usb_device_framework_standard_request_response_virtual_sequence
        // (macro SVT_USB_DEVICE_FRAMEWORK_RESPONSE_SEQUENCE) is the SVT canonical
        // device responder. It runs on the agent's virt_sequencer and:
        //   - For CONTROL transfers: waits for SETUP DATA packet, copies
        //     setup_data_* fields, calls assemble_transfer_response(), then
        //     execute_item(). This advances the EP0 state machine correctly.
        //   - For non-CONTROL transfers: calls assemble_non_ctrl_transfer_response()
        //     then execute_item() to send ACK.
        // Without this, EP0 SM stays in SETUP_STAGE and the DUT host gets
        // "Received Token packet with incorrect PID name : IN" errors.
        // -----------------------------------------------------------------------
        fork
            begin
                svt_usb_device_framework_standard_request_response_virtual_sequence dev_fw_seq;
                dev_fw_seq =
                    svt_usb_device_framework_standard_request_response_virtual_sequence::type_id::create(
                        "dev_fw_seq");
                dev_fw_seq.start(dev_agent_h.virt_sequencer);
            end
        join_none

        // -----------------------------------------------------------------------
        // Step 2: Wait for NOTIFY_USB_TRANSFER_ENDED on the DEVICE agent.
        //
        // The SVT VIP DEVICE agent fires NOTIFY_USB_TRANSFER_ENDED for every
        // completed USB transfer including SET_ADDRESS and SET_CONFIGURATION
        // control transfers issued during USB enumeration in firmware Step 13.
        // Loop until we receive the BULK OUT transfer on EP1, addr=1.
        // Control transfers on EP0 are silently discarded by the loop.
        // -----------------------------------------------------------------------
        `uvm_info("USB_HS_HOST_BULK_SEQ",
            "Waiting for DUT HOST to complete 256B bulk OUT to EP1 (addr=1)...", UVM_LOW)
        do begin
            dev_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger_data(bulk_out_obj);
            if (!$cast(bulk_out_xfer, bulk_out_obj))
                `uvm_fatal("USB_HS_HOST_BULK_SEQ",
                    "Cannot cast NOTIFY_USB_TRANSFER_ENDED data to svt_usb_transfer")
            `uvm_info("USB_HS_HOST_BULK_SEQ",
                $sformatf("Transfer ended: type=%s ep=%0d addr=%0d byte_count=%0d (waiting for BULK_OUT EP1 addr=1)",
                          bulk_out_xfer.xfer_type.name(),
                          bulk_out_xfer.endpoint_number,
                          bulk_out_xfer.device_address,
                          bulk_out_xfer.payload.byte_count), UVM_LOW)
        end while (!(bulk_out_xfer.xfer_type      == svt_usb_transfer::BULK_OUT_TRANSFER &&
                     bulk_out_xfer.endpoint_number == 1 &&
                     bulk_out_xfer.device_address  == 1));
        `uvm_info("USB_HS_HOST_BULK_SEQ",
            $sformatf("BULK OUT transfer received: ep=%0d addr=%0d byte_count=%0d",
                      bulk_out_xfer.endpoint_number,
                      bulk_out_xfer.device_address,
                      bulk_out_xfer.payload.byte_count), UVM_LOW)

        // -----------------------------------------------------------------------
        // Step 3: Verify received data pattern: word[i] = i for i = 0..63.
        // -----------------------------------------------------------------------
        num_bytes  = bulk_out_xfer.payload.byte_count;
        num_errors = 0;

        if (num_bytes != (`USB_HS_HOST_BULK_WORDS * 4)) begin
            `uvm_error("USB_HS_HOST_BULK_SEQ",
                $sformatf("Received %0d bytes, expected %0d (256)",
                          num_bytes, `USB_HS_HOST_BULK_WORDS * 4))
            num_errors++;
        end else begin
            bit [31:0] got_word;
            for (int unsigned w = 0; w < `USB_HS_HOST_BULK_WORDS; w++) begin
                expected_word = w;
                got_word = {bulk_out_xfer.payload.get_byte_val(w*4+3),
                            bulk_out_xfer.payload.get_byte_val(w*4+2),
                            bulk_out_xfer.payload.get_byte_val(w*4+1),
                            bulk_out_xfer.payload.get_byte_val(w*4+0)};
                if (got_word !== expected_word[31:0]) begin
                    `uvm_error("USB_HS_HOST_BULK_SEQ",
                        $sformatf("Data mismatch at word[%0d]: got=0x%08X expected=0x%08X",
                                  w, got_word, expected_word))
                    num_errors++;
                    if (num_errors >= 10) begin
                        `uvm_error("USB_HS_HOST_BULK_SEQ", "Too many errors, stopping check.")
                        break;
                    end
                end
            end
        end

        if (num_errors == 0)
            `uvm_info("USB_HS_HOST_BULK_SEQ",
                "Data verification PASSED: all 256 bytes match pattern word[i]=i.", UVM_LOW)
        else
            `uvm_error("USB_HS_HOST_BULK_SEQ",
                $sformatf("Data verification FAILED: %0d word errors.", num_errors))

        // Allow MCU firmware time to read PTD completion and print result.
        #100us;

        `uvm_info("USB_HS_HOST_BULK_SEQ",
            "caliptra_ss_usb_hs_host_bulk_out_sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_HS_HOST_BULK_WORDS

`endif // CALIPTRA_SS_USB_HS_HOST_BULK_OUT_SEQUENCE_SV
