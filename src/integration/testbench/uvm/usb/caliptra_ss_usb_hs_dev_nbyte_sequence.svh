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

`ifndef CALIPTRA_SS_USB_HS_DEV_NBYTE_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_NBYTE_SEQUENCE_SV

// =============================================================================
// USB HS device NBytes residual test sequence for the Caliptra SS SVT UVM VIP
// environment.
//
// Sequence flow:
//   1. Wait for HS link ENABLED, start SOF.
//   2. Enumerate the device (GET_DESCRIPTOR, SET_ADDRESS, SET_CONFIGURATION).
//   3. Send 5 successive short bulk OUT packets to EP1 with lengths 1..5 bytes.
//      Payload pattern: byte[j] = j+1 for j = 0..len-1.
//   4. Between packets wait for the MCU to re-arm EP1 (toggle-reset cycle).
//
// The MCU firmware (caliptra_ss_usb_hs_dev_nbyte.c) verifies:
//   - NBytes residual == 32 - i  after each transfer
//   - Buffer address offset advanced by one 64-byte chunk
//   - Received byte pattern matches j+1
//   - FRAME_INT co-asserted with EP1OUT
// =============================================================================

// Number of short-packet iterations (must match USB_NBYTE_ITERATIONS in .c).
`define USB_HS_NBYTE_ITERATIONS 5

// NBytes budget the firmware arms; all packets are shorter than this.
`define USB_HS_NBYTE_BUDGET 32

class caliptra_ss_usb_hs_dev_nbyte_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_nbyte_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_nbyte_sequence");
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

    // Send a standard control transfer and wait for completion.
    task do_control_xfer(
        input bit [7:0]  bm_dir, bm_type, bm_recip, breq,
        input bit [15:0] wval, widx, wlen,
        input int        dev_addr,
        input string     label,
        input svt_usb_configuration usb_cfg = null
    );
        svt_usb_transfer req;
        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        if (!req.randomize() with {
                xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
                device_address == dev_addr;
                setup_data_bmrequesttype_dir       == bm_dir;
                setup_data_bmrequesttype_type      == bm_type;
                setup_data_bmrequesttype_recipient == bm_recip;
                setup_data_brequest == breq;
                setup_data_w_value  == wval;
                setup_data_w_index  == widx;
                setup_data_w_length == wlen;
            })
            `uvm_fatal("USB_HS_NBYTE_SEQ", $sformatf("randomize failed: %s", label))
        finish_item(req, -1);
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_NBYTE_SEQ", $sformatf("xfer done: %s", label), UVM_LOW)
    endtask

    // Send a single short bulk OUT transfer to EP1 with 'nbytes' bytes of
    // payload.  Payload pattern: data[j] = j+1 for j=0..nbytes-1.
    task send_short_bulk_out(
        svt_usb_agent        agent_h,
        svt_usb_configuration usb_cfg,
        int unsigned         nbytes,
        int                  iter
    );
        svt_usb_transfer  bulk_req;
        string            label;

        label = $sformatf("NBYTE_BULK_OUT_ITER%0d", iter);

        bulk_req = svt_usb_transfer::type_id::create(label);
        start_item(bulk_req, -1, p_sequencer.xfer_sequencer);
        bulk_req.cfg = usb_cfg;
        // Use USER_DEFINED_ALGORITHM so we can set each byte explicitly.
        bulk_req.payload.USER_DEFINED_ALGORITHM_wt    = 1;
        bulk_req.payload.TWO_SEED_BASED_ALGORITHM_wt  = 0;
        bulk_req.fix_anchors(0, 1, 0);
        if (!bulk_req.randomize() with {
                xfer_type                    == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address               == 1;
                endpoint_number              == 1;
                payload_intended_byte_count  == nbytes;
            })
            `uvm_fatal("USB_HS_NBYTE_SEQ",
                       $sformatf("Bulk OUT randomize failed (iter %0d, %0d bytes)",
                                 iter, nbytes))

        // Fill payload: byte[j] = j+1 (1-indexed).
        // Firmware checks: ep1out_byte_buf[j] == j+1.
        for (int unsigned j = 0; j < nbytes; j++)
            bulk_req.payload.data[j] = 8'(j + 1);

        `uvm_info("USB_HS_NBYTE_SEQ",
                  $sformatf("Sending short bulk OUT iter %0d: %0d bytes, pattern 0x01..0x%02x",
                            iter, nbytes, nbytes),
                  UVM_LOW)
        finish_item(bulk_req, -1);
        wait_xfer_done(agent_h, label);
    endtask

    virtual task body();
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_configuration    get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status       shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_NBYTE_SEQ", "Cannot cast to svt_usb_agent")
        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_NBYTE_SEQ", "get_shared_status returned null.")
        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_NBYTE_SEQ", "Cannot cast cfg.")

        // Wait for HS link ENABLED.
        fork
            begin: W_EN wait(shared_status.link_usb_20_state==svt_usb_types::ENABLED); disable R_EN; end
            begin: R_EN forever begin #10us `uvm_info("USB_HS_NBYTE_SEQ",
                $sformatf("link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_NBYTE_SEQ","HS ENABLED.",UVM_LOW)

        begin
            svt_usb_protocol_service_20_sof_on_sequence s;
            s = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof");
            s.start(p_sequencer.prot_service_sequencer);
        end
        #20us;

        // --- Enumeration ---
        // GET_DESCRIPTOR (device descriptor, 18 bytes).
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,
                        8'h06,16'h0100,16'h0,16'h12,0,"GET_DESC",usb_cfg);
        wait_xfer_done(host_agent_h,"GET_DESC");

        // Wait for MCU to finish GET_DESCRIPTOR processing and EP1 initial arming
        // before issuing SET_ADDRESS. Without this gap the MCU is still writing
        // EP1 OUT entries when the SET_ADDRESS SETUP arrives, pushing the EP0 IN
        // STATUS phase ZLP past the VIP timeout and causing the transfer to ABORT.
        // 10 us is sufficient: MCU EP1 arming completes ~6.4 us after GET_DESC ends.
        #10us;

        // SET_ADDRESS to 1.
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,
                        8'h05,16'h0001,16'h0,16'h0,0,"SET_ADDR",usb_cfg);
        wait_xfer_done(host_agent_h,"SET_ADDR");
        #5us;
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        // SET_CONFIGURATION 1.
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,
                        8'h09,16'h0001,16'h0,16'h0,1,"SET_CFG",usb_cfg);
        wait_xfer_done(host_agent_h,"SET_CFG");
        `uvm_info("USB_HS_NBYTE_SEQ","Enumeration done.",UVM_LOW)
        #10us;

        // --- Short-packet bulk OUT iterations ---
        // Send 5 successive short packets of 1..5 bytes to EP1.  Between each
        // packet wait long enough for the MCU firmware to process the EP1OUT
        // interrupt, verify the data, and re-arm EP1 with toggle-reset.
        // This mirrors the 5-iteration loop in usb_hs_dev_nbyte.cpp.
        for (int unsigned iter = 1; iter <= `USB_HS_NBYTE_ITERATIONS; iter++) begin
            // Allow time for EP1 to be armed / re-armed by the MCU before
            // submitting the next OUT token.  130 us is required to satisfy
            // three constraints simultaneously:
            //   1. MCU polling latency: MCU takes ~22.5 us to detect Active=0
            //      and re-arm; 130 us >> 22.5 us prevents residual mismatch.
            //   2. FRAME_INT window: HS SOF fires every 125 us; 130 us
            //      guarantees at least one SOF per iteration window so
            //      frame_int_seen is set before the next EP1OUT detection.
            //   3. Host/MCU synchronization: keeps all 5 iterations in lockstep
            //      so the MCU processes each one before the next packet arrives.
            #130us;

            send_short_bulk_out(host_agent_h, usb_cfg, iter, int'(iter));

            `uvm_info("USB_HS_NBYTE_SEQ",
                      $sformatf("Iteration %0d/%0d complete (%0d-byte short packet sent)",
                                iter, `USB_HS_NBYTE_ITERATIONS, iter),
                      UVM_LOW)
        end

        // Allow the MCU to finish all pending verification passes before the
        // test drops its objection. With 5 iterations each taking ~14 us to
        // process and the MCU lagging up to 2 behind the host, 100 us covers
        // the full drain after the last packet is sent.
        #100us;

        `uvm_info("USB_HS_NBYTE_SEQ","HS dev nbyte sequence complete.",UVM_LOW)
    endtask

endclass

`undef USB_HS_NBYTE_ITERATIONS
`undef USB_HS_NBYTE_BUDGET

`endif // CALIPTRA_SS_USB_HS_DEV_NBYTE_SEQUENCE_SV
