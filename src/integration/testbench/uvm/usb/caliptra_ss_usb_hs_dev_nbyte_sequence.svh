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
// USB High-Speed device NBytes field test sequence.
// Sequence flow:
//   Same as caliptra_ss_usb_hs_dev_bulk_out_sequence: HS link-up, SOF, enumerate,
//   send 512-byte bulk OUT on EP1, allow MCU to verify NBytes residual.
//   Uses 512 bytes (1 HS bulk packet) to stress the NBytes boundary condition.
// =============================================================================

`define USB_HS_DEV_NBYTE_BYTES 512

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

    virtual task body();
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_configuration    get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status       shared_status;
        svt_usb_transfer     bulk_req;
        bit [7:0]            bulk_data[];

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

        // Enumerate.
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,8'h06,16'h0100,16'h0,16'h12,0,"GET_DESC",usb_cfg);
        wait_xfer_done(host_agent_h,"GET_DESC");
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,8'h05,16'h0001,16'h0,16'h0,0,"SET_ADDR",usb_cfg);
        wait_xfer_done(host_agent_h,"SET_ADDR");
        #5us;
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE,svt_usb_types::STANDARD,svt_usb_types::BMREQ_DEVICE,8'h09,16'h0001,16'h0,16'h0,1,"SET_CFG",usb_cfg);
        wait_xfer_done(host_agent_h,"SET_CFG");
        `uvm_info("USB_HS_NBYTE_SEQ","Enumeration done.",UVM_LOW)
        #10us;

        // Send exactly 512 bytes (one HS bulk packet) to stress NBytes handling.
        bulk_data = new[`USB_HS_DEV_NBYTE_BYTES];
        for (int unsigned b = 0; b < `USB_HS_DEV_NBYTE_BYTES; b++)
            bulk_data[b] = b[7:0];

        bulk_req = svt_usb_transfer::type_id::create("bulk_out");
        start_item(bulk_req,-1,p_sequencer.xfer_sequencer);
        bulk_req.cfg = usb_cfg;
        bulk_req.payload.USER_DEFINED_ALGORITHM_wt = 1;
        bulk_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        bulk_req.fix_anchors(0,1,0);
        if (!bulk_req.randomize() with {
                xfer_type == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address == 1;
                payload_intended_byte_count == `USB_HS_DEV_NBYTE_BYTES;
            })
            `uvm_fatal("USB_HS_NBYTE_SEQ","Bulk OUT randomize failed")
        for (int unsigned bi = 0; bi < `USB_HS_DEV_NBYTE_BYTES; bi++)
            bulk_req.payload.data[bi] = bulk_data[bi];
        finish_item(bulk_req,-1);
        wait_xfer_done(host_agent_h,"NBYTE_BULK_OUT");
        #20us;

        `uvm_info("USB_HS_NBYTE_SEQ","HS dev nbyte sequence complete.",UVM_LOW)
    endtask

endclass

`undef USB_HS_DEV_NBYTE_BYTES

`endif // CALIPTRA_SS_USB_HS_DEV_NBYTE_SEQUENCE_SV
