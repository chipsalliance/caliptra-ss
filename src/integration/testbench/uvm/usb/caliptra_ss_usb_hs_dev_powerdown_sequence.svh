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

`ifndef CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV

// =============================================================================
// USB HS device power-down sequence.
// This (no analog PHY probing) sequence
// verifies link-level behavior: HS connected, VBUS removed (power-down),
// link leaves ENABLED, VBUS restored, link re-established.
// =============================================================================
class caliptra_ss_usb_hs_dev_powerdown_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_powerdown_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_powerdown_sequence");
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

    virtual task body();
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_usb_status       shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_PWRDN_SEQ","Cannot cast to svt_usb_agent")
        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_PWRDN_SEQ","get_shared_status returned null.")

        // Wait for HS link ENABLED.
        fork
            begin: WE wait(shared_status.link_usb_20_state==svt_usb_types::ENABLED);disable RE;end
            begin: RE forever begin #10us `uvm_info("USB_HS_PWRDN_SEQ",
                $sformatf("link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","HS ENABLED.",UVM_LOW)

        begin
            svt_usb_protocol_service_20_sof_on_sequence s;
            s = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof");
            s.start(p_sequencer.prot_service_sequencer);
        end
        #2us;

        // Power down - VBUS off.
        `uvm_info("USB_HS_PWRDN_SEQ","Powering down (VBUS off)...",UVM_LOW)
        begin
            svt_usb_protocol_service_20_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_protocol_service_20_vbus_off_sequence::type_id::create("voff");
            vbus_off.start(p_sequencer.prot_service_sequencer);
        end

        // Wait link to leave ENABLED.
        fork
            begin: WD wait(shared_status.link_usb_20_state!=svt_usb_types::ENABLED);disable RD;end
            begin: RD forever begin #5us `uvm_info("USB_HS_PWRDN_SEQ",
                $sformatf("powerdown link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","Link powered down.",UVM_LOW)
        #5us;

        // Power up - VBUS on.
        `uvm_info("USB_HS_PWRDN_SEQ","Powering up (VBUS on)...",UVM_LOW)
        begin
            svt_usb_protocol_service_20_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_protocol_service_20_vbus_on_sequence::type_id::create("von");
            vbus_on.start(p_sequencer.prot_service_sequencer);
        end

        // Wait for link re-establishment.
        fork
            begin: WR wait(shared_status.link_usb_20_state==svt_usb_types::ENABLED);disable RR;end
            begin: RR forever begin #10us `uvm_info("USB_HS_PWRDN_SEQ",
                $sformatf("powerup link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","HS link re-established after power-up. Test PASSED.",UVM_LOW)
        #10us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
