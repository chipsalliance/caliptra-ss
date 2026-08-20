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

`ifndef CALIPTRA_SS_USB_HS_HOST_POWERDOWN_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_HOST_POWERDOWN_SEQUENCE_SV

class caliptra_ss_usb_hs_host_powerdown_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_host_powerdown_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)
    function new(string name = "caliptra_ss_usb_hs_host_powerdown_sequence"); super.new(name); endfunction
    virtual task pre_start();
        uvm_phase phase; super.pre_start(); phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null) phase.raise_objection(this);
    endtask
    virtual task post_start();
        uvm_phase phase; phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null) phase.drop_objection(this);
    endtask
    virtual task body();
        svt_usb_agent host_agent_h; uvm_component parent_comp; svt_usb_status shared_status;
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("CALIPTRA_SS_USB_HS_H","Cannot cast to svt_usb_agent")
        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null) `uvm_fatal("CALIPTRA_SS_USB_HS_H","get_shared_status null.")
        fork
            begin: WE wait(shared_status.link_usb_20_state==svt_usb_types::ENABLED);disable RE;end
            begin: RE forever begin #10us `uvm_info("CALIPTRA_SS_USB_HS_H",$sformatf("link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("CALIPTRA_SS_USB_HS_H","HS link ENABLED.",UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_on_sequence s;
            s = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof");
            s.start(p_sequencer.prot_service_sequencer);
        end
        #2us;
        `uvm_info("USB_HS_HPWRDN_SEQ","VBUS off (powerdown)...",UVM_LOW)
        begin
            svt_usb_protocol_service_20_vbus_off_sequence voff;
            voff = svt_usb_protocol_service_20_vbus_off_sequence::type_id::create("voff");
            voff.start(p_sequencer.prot_service_sequencer);
        end
        fork
            begin: WPD wait(shared_status.link_usb_20_state!=svt_usb_types::ENABLED);disable RPD;end
            begin: RPD forever begin #5us `uvm_info("USB_HS_HPWRDN_SEQ",$sformatf("link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_HPWRDN_SEQ","Powered down.",UVM_LOW) #5us;
        begin
            svt_usb_protocol_service_20_vbus_on_sequence von;
            von = svt_usb_protocol_service_20_vbus_on_sequence::type_id::create("von");
            von.start(p_sequencer.prot_service_sequencer);
        end
        fork
            begin: WPU wait(shared_status.link_usb_20_state==svt_usb_types::ENABLED);disable RPU;end
            begin: RPU forever begin #10us `uvm_info("USB_HS_HPWRDN_SEQ",$sformatf("link=%p",shared_status.link_usb_20_state),UVM_LOW); end end
        join
        `uvm_info("USB_HS_HPWRDN_SEQ","HS host powerdown/wakeup PASSED.",UVM_LOW)
        #100us;
        `uvm_info("CALIPTRA_SS_USB_HS_H","caliptra_ss_usb_hs_host_powerdown_sequence complete.",UVM_LOW)
    endtask
endclass

`endif // CALIPTRA_SS_USB_HS_HOST_POWERDOWN_SEQUENCE_SV
