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

`ifndef CALIPTRA_SS_USB_OCP_RECOVERY_ENV_SV
`define CALIPTRA_SS_USB_OCP_RECOVERY_ENV_SV

// =============================================================================
// caliptra_ss_usb_ocp_recovery_env
//
// Extends caliptra_ss_usb_env. Adds:
//   * caliptra_ss_usb_ocp_scoreboard instance.
//   * Run-phase forever-loop that forwards every completed host-side
//     svt_usb_transfer (the trigger data of host_agent.prot.event_pool
//     "NOTIFY_USB_TRANSFER_ENDED") into a uvm_analysis_port, which is
//     connected to the scoreboard's transfer_imp.
//
// Why a forever-loop forwarder instead of a direct
// host_agent.monitor.<analysis_port> hookup:
//
//   The svt_usb_agent class reference enumerates link / physical-adapter /
//   physical / protocol monitor components but does not expose a publicly
//   documented analysis_port carrying svt_usb_transfer items off
//   host_agent.monitor (the names found in the class ref are constructor
//   methods like new_protocol_monitor, not analysis ports). The
//   canonical published pattern from the VIP example (EX20PHY/
//   usb_20_phy_env.sv:192,385,1168-1196) is exactly this forever-loop
//   forwarder over host_agent.prot.event_pool / NOTIFY_USB_TRANSFER_ENDED,
//   and is reused here.
//
//   TODO: if a direct host_agent.monitor.<analysis_port> is later
//   discovered, replace the forwarder with a direct .connect() call. See
//   research/usb_vip_ocp_recovery_class_xfers.md sec 3.
// =============================================================================
class caliptra_ss_usb_ocp_recovery_env extends caliptra_ss_usb_env;

    `uvm_component_utils(caliptra_ss_usb_ocp_recovery_env)

    caliptra_ss_usb_ocp_scoreboard               scoreboard;
    uvm_analysis_port #(svt_usb_transfer)        host_transfer_observed_port;

    function new(string name = "caliptra_ss_usb_ocp_recovery_env",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);
    extern virtual task          run_phase(uvm_phase phase);

endclass

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_ocp_recovery_env::build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_transfer_observed_port =
        new("host_transfer_observed_port", this);
    scoreboard =
        caliptra_ss_usb_ocp_scoreboard::type_id::create("scoreboard", this);
    // Review M4: republish the shared_cfg at the global wildcard scope so
    // the OCP recovery sequence's lookup at uvm_config_db::get(null, "",
    // "cfg", scfg) hits. The base env::build_phase only sets it under
    // "this" scope, which is invisible to sequences that have no
    // component context. Without this fix get_iface_num() silently
    // returns 0 even if the recovery interface is renumbered.
    if (cfg != null) begin
        uvm_config_db#(caliptra_ss_usb_shared_cfg)::set(null, "*",
            "cfg", cfg);
    end
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_ocp_recovery_env::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    host_transfer_observed_port.connect(scoreboard.transfer_imp);
endfunction

// -----------------------------------------------------------------------------
// run_phase: forever loop forwarding NOTIFY_USB_TRANSFER_ENDED trigger
// data into the analysis port. Pattern is exactly EX20PHY/
// usb_20_phy_env.sv:1168-1196.
// -----------------------------------------------------------------------------
task caliptra_ss_usb_ocp_recovery_env::run_phase(uvm_phase phase);
    uvm_object         trig_obj;
    svt_usb_transfer   trig_xfer;
    svt_usb_transfer   clone_xfer;

    if (host_agent == null) begin
        `uvm_warning("OCPREC_ENV",
            "host_agent is null; scoreboard analysis port will receive nothing.")
        super.run_phase(phase);
        return;
    end

    // Review M5: fork the forwarder so it runs concurrently with whatever
    // super.run_phase() does. uvm_env::run_phase is empty today but any
    // future blocking work in super (delay, wait for reset deassert)
    // would otherwise delay the start of the forwarder and silently drop
    // the first N transfers from the scoreboard.
    //
    // Review M6 (documentation): NOTIFY_USB_TRANSFER_ENDED is a shared
    // uvm_event with multiple waiters (this forwarder AND the sequence's
    // own wait_trigger() in caliptra_ss_usb_ocp_recovery_sequence.svh).
    // Back-to-back triggers issued before all waiters have re-armed can
    // drop samples on either consumer. This forwarder remains the
    // primary scoreboard path; the sequence publishes
    // transfers_issued via uvm_config_db and the scoreboard's
    // report_phase raises UVM_ERROR on a mismatch with the analysis-port
    // observation count, surfacing any dropped samples.
    fork
        super.run_phase(phase);
        begin
            forever begin
                host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
                trig_obj = host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.get_trigger_data();
                if (trig_obj == null) continue;
                if (!$cast(trig_xfer, trig_obj)) continue;
                // Clone first (pattern from VIP example) so the analysis-port
                // subscriber receives a stable snapshot.
                if (!$cast(clone_xfer, trig_xfer.clone())) begin
                    `uvm_warning("OCPREC_ENV",
                        "Could not clone svt_usb_transfer for analysis-port publish.")
                    continue;
                end
                host_transfer_observed_port.write(clone_xfer);
            end
        end
    join
endtask

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_ENV_SV
