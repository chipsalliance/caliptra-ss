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

`ifndef CALIPTRA_SS_USB_OCP_ARBITER_CHECKER_SV
`define CALIPTRA_SS_USB_OCP_ARBITER_CHECKER_SV

// Source-independent checker for OCP Recovery EP0 ownership. Sequences bracket
// one effective owner class per generation using begin_observation() and
// finish_observation(). Multiple claimed transfers are allowed in one window
// so a read-only target can be followed by a claimed semantic marker.
class caliptra_ss_usb_ocp_arbiter_checker extends uvm_component;

    `uvm_component_utils(caliptra_ss_usb_ocp_arbiter_checker)

    localparam int unsigned USB_SETUP_SRAM_WORD_ADDRESS = 9'h020;
    localparam int unsigned SNAPSHOT_FIELD_COUNT = 18;
    localparam logic [31:0] USB_EP0_INTSTAT_MASK = 32'h0000_0003;

    // Exclude write-one-to-clear change indicators from the stable
    // DEVCMDSTAT comparison. Address, enable, SETUP, IntOnNAK, connection,
    // suspend, speed, VBUS, and PHY-test fields remain checked.
    localparam logic [31:0] USB_DEVCMDSTAT_STABLE_MASK =
        32'hF8FF_FFFF;

    uvm_analysis_imp #(
        svt_usb_transfer,
        caliptra_ss_usb_ocp_arbiter_checker) transfer_imp;

    caliptra_ss_usb_ocp_arbiter_packet_callback packet_callback;

    protected virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
    protected caliptra_ss_usb_shared_cfg shared_cfg;
    protected svt_usb_transfer observed_transfers[$];
    protected logic [31:0] baseline_fields[0:SNAPSHOT_FIELD_COUNT-1];
    protected bit observation_active;
    protected bit path_disabled;
    protected logic [15:0] active_generation;
    protected int unsigned windows_checked;
    protected int unsigned claimed_windows_checked;
    protected int unsigned unclaimed_windows_checked;

    function new(
        string name = "caliptra_ss_usb_ocp_arbiter_checker",
        uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        transfer_imp = new("transfer_imp", this);
        packet_callback =
            caliptra_ss_usb_ocp_arbiter_packet_callback::type_id::create(
                "packet_callback");

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_fatal("OCP_ARB_CHECK",
                "usb_legacy_ep0_observer_if not found in config_db")
        end
        if (!uvm_config_db#(caliptra_ss_usb_shared_cfg)::get(
                null, "", "cfg", shared_cfg)) begin
            `uvm_fatal("OCP_ARB_CHECK",
                "caliptra_ss_usb_shared_cfg not found in config_db")
        end

        observation_active = 1'b0;
        path_disabled = 1'b0;
        active_generation = '0;
        windows_checked = 0;
        claimed_windows_checked = 0;
        unclaimed_windows_checked = 0;
    endfunction

    function void write(input svt_usb_transfer transfer);
        svt_usb_transfer clone;

        if (!observation_active || (transfer == null)) begin
            return;
        end
        if (!$cast(clone, transfer.clone())) begin
            `uvm_error("OCP_ARB_CHECK",
                "Could not clone observed USB transfer.")
            return;
        end
        observed_transfers.push_back(clone);
    endfunction

    protected virtual function bit is_claim_candidate(
        input svt_usb_transfer transfer);

        if ((transfer == null) ||
            (transfer.xfer_type !=
                svt_usb_transfer::CONTROL_TRANSFER)) begin
            return 1'b0;
        end

        return
            (transfer.setup_data_bmrequesttype_type ==
                svt_usb_types::CLASS) &&
            (transfer.setup_data_bmrequesttype_recipient ==
                svt_usb_types::BMREQ_INTERFACE) &&
            (transfer.setup_data_brequest == OCP_BREQUEST_XFER) &&
            (transfer.setup_data_w_index ==
                {8'h00, 8'(shared_cfg.ocp_recovery_iface_num)});
    endfunction

    protected virtual function logic [63:0] expected_setup_line(
        input svt_usb_transfer transfer);

        logic [7:0] bm_request_type;
        logic [31:0] setup_word0;
        logic [31:0] setup_word1;

        bm_request_type = {
            1'(transfer.setup_data_bmrequesttype_dir),
            2'(transfer.setup_data_bmrequesttype_type),
            5'(transfer.setup_data_bmrequesttype_recipient)
        };
        setup_word0 = {
            transfer.setup_data_w_value,
            transfer.setup_data_brequest,
            bm_request_type
        };
        setup_word1 = {
            transfer.setup_data_w_length,
            transfer.setup_data_w_index
        };
        return {setup_word1, setup_word0};
    endfunction

    protected virtual function logic [63:0] observed_setup_line(
        output logic [7:0] observed_byte_coverage);
        logic [63:0] result;

        observed_byte_coverage = '0;
        result = {
            baseline_fields[
                observer_vif.SNAPSHOT_FIELD_SETUP_WORD1],
            baseline_fields[
                observer_vif.SNAPSHOT_FIELD_SETUP_WORD0]
        };

        for (int unsigned write_index = 0;
             write_index < observer_vif.write_count();
             write_index++) begin
            logic [8:0] write_word_address;
            logic [63:0] write_data;
            logic [7:0] write_byte_enable;

            write_word_address =
                observer_vif.get_write_word_address(write_index);
            write_data = observer_vif.get_write_data(write_index);
            write_byte_enable =
                observer_vif.get_write_byte_enable(write_index);
            if (write_word_address !=
                    USB_SETUP_SRAM_WORD_ADDRESS) begin
                continue;
            end
            for (int unsigned byte_index = 0;
                 byte_index < 8;
                 byte_index++) begin
                if (write_byte_enable[byte_index]) begin
                    result[(byte_index * 8) +: 8] =
                        write_data[(byte_index * 8) +: 8];
                    observed_byte_coverage[byte_index] = 1'b1;
                end
            end
        end
        return result;
    endfunction

    protected virtual function void check_field_unchanged(
        input int unsigned field_index,
        input string field_name);

        logic [31:0] post_value;
        post_value = observer_vif.get_snapshot_field(field_index);
        if (post_value !== baseline_fields[field_index]) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("%s changed 0x%08h -> 0x%08h during claimed transfer window.",
                          field_name,
                          baseline_fields[field_index],
                          post_value))
        end
    endfunction

    protected virtual function void check_counter_unchanged(
        input int unsigned field_index,
        input string counter_name);
        check_field_unchanged(field_index, counter_name);
    endfunction

    protected virtual function void check_claimed_window();
        logic [31:0] baseline_devcmdstat;
        logic [31:0] post_devcmdstat;
        logic [31:0] baseline_intstat;
        logic [31:0] post_intstat;

        if (observer_vif.write_count() != 0) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Claimed transfer window produced %0d legacy USB SRAM writes.",
                          observer_vif.write_count()))
        end

        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_SETUP_WORD0,
            "Legacy SETUP SRAM word 0");
        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_SETUP_WORD1,
            "Legacy SETUP SRAM word 1");
        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_OUT_DESC,
            "Legacy EP0 OUT descriptor");
        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_SETUP_DESC,
            "Legacy EP0 SETUP descriptor");
        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_IN_DESC,
            "Legacy EP0 IN descriptor");
        check_field_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_RSVD_DESC,
            "Legacy EP0 reserved descriptor");

        baseline_devcmdstat = baseline_fields[
            observer_vif.SNAPSHOT_FIELD_DEVCMDSTAT];
        post_devcmdstat = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_DEVCMDSTAT);
        if ((post_devcmdstat & USB_DEVCMDSTAT_STABLE_MASK) !==
            (baseline_devcmdstat & USB_DEVCMDSTAT_STABLE_MASK)) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Stable DEVCMDSTAT fields changed 0x%08h -> 0x%08h during claimed transfer window.",
                          baseline_devcmdstat, post_devcmdstat))
        end

        baseline_intstat = baseline_fields[
            observer_vif.SNAPSHOT_FIELD_INTSTAT];
        post_intstat = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_INTSTAT);
        if ((post_intstat & USB_EP0_INTSTAT_MASK) !==
            (baseline_intstat & USB_EP0_INTSTAT_MASK)) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Legacy EP0 INTSTAT changed 0x%08h -> 0x%08h during claimed transfer window.",
                          baseline_intstat, post_intstat))
        end

        check_counter_unchanged(
            observer_vif.SNAPSHOT_FIELD_TRANSFERS,
            "Legacy transfer-dispatch count");
        check_counter_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_IRQ_COUNT,
            "Legacy EP0 interrupt count");
        check_counter_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_OUT_COUNT,
            "Legacy EP0 OUT interrupt count");
        check_counter_unchanged(
            observer_vif.SNAPSHOT_FIELD_EP0_IN_COUNT,
            "Legacy EP0 IN interrupt count");
        check_counter_unchanged(
            observer_vif.SNAPSHOT_FIELD_DISPATCH_COUNT,
            "Legacy SETUP-dispatch count");

        claimed_windows_checked++;
    endfunction

    protected virtual function void check_unclaimed_window();
        svt_usb_transfer last_transfer;
        logic [63:0] expected_setup;
        logic [63:0] actual_setup;
        logic [7:0] setup_byte_coverage;
        logic [31:0] baseline_dispatch;
        logic [31:0] post_dispatch;
        logic [31:0] baseline_out_irq;
        logic [31:0] post_out_irq;

        if (observed_transfers.size() != 1) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf({"Unclaimed observation windows require exactly one ",
                           "completed transfer; observed %0d."},
                          observed_transfers.size()))
            return;
        end
        last_transfer = observed_transfers[
            observed_transfers.size() - 1];
        expected_setup = expected_setup_line(last_transfer);
        actual_setup = observed_setup_line(setup_byte_coverage);

        if (observer_vif.write_count() == 0) begin
            `uvm_error("OCP_ARB_CHECK",
                "Unclaimed transfer window produced no legacy USB SRAM writes.")
        end
        if (setup_byte_coverage != 8'hFF) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf({"Legacy SETUP SRAM write coverage was 0x%02h; ",
                           "all eight host SETUP bytes must reach the legacy path."},
                          setup_byte_coverage))
        end
        if (actual_setup !== expected_setup) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Legacy SETUP SRAM mismatch: expected 0x%016h got 0x%016h.",
                          expected_setup, actual_setup))
        end

        baseline_dispatch = baseline_fields[
            observer_vif.SNAPSHOT_FIELD_DISPATCH_COUNT];
        post_dispatch = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_DISPATCH_COUNT);
        if ((post_dispatch - baseline_dispatch) != 32'd1) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Legacy SETUP dispatch advanced by %0d; expected exactly one.",
                          post_dispatch - baseline_dispatch))
        end

        baseline_out_irq = baseline_fields[
            observer_vif.SNAPSHOT_FIELD_EP0_OUT_COUNT];
        post_out_irq = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_EP0_OUT_COUNT);
        if ((post_out_irq - baseline_out_irq) != 32'd1) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Legacy EP0 OUT interrupt count advanced by %0d; expected exactly one.",
                          post_out_irq - baseline_out_irq))
        end

        unclaimed_windows_checked++;
    endfunction

    task begin_observation(
        input  logic [15:0] generation,
        input  bit          disable_recovery_path,
        input  time         timeout,
        output bit          ready);

        if (observation_active) begin
            `uvm_fatal("OCP_ARB_CHECK",
                "begin_observation called while another window is active.")
        end

        observer_vif.receive_snapshot(
            observer_vif.SNAPSHOT_STATE_BASELINE,
            generation,
            timeout,
            ready);
        if (!ready) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Baseline snapshot generation %0d was not received.",
                          generation))
            return;
        end

        for (int unsigned field_index = 0;
             field_index < SNAPSHOT_FIELD_COUNT;
             field_index++) begin
            baseline_fields[field_index] =
                observer_vif.get_snapshot_field(field_index);
        end

        observed_transfers.delete();
        active_generation = generation;
        path_disabled = disable_recovery_path;
        ready = observer_vif.start_window(generation);
        observation_active = ready;
        if (ready) begin
            packet_callback.start_window(generation);
        end
    endtask

    task finish_observation(
        input  logic [15:0] generation,
        input  time         timeout,
        output bit          complete);

        bit first_effective_claimed;
        logic [31:0] baseline_publish_sequence;
        logic [31:0] post_publish_sequence;
        logic [31:0] post_snapshot_version;

        complete = 1'b0;
        if (!observation_active ||
            (generation != active_generation)) begin
            `uvm_error("OCP_ARB_CHECK",
                "finish_observation does not match the active generation.")
            return;
        end

        observer_vif.receive_snapshot(
            observer_vif.SNAPSHOT_STATE_POST,
            generation,
            timeout,
            complete);
        observer_vif.stop_window();
        packet_callback.stop_window();
        observation_active = 1'b0;
        if (!complete) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Post snapshot generation %0d was not received.",
                          generation))
            return;
        end

        baseline_publish_sequence = baseline_fields[
            observer_vif.SNAPSHOT_FIELD_PUBLISH_SEQUENCE];
        post_publish_sequence = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_PUBLISH_SEQUENCE);
        post_snapshot_version = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_VERSION);
        if (baseline_fields[observer_vif.SNAPSHOT_FIELD_VERSION] !==
                observer_vif.SNAPSHOT_VERSION ||
            post_snapshot_version !== observer_vif.SNAPSHOT_VERSION) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf({"Unsupported legacy EP0 snapshot version: ",
                           "baseline=%0d post=%0d expected=%0d."},
                          baseline_fields[
                              observer_vif.SNAPSHOT_FIELD_VERSION],
                          post_snapshot_version,
                          observer_vif.SNAPSHOT_VERSION))
            return;
        end
        if (post_publish_sequence !==
                (baseline_publish_sequence + 32'd1)) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf({"Post snapshot sequence %0d is not the immediate ",
                           "successor of baseline sequence %0d."},
                          post_publish_sequence,
                          baseline_publish_sequence))
            return;
        end

        if (observed_transfers.size() == 0) begin
            `uvm_error("OCP_ARB_CHECK",
                "Observation window contained no completed USB transfer.")
            return;
        end

        first_effective_claimed =
            is_claim_candidate(observed_transfers[0]) &&
            !path_disabled;
        foreach (observed_transfers[transfer_index]) begin
            bit effective_claimed;
            effective_claimed =
                is_claim_candidate(
                    observed_transfers[transfer_index]) &&
                !path_disabled;
            if (effective_claimed != first_effective_claimed) begin
                `uvm_error("OCP_ARB_CHECK",
                    {"Observation window mixed effective legacy and recovery ",
                     "owners. Bracket each owner class in a separate generation."})
                return;
            end
        end

        if (first_effective_claimed) begin
            check_claimed_window();
        end else begin
            check_unclaimed_window();
        end
        windows_checked++;

        `uvm_info("OCP_ARB_CHECK",
            $sformatf({"Generation %0d checked as %s: transfers=%0d ",
                       "packets=%0d SRAM_writes=%0d."},
                      generation,
                      first_effective_claimed ? "CLAIMED" : "UNCLAIMED",
                      observed_transfers.size(),
                      packet_callback.packet_count(),
                      observer_vif.write_count()),
            UVM_NONE)
    endtask

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        if (observation_active) begin
            `uvm_error("OCP_ARB_CHECK",
                $sformatf("Observation generation %0d was not finished.",
                          active_generation))
        end
        `uvm_info("OCP_ARB_CHECK",
            $sformatf("Arbiter isolation summary: windows=%0d claimed=%0d unclaimed=%0d",
                      windows_checked,
                      claimed_windows_checked,
                      unclaimed_windows_checked),
            UVM_NONE)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_ARBITER_CHECKER_SV
