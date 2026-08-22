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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_FLOW_CONTROL_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FIFO_FLOW_CONTROL_SEQUENCE_SV

class caliptra_ss_usb_ocp_fifo_flow_control_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    typedef bit [7:0] byte_queue_t[$];

    typedef struct {
        bit          empty;
        bit          full;
        bit [7:0]    region_type;
        bit [31:0]   write_index;
        bit [31:0]   read_index;
        bit [31:0]   fifo_size;
        bit [31:0]   max_transfer_dwords;
    } fifo_status_s;

    typedef enum logic [1:0] {
        FIFO_OCC_EMPTY,
        FIFO_OCC_PARTIAL,
        FIFO_OCC_NEAR_FULL,
        FIFO_OCC_FULL
    } fifo_occupancy_state_e;

    `uvm_object_utils_begin(caliptra_ss_usb_ocp_fifo_flow_control_sequence)
        `uvm_field_enum(ocp_fifo_flow_control_strategy_e, strategy, UVM_DEFAULT)
        `uvm_field_int(cms, UVM_DEFAULT)
        `uvm_field_queue_int(image_bytes, UVM_DEFAULT)
        `uvm_field_int(image_dwords, UVM_DEFAULT)
        `uvm_field_int(poll_delay, UVM_DEFAULT)
        `uvm_field_int(max_polls, UVM_DEFAULT)
        `uvm_field_int(max_retries, UVM_DEFAULT)
        `uvm_field_int(completion_wait, UVM_DEFAULT)
    `uvm_object_utils_end

    ocp_fifo_flow_control_strategy_e strategy;
    bit [7:0]                        cms;
    byte_queue_t                     image_bytes;
    int unsigned                     image_dwords;
    bit [31:0]                       pattern_base;
    time                             poll_delay;
    int unsigned                     max_polls;
    int unsigned                     max_retries;
    time                             completion_wait;

    int unsigned successful_attempts;
    int unsigned rejected_attempts;
    int unsigned observed_naks;
    protected caliptra_ss_usb_nak_monitor_callback nak_callback;

    covergroup fifo_flow_cg with function sample(
        ocp_fifo_flow_control_strategy_e sampled_strategy,
        fifo_occupancy_state_e sampled_occupancy,
        bit sampled_wrap,
        int unsigned sampled_chunk_dwords,
        bit sampled_retry);
        option.per_instance = 1;
        cp_strategy: coverpoint sampled_strategy;
        cp_occupancy: coverpoint sampled_occupancy;
        cp_wrap: coverpoint sampled_wrap;
        cp_chunk_dwords: coverpoint sampled_chunk_dwords {
            bins status_only = {0};
            bins one         = {1};
            bins small_chunk = {[2:4]};
            bins large_chunk = {[5:$]};
        }
        cp_retry: coverpoint sampled_retry;
        strategy_x_occupancy: cross cp_strategy, cp_occupancy;
        strategy_x_retry: cross cp_strategy, cp_retry;
        occupancy_x_wrap: cross cp_occupancy, cp_wrap;
    endgroup

    function new(string name =
            "caliptra_ss_usb_ocp_fifo_flow_control_sequence");
        super.new(name);
        strategy           = FIFO_FLOW_BY_INDICES;
        cms                = 8'h00;
        image_dwords       = 96;
        pattern_base       = 32'hC0DE_0000;
        poll_delay         = 1us;
        max_polls          = 100;
        max_retries        = 10;
        completion_wait    = 500us;
        successful_attempts = 0;
        rejected_attempts   = 0;
        observed_naks       = 0;
        fifo_flow_cg = new();
    endfunction

    protected virtual function void generate_default_image();
        bit [31:0] word;

        if (image_bytes.size() != 0) return;
        for (int unsigned word_index = 0;
             word_index < image_dwords; word_index++) begin
            word = pattern_base | 32'(word_index);
            image_bytes.push_back(word[7:0]);
            image_bytes.push_back(word[15:8]);
            image_bytes.push_back(word[23:16]);
            image_bytes.push_back(word[31:24]);
        end
        // OCP Recovery v1.1 Sec 9.2 permits a non-DWORD-aligned final
        // INDIRECT_FIFO_DATA transfer. The Device advances one DWORD and zero
        // pads the invalid lane.
        if (image_bytes.size() != 0)
            void'(image_bytes.pop_back());
    endfunction

    protected virtual function int unsigned bytes_to_dwords(
        input int unsigned byte_count);
        return (byte_count + 3) / 4;
    endfunction

    protected virtual function int unsigned dwords_to_bytes(
        input int unsigned dword_count);
        return dword_count * 4;
    endfunction

    protected virtual function int unsigned legal_max_chunk_dwords(
        input fifo_status_s status);
        int unsigned usb_limit_dwords;

        usb_limit_dwords = wMaxWrTransferSize / 4;
        if (status.max_transfer_dwords < usb_limit_dwords)
            return status.max_transfer_dwords;
        return usb_limit_dwords;
    endfunction

    protected virtual function int unsigned fifo_occupancy(
        input int unsigned write_index,
        input int unsigned read_index,
        input int unsigned fifo_size);
        if (fifo_size == 0) return 0;
        return (write_index + fifo_size - read_index) % fifo_size;
    endfunction

    protected virtual function int unsigned fifo_space(
        input int unsigned write_index,
        input int unsigned read_index,
        input int unsigned fifo_size);
        if (fifo_size == 0) return 0;
        return (read_index + fifo_size - ((write_index + 1) % fifo_size)) %
               fifo_size;
    endfunction

    protected virtual function fifo_occupancy_state_e occupancy_state(
        input fifo_status_s status);
        int unsigned occupancy;
        int unsigned space;

        occupancy = fifo_occupancy(
            status.write_index, status.read_index, status.fifo_size);
        space = fifo_space(
            status.write_index, status.read_index, status.fifo_size);
        if (status.empty) return FIFO_OCC_EMPTY;
        if (status.full) return FIFO_OCC_FULL;
        if (space <= 1) return FIFO_OCC_NEAR_FULL;
        if (occupancy != 0) return FIFO_OCC_PARTIAL;
        return FIFO_OCC_EMPTY;
    endfunction

    protected virtual function void slice_payload(
        input int unsigned start_dword,
        input int unsigned dword_count,
        ref bit [7:0] payload[$]);
        int unsigned byte_index;

        payload.delete();
        for (int unsigned i = 0;
             (i < dwords_to_bytes(dword_count)) &&
             ((dwords_to_bytes(start_dword) + i) < image_bytes.size());
             i++) begin
            byte_index = dwords_to_bytes(start_dword) + i;
            payload.push_back(image_bytes[byte_index]);
        end
    endfunction

    protected virtual task read_and_check_status(
        output fifo_status_s status,
        input string label);
        bit [7:0] response[$];
        indirect_fifo_status_read(
            response, status.empty, status.full, status.region_type,
            status.write_index, status.read_index, status.fifo_size,
            status.max_transfer_dwords, label);
        if ((status.fifo_size == 0) ||
            (status.max_transfer_dwords == 0)) begin
            `uvm_error("OCP_FIFO_FLOW",
                $sformatf("%s reported FIFO_SIZE=%0d MAX_TRANSFER_SIZE=%0d; both shall be nonzero per OCP Recovery v1.1 Sec 9.2.",
                          label, status.fifo_size,
                          status.max_transfer_dwords))
            return;
        end
        if (status.empty && status.full) begin
            `uvm_error("OCP_FIFO_FLOW",
                $sformatf("%s reports EMPTY and FULL simultaneously.",
                          label))
        end
        fifo_flow_cg.sample(
            strategy, occupancy_state(status), 1'b0, 0, 1'b0);
    endtask

    protected virtual task push_by_indices();
        fifo_status_s status;
        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        int unsigned offset_dwords;
        int unsigned remaining_dwords;
        int unsigned chunk_dwords;
        int unsigned chunk_number;
        bit wrapped;
        bit equality_deviation_reported;

        offset_dwords = 0;
        chunk_number = 0;
        equality_deviation_reported = 1'b0;
        configure_ep0_nak_retry_limit(10000);
        while (offset_dwords < bytes_to_dwords(image_bytes.size())) begin
            read_and_check_status(
                status,
                $sformatf("OCP_FIFO_INDEX_STATUS_%0d", chunk_number));
            remaining_dwords =
                bytes_to_dwords(image_bytes.size()) - offset_dwords;
            chunk_dwords = fifo_space(
                status.write_index, status.read_index, status.fifo_size);
            if (chunk_dwords == 0) begin
                // The implementation can expose W/R equality as FULL. Issue
                // one bounded probe so the test terminates with a precise
                // OCP Recovery v1.1 Sec 8.2.5 compliance verdict instead of
                // waiting forever for index-derived space.
                chunk_dwords = 1;
            end
            if (chunk_dwords > legal_max_chunk_dwords(status))
                chunk_dwords = legal_max_chunk_dwords(status);
            if (chunk_dwords > remaining_dwords)
                chunk_dwords = remaining_dwords;
            slice_payload(offset_dwords, chunk_dwords, payload);
            indirect_fifo_data_try_write(
                payload, result,
                $sformatf("OCP_FIFO_INDEX_DATA_%0d", chunk_number));
            if (result != OCP_XFER_SUCCESS) begin
                rejected_attempts++;
                `uvm_info("OCP_FIFO_FLOW",
                    $sformatf("Index boundary write %0d returned %s as required before WRITE_INDEX equals READ_INDEX.",
                              chunk_number, result.name()),
                    UVM_NONE)
                return;
            end
            successful_attempts++;
            wrapped = (((status.write_index % status.fifo_size) +
                        chunk_dwords) >= status.fifo_size);
            fifo_flow_cg.sample(
                strategy, occupancy_state(status), wrapped,
                chunk_dwords, 1'b0);
            offset_dwords += chunk_dwords;
            if (!equality_deviation_reported &&
                (caliptra_ss_usb_nak_monitor_callback::get_nak_count() == 0) &&
                (((status.write_index + chunk_dwords) %
                   status.fifo_size) == status.read_index)) begin
                equality_deviation_reported = 1'b1;
                `uvm_error("OCP_FIFO_FLOW",
                    "Device accepted a FIFO transfer that advanced WRITE_INDEX equal to READ_INDEX; OCP Recovery v1.1 Sec 8.2.5 requires NACK.")
            end
            chunk_number++;
        end
    endtask

    protected virtual task wait_until_empty_by_flags(
        output fifo_status_s status,
        input int unsigned chunk_number);
        for (int unsigned poll = 0; poll < max_polls; poll++) begin
            read_and_check_status(
                status,
                $sformatf("OCP_FIFO_FLAGS_STATUS_%0d_%0d",
                          chunk_number, poll));
            if ((status.fifo_size != 0) &&
                (status.max_transfer_dwords != 0) &&
                (legal_max_chunk_dwords(status) != 0) &&
                status.empty && !status.full) return;
            #(poll_delay);
        end
        `uvm_fatal("OCP_FIFO_FLOW",
            $sformatf("Status-flag flow control did not reach EMPTY after %0d polls.",
                      max_polls))
    endtask

    protected virtual task push_by_status_flags();
        fifo_status_s status;
        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        int unsigned offset_dwords;
        int unsigned remaining_dwords;
        int unsigned chunk_dwords;
        int unsigned chunk_number;
        int unsigned batch_dwords;
        int unsigned batch_sent;
        bit wrapped;
        bit equality_deviation_reported;

        offset_dwords = 0;
        chunk_number = 0;
        equality_deviation_reported = 1'b0;
        while (offset_dwords < bytes_to_dwords(image_bytes.size())) begin
            wait_until_empty_by_flags(status, chunk_number);
            remaining_dwords =
                bytes_to_dwords(image_bytes.size()) - offset_dwords;
            batch_dwords = remaining_dwords;
            if (batch_dwords > status.fifo_size)
                batch_dwords = status.fifo_size;
            batch_sent = 0;
            while (batch_sent < batch_dwords) begin
                chunk_dwords = legal_max_chunk_dwords(status);
                if (chunk_dwords > (batch_dwords - batch_sent))
                    chunk_dwords = batch_dwords - batch_sent;
                if (chunk_dwords == 0) begin
                    `uvm_fatal("OCP_FIFO_FLOW",
                        "Status-flag flow control could not form a legal chunk.")
                end
                slice_payload(offset_dwords, chunk_dwords, payload);
                indirect_fifo_data_try_write(
                    payload, result,
                    $sformatf("OCP_FIFO_FLAGS_DATA_%0d", chunk_number));
                if (result != OCP_XFER_SUCCESS) begin
                    rejected_attempts++;
                    `uvm_error("OCP_FIFO_FLOW",
                        $sformatf("Status-flag flow-control write %0d returned %s.",
                                  chunk_number, result.name()))
                    return;
                end
                successful_attempts++;
                wrapped = (((status.write_index % status.fifo_size) +
                            batch_sent + chunk_dwords) >= status.fifo_size);
                fifo_flow_cg.sample(
                    strategy, occupancy_state(status), wrapped,
                    chunk_dwords, 1'b0);
                offset_dwords += chunk_dwords;
                batch_sent += chunk_dwords;
                if (!equality_deviation_reported &&
                    (((status.write_index + batch_sent) %
                       status.fifo_size) == status.read_index)) begin
                    equality_deviation_reported = 1'b1;
                    `uvm_error("OCP_FIFO_FLOW",
                        "Status-controlled batch accepted a transfer that advanced WRITE_INDEX equal to READ_INDEX; OCP Recovery v1.1 Sec 8.2.5 requires NACK.")
                end
                chunk_number++;
            end
        end
    endtask

    protected virtual task push_by_usb_nak();
        fifo_status_s status;
        bit [7:0] payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        int unsigned offset_dwords;
        int unsigned remaining_dwords;
        int unsigned chunk_dwords;
        int unsigned chunk_number;
        int unsigned nak_count_before;
        int unsigned nak_count_after;
        bit nak_observed;
        bit wrapped;

        read_and_check_status(status, "OCP_FIFO_NAK_CAPABILITY_STATUS");
        if ((status.fifo_size == 0) ||
            (status.max_transfer_dwords == 0) ||
            (legal_max_chunk_dwords(status) == 0)) return;
        configure_ep0_nak_retry_limit(10000);
        offset_dwords = 0;
        chunk_number = 0;
        while (offset_dwords < bytes_to_dwords(image_bytes.size())) begin
            remaining_dwords =
                bytes_to_dwords(image_bytes.size()) - offset_dwords;
            chunk_dwords = legal_max_chunk_dwords(status);
            if (chunk_dwords > remaining_dwords)
                chunk_dwords = remaining_dwords;
            if (chunk_dwords == 0) begin
                `uvm_fatal("OCP_FIFO_FLOW",
                    "USB non-success flow control could not form a legal chunk.")
            end
            slice_payload(offset_dwords, chunk_dwords, payload);

            nak_count_before =
                caliptra_ss_usb_nak_monitor_callback::get_nak_count();
            indirect_fifo_data_try_write(
                payload, result,
                $sformatf("OCP_FIFO_NAK_DATA_%0d", chunk_number));
            nak_count_after =
                caliptra_ss_usb_nak_monitor_callback::get_nak_count();
            nak_observed = nak_count_after > nak_count_before;
            observed_naks += nak_count_after - nak_count_before;
            if (result != OCP_XFER_SUCCESS) begin
                `uvm_fatal("OCP_FIFO_FLOW",
                    $sformatf("FIFO write %0d ended with %s after %0d observed NAK responses.",
                              chunk_number, result.name(),
                              nak_count_after - nak_count_before))
            end
            successful_attempts++;
            wrapped = (((status.write_index % status.fifo_size) +
                        offset_dwords + chunk_dwords) >= status.fifo_size);
            fifo_flow_cg.sample(
                strategy, occupancy_state(status), wrapped,
                chunk_dwords, nak_observed);
            `uvm_info("OCP_FIFO_FLOW",
                $sformatf("FIFO write %0d completed after observed_naks=%0d.",
                          chunk_number,
                          nak_count_after - nak_count_before),
                UVM_NONE)
            offset_dwords += chunk_dwords;
            if (((offset_dwords % status.fifo_size) == 0) &&
                (offset_dwords < bytes_to_dwords(image_bytes.size()))) begin
                // Let the already-blocked EXT read acquire the shared path
                // before the next DATA transaction begins retrying.
                #(poll_delay);
            end
            chunk_number++;
        end
        if (observed_naks == 0) begin
            `uvm_error("OCP_FIFO_FLOW",
                "USB-NAK flow-control strategy completed without observing required protocol backpressure.")
        end
    endtask

    virtual task push_image();
        case (strategy)
            FIFO_FLOW_BY_INDICES:      push_by_indices();
            FIFO_FLOW_BY_STATUS_FLAGS: push_by_status_flags();
            FIFO_FLOW_BY_USB_NAK:      push_by_usb_nak();
            default: `uvm_fatal("OCP_FIFO_FLOW",
                $sformatf("Unsupported FIFO flow-control strategy %0d.",
                          strategy))
        endcase
    endtask

    protected virtual task wait_for_final_empty();
        fifo_status_s status;
        for (int unsigned poll = 0; poll < max_polls; poll++) begin
            read_and_check_status(
                status, $sformatf("OCP_FIFO_FINAL_EMPTY_%0d", poll));
            if (status.empty && !status.full &&
                (status.write_index == status.read_index)) return;
            #(poll_delay);
        end
        `uvm_fatal("OCP_FIFO_FLOW",
            $sformatf("FIFO did not drain to EMPTY within %0d polls.",
                      max_polls))
    endtask

    protected virtual function void apply_config();
        void'(uvm_config_db#(ocp_fifo_flow_control_strategy_e)::get(
            null, get_full_name(), "strategy", strategy));
        void'(uvm_config_db#(bit [7:0])::get(
            null, get_full_name(), "cms", cms));
        void'(uvm_config_db#(byte_queue_t)::get(
            null, get_full_name(), "image_bytes", image_bytes));
        void'(uvm_config_db#(int unsigned)::get(
            null, get_full_name(), "image_dwords", image_dwords));
        void'(uvm_config_db#(time)::get(
            null, get_full_name(), "poll_delay", poll_delay));
        void'(uvm_config_db#(int unsigned)::get(
            null, get_full_name(), "max_polls", max_polls));
        void'(uvm_config_db#(int unsigned)::get(
            null, get_full_name(), "max_retries", max_retries));
        void'(uvm_config_db#(time)::get(
            null, get_full_name(), "completion_wait", completion_wait));
    endfunction

    virtual task body();
        apply_config();
        generate_default_image();
        successful_attempts = 0;
        rejected_attempts = 0;
        observed_naks = 0;
        `uvm_info("OCP_FIFO_FLOW",
            $sformatf("OCP_FIFO_FLOW_START strategy=%s cms=%0d image_bytes=%0d image_dwords=%0d pattern_base=0x%08h poll_delay=%0t max_polls=%0d max_retries=%0d completion_wait=%0t",
                      strategy.name(), cms, image_bytes.size(),
                      bytes_to_dwords(image_bytes.size()), pattern_base,
                      poll_delay, max_polls, max_retries, completion_wait),
            UVM_NONE)
        initialize_ocp_transport();
        nak_callback =
            caliptra_ss_usb_nak_monitor_callback::type_id::create(
                "nak_callback");
        uvm_callbacks#(
            svt_usb_link_monitor,
            svt_usb_link_monitor_callback)::add(
                host_agent_h.link_mon, nak_callback);
        caliptra_ss_usb_nak_monitor_callback::reset_nak_count();
        recovery_ctrl_write(
            cms, 8'h00, 1'b0, "OCP_FIFO_FLOW_RECOVERY_CTRL");
        if (image_bytes.size() != 0) begin
            indirect_fifo_ctrl_write(
                cms, 1'b1, bytes_to_dwords(image_bytes.size()),
                "OCP_FIFO_FLOW_CTRL");
            push_image();
            wait_for_final_empty();
        end
        publish_transfer_count();
        `uvm_info("OCP_FIFO_FLOW",
            $sformatf("OCP_FIFO_FLOW_SUMMARY strategy=%s image_bytes=%0d image_dwords=%0d pattern_base=0x%08h poll_delay=%0t max_polls=%0d max_retries=%0d completion_wait=%0t successful_attempts=%0d rejected_attempts=%0d observed_naks=%0d transfers=%0d",
                       strategy.name(), image_bytes.size(),
                       bytes_to_dwords(image_bytes.size()),
                       pattern_base, poll_delay, max_polls, max_retries,
                       completion_wait,
                       successful_attempts, rejected_attempts,
                       observed_naks,
                       transfers_issued),
            UVM_NONE)
        `uvm_info("OCP_FIFO_FLOW",
            "Holding the main_phase objection for firmware completion.",
            UVM_NONE)
        #(completion_wait);
        `uvm_error("OCP_FIFO_FLOW",
            $sformatf("Firmware did not end simulation within completion_wait=%0t.",
                      completion_wait))
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_FLOW_CONTROL_SEQUENCE_SV
