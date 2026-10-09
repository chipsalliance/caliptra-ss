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
//
// DEV0 endpoint utilities for usb_base_seq. This file is included inside the
// usb_base_seq class body and is not compiled on its own.
//
// Every routine addresses an endpoint through a usb_endpoint_cfg resolved from
// the environment, never a literal index, so the endpoint layout can be
// reordered or extended in usb_env_cfg without editing any sequence. Endpoint
// list words use the usb_ep_entry_t layout declared in usb_tb_pkg.

  // ---------------------------------------------------------------------------
  // Endpoint-list entry encoding and decoding
  // ---------------------------------------------------------------------------

  // Encode one DEV0 endpoint-list word from ownership, stall, byte-count, and
  // 64-byte-aligned packet-buffer fields. Values the hardware field cannot hold
  // are fatal rather than silently truncated.
  function usb_ep_entry_t endpoint_entry(bit active, bit stall, int unsigned byte_count, logic [31:0] buffer_offset);
    usb_ep_entry_t entry;

    if (byte_count >= (1 << $bits(entry.nbytes))) begin
      `uvm_fatal("USB_EP", $sformatf("Byte count %0d does not fit the %0d-bit NBytes field", byte_count, $bits(entry.nbytes)))
    end
    if (buffer_offset[5:0] !== 6'h0 || (buffer_offset >> 6) >= (1 << $bits(entry.buffer_offset))) begin
      `uvm_fatal("USB_EP", $sformatf("Buffer offset 0x%08h is not a 64-byte-aligned address the entry can encode", buffer_offset))
    end
    entry = '0;
    entry.active = active;
    entry.stall = stall;
    entry.nbytes = byte_count;
    entry.buffer_offset = buffer_offset >> 6;
    return entry;
  endfunction

  // Packet-memory byte offset of the buffer an entry points at.
  function logic [31:0] entry_buffer_byte_offset(usb_ep_entry_t entry);
    return 32'(entry.buffer_offset) << 6;
  endfunction

  // Fail if a packet-memory buffer would overlap the DEV0 endpoint list.
  // Buffer offsets are relative to DATABUFSTART, which the bench keeps at 0.
  function void check_buffer_clear_of_endpoint_list(string label, logic [31:0] buffer_offset, int unsigned byte_count);
    longint unsigned list_start;
    longint unsigned list_end;

    list_start = endpoint_list_base();
    list_end = list_start + p_sequencer.cfg.endpoint_list_bytes();
    if (buffer_offset < list_end && 64'(buffer_offset) + byte_count > list_start) begin
      `uvm_fatal("USB_EP", $sformatf("%s buffer [0x%08h, +%0d) overlaps the endpoint list [0x%08h, 0x%08h)", label, buffer_offset, byte_count, list_start, list_end))
    end
  endfunction

  // Decoded one-line view of an entry for diagnostics.
  function string describe_entry(usb_ep_entry_t entry);
    return $sformatf("0x%08h (active=%0b disabled=%0b stall=%0b nbytes=%0d buffer=0x%03h)", entry, entry.active, entry.disabled, entry.stall, entry.nbytes, entry_buffer_byte_offset(entry));
  endfunction

  // ---------------------------------------------------------------------------
  // Endpoint resolution
  // ---------------------------------------------------------------------------

  // Resolve an endpoint by protocol identity through the environment
  // configuration. A sequence never names an anchor or physical index directly.
  function usb_endpoint_cfg get_endpoint(int unsigned ep_number, usb_direction_e direction);
    if (p_sequencer == null || p_sequencer.cfg == null) begin
      `uvm_fatal("USB_EP", "The USB environment configuration is unavailable, so endpoints cannot be resolved")
    end
    return p_sequencer.cfg.get_endpoint(ep_number, direction);
  endfunction

  // ---------------------------------------------------------------------------
  // Endpoint-list access
  // ---------------------------------------------------------------------------

  // For EP0 OUT, buffer_select 1 addresses the SETUP entry; for generic
  // endpoints it addresses the second buffer.
  function logic [31:0] endpoint_entry_address(usb_endpoint_cfg endpoint, int unsigned buffer_select = 0);
    return endpoint_list_base() + endpoint.entry_offset(buffer_select);
  endfunction

  task write_endpoint_entry(usb_endpoint_cfg endpoint, usb_ep_entry_t entry, int unsigned buffer_select = 0);
    write32(USB_DEV0_SRAM, endpoint_entry_address(endpoint, buffer_select), entry);
  endtask

  task read_endpoint_entry(usb_endpoint_cfg endpoint, output usb_ep_entry_t entry, input int unsigned buffer_select = 0);
    logic [31:0] word;

    read32(USB_DEV0_SRAM, endpoint_entry_address(endpoint, buffer_select), word);
    entry = word;
  endtask

  // Hand the endpoint to hardware over the given buffer and byte count, and
  // return the entry that was written so a caller can compare against it.
  task arm_endpoint(usb_endpoint_cfg endpoint, int unsigned byte_count, logic [31:0] buffer_offset, output usb_ep_entry_t entry, input int unsigned buffer_select = 0);
    entry = endpoint_entry(1'b1, 1'b0, byte_count, buffer_offset);
    entry.ep_type = endpoint.transfer_type inside {
      USB_TRANSFER_TYPE_INTERRUPT,
      USB_TRANSFER_TYPE_ISOCHRONOUS
    };
    write_endpoint_entry(endpoint, entry, buffer_select);
    `uvm_info("USB_EP", $sformatf("Armed %s buffer %0d: entry=%s", endpoint.convert2string(), buffer_select, describe_entry(entry)), UVM_LOW)
  endtask

  // Fill a packet-memory buffer with a repeating sentinel so a later comparison
  // can prove every byte was overwritten by real traffic. Bytes past
  // byte_count in a partial final word keep their contents.
  task fill_endpoint_buffer(logic [31:0] buffer_offset, int unsigned byte_count, logic [31:0] fill_word);
    for (int unsigned offset = 0; offset < byte_count; offset += 4) begin
      write_sram_bytes(USB_DEV0_SRAM, buffer_offset + offset, fill_word, byte_count - offset);
    end
    `uvm_info("USB_EP", $sformatf("Filled %0d bytes at buffer 0x%03h with 0x%08h", byte_count, buffer_offset, fill_word), UVM_HIGH)
  endtask

  // ---------------------------------------------------------------------------
  // Per-endpoint interrupt and skip control
  // ---------------------------------------------------------------------------

  // INTSTAT places endpoint status at the physical index for every endpoint,
  // but the generated RAL names fields only through EP5IN, so the bit is taken
  // from the endpoint configuration rather than looked up by field name.
  function logic [31:0] endpoint_intstat_mask(usb_endpoint_cfg endpoint);
    return endpoint.csr_bit_mask();
  endfunction

  // Add an endpoint to the enabled interrupt set without disturbing the
  // enables an earlier stage established.
  task enable_endpoint_interrupt(usb_endpoint_cfg endpoint);
    logic [31:0] interrupt_enable_value;
    logic [31:0] endpoint_enable_bit;

    endpoint_enable_bit = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.INTEN.EP_INT_EN, endpoint.csr_bit_mask());
    ral_read32("INTEN", p_sequencer.reg_model.combo.dev0_csr.INTEN, interrupt_enable_value);
    interrupt_enable_value |= endpoint_enable_bit;
    ral_write32("INTEN", p_sequencer.reg_model.combo.dev0_csr.INTEN, interrupt_enable_value);
    `uvm_info("USB_EP", $sformatf("Enabled the interrupt for %s: INTEN=0x%08h", endpoint.convert2string(), interrupt_enable_value), UVM_LOW)
  endtask

  // Clear only this endpoint's write-one-to-clear status bit.
  task clear_endpoint_interrupt(usb_endpoint_cfg endpoint);
    ral_write32("INTSTAT", p_sequencer.reg_model.combo.dev0_csr.INTSTAT, endpoint_intstat_mask(endpoint));
  endtask

  // Ask the DMA to abandon the endpoint's current entry. Hardware owns the
  // request until its writeback completes, so the bit is not expected to read
  // back as written.
  task request_endpoint_skip(usb_endpoint_cfg endpoint);
    logic [31:0] skip_mask;

    skip_mask = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.EPSKIP.SKIP, endpoint.csr_bit_mask());
    ral_write32("EPSKIP", p_sequencer.reg_model.combo.dev0_csr.EPSKIP, skip_mask);
    `uvm_info("USB_EP", $sformatf("Requested a skip for %s: EPSKIP=0x%08h", endpoint.convert2string(), skip_mask), UVM_LOW)
  endtask

  // ---------------------------------------------------------------------------
  // Bounded CSR polling
  // ---------------------------------------------------------------------------

  // Poll one DEV0 CSR until the masked bits reach want_set, reporting progress
  // so a stalled wait is visible in the log long before it times out. A timeout
  // is fatal and reports the last value read, so the failure identifies the
  // condition that was never met rather than a downstream symptom.
  task poll_csr_bits(
    string label,
    uvm_reg register_handle,
    logic [31:0] mask,
    bit want_set,
    time timeout,
    output logic [31:0] final_value,
    input time poll_interval = EP_POLL_INTERVAL,
    input time progress_interval = EP_PROGRESS_REPORT_INTERVAL
  );
    realtime poll_deadline;
    realtime next_progress_report;
    bit satisfied;

    satisfied = 1'b0;
    final_value = 32'h0;
    poll_deadline = $realtime + timeout;
    next_progress_report = $realtime + progress_interval;
    `uvm_info("USB_EP", $sformatf("Waiting up to %0t for %s (mask=0x%08h expected=%0b)", timeout, label, mask, want_set), UVM_LOW)

    // Bound reads and pacing as well as loop iterations. The outer process
    // confines cancellation to this poll, not the caller's other activity.
    fork
      begin
        fork
          begin
            while (!satisfied && (usb_time_ps($realtime) < usb_time_ps(poll_deadline))) begin
              ral_read32(label, register_handle, final_value);
              if (usb_time_ps($realtime) >= usb_time_ps(poll_deadline)) break;
              if ((|(final_value & mask)) === want_set) begin
                satisfied = 1'b1;
              end else begin
                if ($realtime >= next_progress_report) begin
                  `uvm_info("USB_EP", $sformatf("Still waiting for %s: value=0x%08h elapsed=%0t", label, final_value, timeout - (poll_deadline - $realtime)), UVM_LOW)
                  next_progress_report = $realtime + progress_interval;
                end
                #(poll_interval);
              end
            end
          end
          begin
            #(timeout);
          end
        join_any
        disable fork;
      end
    join

    if (!satisfied) begin
      `uvm_fatal("USB_EP", $sformatf("%s was not satisfied within %0t; mask=0x%08h expected=%0b last value=0x%08h", label, timeout, mask, want_set, final_value))
    end
  endtask

  // Wait for hardware to retire a skip request by self-clearing the bit.
  task wait_for_endpoint_skip_clear(
    usb_endpoint_cfg endpoint,
    time timeout,
    input time poll_interval = EP_POLL_INTERVAL,
    input time progress_interval = EP_PROGRESS_REPORT_INTERVAL
  );
    logic [31:0] skip_mask;
    logic [31:0] skip_status;

    skip_mask = ral_field_value(p_sequencer.reg_model.combo.dev0_csr.EPSKIP.SKIP, endpoint.csr_bit_mask());
    poll_csr_bits(
      $sformatf("EPSKIP self-clear for %s", endpoint.convert2string()),
      p_sequencer.reg_model.combo.dev0_csr.EPSKIP,
      skip_mask,
      1'b0,
      timeout,
      skip_status,
      poll_interval,
      progress_interval
    );
  endtask

  // Wait for an endpoint to report activity, then clear its status so a later
  // wait observes only the next event.
  task wait_for_endpoint_interrupt(
    usb_endpoint_cfg endpoint,
    time timeout,
    input time poll_interval = EP_POLL_INTERVAL,
    input time progress_interval = EP_PROGRESS_REPORT_INTERVAL
  );
    logic [31:0] interrupt_status;

    poll_csr_bits(
      $sformatf("INTSTAT.%s for %s", endpoint.short_name(), endpoint.convert2string()),
      p_sequencer.reg_model.combo.dev0_csr.INTSTAT,
      endpoint_intstat_mask(endpoint),
      1'b1,
      timeout,
      interrupt_status,
      poll_interval,
      progress_interval
    );
    clear_endpoint_interrupt(endpoint);
  endtask

  // Require the endpoint's entry to match an expected word exactly, reporting
  // the decoded fields so a mismatch does not need manual bit extraction.
  task check_endpoint_entry_writeback(usb_endpoint_cfg endpoint, usb_ep_entry_t expected_entry, string check_label, input int unsigned buffer_select = 0);
    usb_ep_entry_t observed_entry;

    read_endpoint_entry(endpoint, observed_entry, buffer_select);
    if (observed_entry !== expected_entry) begin
      `uvm_fatal("USB_EP", $sformatf("%s for %s: observed %s, expected %s", check_label, endpoint.convert2string(), describe_entry(observed_entry), describe_entry(expected_entry)))
    end
  endtask
