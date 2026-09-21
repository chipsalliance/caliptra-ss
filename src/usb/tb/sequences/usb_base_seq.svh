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
// Shared access layer for USB environment-level sequences: native 32-bit AXI
// transfers, COMBO register accesses through RAL, and 64-bit packet-memory rows.
// Native addresses are byte offsets within the selected target's root map;
// HUB offsets include HUB_BASE_ADDR within COMBO. RAL memory indices are rows,
// not byte offsets. Access helpers use the supplied USER override or resolve a
// fresh randomized value when it is null.
class usb_base_seq extends uvm_sequence;
  `uvm_object_utils(usb_base_seq)
  `uvm_declare_p_sequencer(usb_virtual_sequencer)

  localparam logic [31:0] HUB_BASE_ADDR = 32'(usb_compound_pkg::HUB_BASE_ADDR);

  usb_target_stats_t target_stats[USB_TARGET_COUNT];
  int unsigned ral_memory_writes[USB_TARGET_COUNT];
  int unsigned ral_memory_reads[USB_TARGET_COUNT];

  // Create a sequence with cleared native-access and RAL-memory counters.
  function new(string name = "usb_base_seq");
    super.new(name);
    initialize_target_stats();
  endfunction

  // Fail before sequence traffic starts if the virtual sequencer lacks the
  // register model or any required Avery manager, even for an unused target.
  virtual task pre_start();
    super.pre_start();
    if (p_sequencer == null ||
        p_sequencer.reg_model == null ||
        p_sequencer.combo_sequencer == null ||
        p_sequencer.dev0_memory_sequencer == null ||
        p_sequencer.dev1_csr_sequencer == null ||
        p_sequencer.dev1_memory_sequencer == null) begin
      `uvm_fatal("USB_SEQ", "USB virtual sequencer is missing required RAL or Avery handles")
    end
  endtask

  // Clear accumulated per-target traffic and comparison counts without
  // changing the DUT, register model, or sequencer configuration.
  function void initialize_target_stats();
    foreach (target_stats[target_index]) begin
      target_stats[target_index] = '{default: 0};
      ral_memory_writes[target_index] = 0;
      ral_memory_reads[target_index] = 0;
    end
  endfunction

  // Route a functional target to its Avery manager and require a valid
  // sequencer configuration. HUB and DEV0 CSR share COMBO; others are dedicated.
  protected function aaxi_sequencer sequencer_for(usb_target_e target);
    aaxi_sequencer target_sequencer;

    case (target)
      USB_HUB,
      USB_DEV0_CSR:  target_sequencer = p_sequencer.combo_sequencer;
      USB_DEV0_SRAM: target_sequencer = p_sequencer.dev0_memory_sequencer;
      USB_DEV1_CSR:  target_sequencer = p_sequencer.dev1_csr_sequencer;
      USB_DEV1_SRAM: target_sequencer = p_sequencer.dev1_memory_sequencer;
      default: `uvm_fatal("USB_SEQ", "Invalid functional target")
    endcase
    if (target_sequencer == null) begin
      `uvm_fatal("USB_SEQ", $sformatf("%s Avery sequencer is missing", usb_target_name(target)))
    end
    if (target_sequencer.cfg == null) begin
      `uvm_fatal("USB_SEQ", $sformatf("%s Avery sequencer configuration is missing", usb_target_name(target)))
    end
    return target_sequencer;
  endfunction

  // Assign native traffic a stable AXI ID per manager, rather than a unique ID
  // per request. HUB and DEV0 CSR both use ID 1 on their shared COMBO manager.
  protected function aaxi_id_t transaction_id_for(usb_target_e target);
    case (target)
      USB_HUB,
      USB_DEV0_CSR:  return aaxi_id_t'(1);
      USB_DEV0_SRAM: return aaxi_id_t'(2);
      USB_DEV1_CSR:  return aaxi_id_t'(3);
      USB_DEV1_SRAM: return aaxi_id_t'(4);
      default: begin
        `uvm_fatal("USB_SEQ", "Invalid functional target")
        return '0;
      end
    endcase
  endfunction

  // Convert the selected SRAM's configured depth in 64-bit rows to bytes for
  // native-address bounds checking. Requesting a non-SRAM target is fatal.
  protected function logic [31:0] sram_implemented_bytes(usb_target_e target);
    case (target)
      USB_DEV0_SRAM: return USB_DEV0_RAM_DEPTH * 32'd8;
      USB_DEV1_SRAM: return USB_DEV1_RAM_DEPTH * 32'd8;
      default: begin
        `uvm_fatal("USB_SEQ", "SRAM size requested for a non-SRAM target")
        return '0;
      end
    endcase
  endfunction

  // Find the DEV0 or DEV1 packet-memory abstraction used for RAL row accesses.
  // Reject non-SRAM targets or incomplete models instead of returning null.
  protected function uvm_mem memory_for(usb_target_e target);
    uvm_mem target_memory;

    if (p_sequencer.reg_model == null) begin
      `uvm_fatal("USB_RAL_MEMORY", "RAL model is not configured")
    end
    case (target)
      USB_DEV0_SRAM: begin
        if (p_sequencer.reg_model.dev0_mem == null) begin
          `uvm_fatal("USB_RAL_MEMORY", "DEV0 memory model is not configured")
        end
        if (p_sequencer.reg_model.dev0_mem.packet_mem == null) begin
          `uvm_fatal("USB_RAL_MEMORY", "DEV0 packet memory is not configured")
        end
        target_memory = p_sequencer.reg_model.dev0_mem.packet_mem.m_mem;
      end
      USB_DEV1_SRAM: begin
        if (p_sequencer.reg_model.dev1_mem == null) begin
          `uvm_fatal("USB_RAL_MEMORY", "DEV1 memory model is not configured")
        end
        if (p_sequencer.reg_model.dev1_mem.packet_mem == null) begin
          `uvm_fatal("USB_RAL_MEMORY", "DEV1 packet memory is not configured")
        end
        target_memory = p_sequencer.reg_model.dev1_mem.packet_mem.m_mem;
      end
      default: `uvm_fatal("USB_RAL_MEMORY", "RAL memory requested for a non-SRAM target")
    endcase
    if (target_memory == null) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL memory is not configured", usb_target_name(target)))
    end
    return target_memory;
  endfunction

  // Select the root RAL map that supplies the target's bus base address and
  // frontdoor route. HUB and DEV0 CSR share COMBO; invalid or missing maps fail.
  protected function uvm_reg_map map_for(usb_target_e target);
    uvm_reg_map target_map;

    if (p_sequencer.reg_model == null) begin
      `uvm_fatal("USB_RAL_MAP", "RAL model is not configured")
    end
    case (target)
      USB_HUB,
      USB_DEV0_CSR:  target_map = p_sequencer.reg_model.combo_map;
      USB_DEV0_SRAM: target_map = p_sequencer.reg_model.dev0_mem_map;
      USB_DEV1_CSR:  target_map = p_sequencer.reg_model.dev1_csr_map;
      USB_DEV1_SRAM: target_map = p_sequencer.reg_model.dev1_mem_map;
      default: `uvm_fatal("USB_RAL_MAP", "RAL map requested for an invalid target")
    endcase
    if (target_map == null) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s RAL map is not configured", usb_target_name(target)))
    end
    return target_map;
  endfunction

  // Reject unknown, non-word-aligned, or out-of-range native byte offsets before
  // wrapper address truncation can alias an illegal access onto valid storage.
  // HUB uses its FIFO window within COMBO; CSRs and SRAM use zero-based offsets.
  protected function void check_address(usb_target_e target, logic [31:0] address);
    bit valid_address;

    valid_address = 1'b0;
    case (target)
      USB_HUB:
        valid_address = address >= HUB_BASE_ADDR && address < HUB_BASE_ADDR + USB_HUB_FIFO_SIZE * 4;
      USB_DEV0_CSR,
      USB_DEV1_CSR:
        valid_address = address < 32'h40;
      USB_DEV0_SRAM,
      USB_DEV1_SRAM:
        valid_address = address < sram_implemented_bytes(target);
      default:
        `uvm_fatal("USB_SEQ", "Invalid functional target")
    endcase
    if ($isunknown(address) || address[1:0] !== 2'b00 || !valid_address) begin
      `uvm_fatal("USB_ADDRESS", $sformatf("Illegal local address: target=%s addr=0x%08h", usb_target_name(target), address))
    end
  endfunction

  // Build, but do not send, a single-beat 32-bit AXI4 request using the manager's
  // configuration, fixed target ID, and root-map base plus the local byte offset.
  // Apply one resolved USER value to the request fields; writes pack the least
  // significant byte first and enable all byte lanes. The caller validates address.
  protected function aaxi_master_tr create_transaction(usb_target_e target, logic [31:0] address, bit is_write, logic [31:0] write_data, input usb_axi_user_override user_override = null);
    aaxi_master_tr transaction;
    usb_axi_user_override effective_user;
    aaxi_sequencer target_sequencer;
    uvm_reg_map target_map;

    effective_user = usb_axi_user_override::resolve(user_override);
    target_sequencer = sequencer_for(target);
    target_map = map_for(target);
    transaction = aaxi_master_tr::type_id::create($sformatf("%s_%s", usb_target_name(target), is_write ? "write" : "read"));
    target_sequencer.cfg.cfg_info.copy_master_param(transaction.master_param);
    transaction.slave_param.data_bus_bytes = USB_AXI_DATA_WIDTH / 8;
    transaction.vers = AAXI4;
    transaction.kind = is_write ? AAXI_WRITE : AAXI_READ;
    transaction.addr = target_map.get_base_addr(UVM_NO_HIER) + uvm_reg_addr_t'(address);
    transaction.id = transaction_id_for(target);
    transaction.len = 0;
    transaction.size = 2;
    transaction.burst = AAXI_BURST_INCR;
    transaction.lock = AAXI_ALOCK_NOLOCK;
    transaction.cache = 0;
    transaction.prot = 0;
    transaction.region = 0;
    transaction.awuser = effective_user.value;
    transaction.aruser = effective_user.value;
    transaction.wuser_A = new[1];
    transaction.wuser_A[0] = effective_user.value;
    transaction.uvm_tr_ctrl = AAXI_TRCTRL_BLOCKING;
    if (is_write) begin
      for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
        transaction.data.push_back(write_data[byte_index * 8 +: 8]);
        transaction.strobes.push_back(1'b1);
      end
    end
    return transaction;
  endfunction

  // Submit a prepared native request and wait for Avery completion, failing if
  // USB_TRANSFER_TIMEOUT expires. The supplied bus address and direction label
  // timeout diagnostics; response validation and statistics belong to access().
  protected task execute_transaction(usb_target_e target, logic [31:0] address, bit is_write, aaxi_master_tr transaction);
    aaxi_sequencer target_sequencer;

    target_sequencer = sequencer_for(target);
    // Isolate timeout cancellation from any other children of the caller.
    fork
      begin
        fork
          begin
            start_item(transaction, -1, target_sequencer);
            finish_item(transaction);
            transaction.wait_done();
          end
          begin
            #(USB_TRANSFER_TIMEOUT);
            `uvm_fatal("USB_ACCESS_TIMEOUT", $sformatf("%s %s addr=0x%08h did not complete", usb_target_name(target), is_write ? "write" : "read", address))
          end
        join_any
        disable fork;
      end
    join
  endtask

  // Require one OKAY read response with exactly one bus word of data, then
  // assemble the byte queue into a 32-bit value with byte 0 in bits [7:0].
  // Malformed or unsuccessful responses are fatal and identify the bus address.
  protected function logic [31:0] unpack_read_data(usb_target_e target, logic [31:0] address, aaxi_master_tr transaction);
    logic [31:0] read_data;

    if (transaction.rresp_Q.size() != 1 || transaction.data.size() != USB_AXI_DATA_WIDTH / 8) begin
      `uvm_fatal("USB_RESPONSE", $sformatf("%s read addr=0x%08h returned %0d responses and %0d bytes", usb_target_name(target), address, transaction.rresp_Q.size(), transaction.data.size()))
    end
    if (transaction.rresp_Q[0] !== AAXI_RESP_OKAY) begin
      `uvm_fatal("USB_RESPONSE", $sformatf("%s read addr=0x%08h response=0x%h, expected OKAY", usb_target_name(target), address, transaction.rresp_Q[0]))
    end
    read_data = '0;
    for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
      read_data[byte_index * 8 +: 8] = transaction.data[byte_index];
    end
    return read_data;
  endfunction

  // Centralize a checked native read or write: validate the local byte offset,
  // build and execute a time-limited request, and require an OKAY response.
  // Count successful transfers in target_stats; return read data for reads and
  // zero for writes. This path uses RAL maps for addressing, not RAL read/write.
  protected task access(usb_target_e target, logic [31:0] address, bit is_write, logic [31:0] write_data, output logic [31:0] read_data, input usb_axi_user_override user_override = null);
    aaxi_master_tr transaction;

    check_address(target, address);
    transaction = create_transaction(target, address, is_write, write_data, user_override);
    read_data = '0;
    `uvm_info("USB_ACCESS", $sformatf("Start %s %s offset=0x%08h addr=0x%08h data=0x%08h user=0x%0h timeout=%0t", usb_target_name(target), is_write ? "write" : "read", address, transaction.addr, write_data, is_write ? transaction.awuser : transaction.aruser, USB_TRANSFER_TIMEOUT), UVM_LOW)
    execute_transaction(target, 32'(transaction.addr), is_write, transaction);
    if (is_write) begin
      if (transaction.resp !== AAXI_RESP_OKAY) begin
        `uvm_fatal("USB_RESPONSE", $sformatf("%s write addr=0x%08h response=0x%h, expected OKAY", usb_target_name(target), transaction.addr, transaction.resp))
      end
      target_stats[target].writes++;
    end else begin
      read_data = unpack_read_data(target, 32'(transaction.addr), transaction);
      target_stats[target].reads++;
    end
    `uvm_info("USB_ACCESS", $sformatf("Completed %s %s offset=0x%08h addr=0x%08h data=0x%08h", usb_target_name(target), is_write ? "write" : "read", address, transaction.addr, is_write ? write_data : read_data), UVM_HIGH)
  endtask

  // Write all four bytes at a target-local byte offset through native AXI.
  // access() supplies address, timeout, and response checks and counts the write;
  // this helper does not read back or compare the stored value.
  task write32(usb_target_e target, logic [31:0] address, logic [31:0] write_data, input usb_axi_user_override user_override = null);
    logic [31:0] unused_read_data;

    access(target, address, 1'b1, write_data, unused_read_data, user_override);
  endtask

  // Return one word from a target-local byte offset through native AXI, using
  // access() for validation, timeout handling, response checks, and read counting.
  task read32(usb_target_e target, logic [31:0] address, output logic [31:0] read_data, input usb_axi_user_override user_override = null);
    access(target, address, 1'b0, '0, read_data, user_override);
  endtask

  // Perform one native read and compare only bits selected by comparison_mask
  // against expected_data; the default checks the entire word. A mismatch is
  // fatal. Count a passing comparison in addition to the read; this is not polling.
  task expect32(usb_target_e target, logic [31:0] address, logic [31:0] expected_data, logic [31:0] comparison_mask = 32'hffff_ffff, input usb_axi_user_override user_override = null);
    logic [31:0] actual_data;

    read32(target, address, actual_data, user_override);
    if ((actual_data & comparison_mask) !== (expected_data & comparison_mask)) begin
      `uvm_fatal("USB_DATA", $sformatf("%s addr=0x%08h expected=0x%08h actual=0x%08h mask=0x%08h", usb_target_name(target), address, expected_data, actual_data, comparison_mask))
    end
    target_stats[target].comparisons++;
  endtask

  // Write a register handle through the COMBO RAL frontdoor, retaining INIT's
  // route rather than selecting a map from the handle. Pass resolved USER as
  // the RAL extension and fail on a null handle or unsuccessful status; label
  // identifies diagnostics. The caller provides the timeout; no counters change.
  task ral_write32(string label, uvm_reg register_handle, logic [31:0] data, input usb_axi_user_override user_override = null);
    uvm_status_e status;
    usb_axi_user_override effective_user;
    uvm_reg_map target_map;

    effective_user = usb_axi_user_override::resolve(user_override);
    target_map = map_for(USB_DEV0_CSR);
    if (register_handle == null) begin
      `uvm_fatal("USB_RAL", $sformatf("RAL register handle is missing for %s", label))
    end
    `uvm_info("USB_RAL", $sformatf("Writing %s=0x%08h through combo RAL map", label, data), UVM_HIGH)
    register_handle.write(status, uvm_reg_data_t'(data), UVM_FRONTDOOR, target_map, this, -1, effective_user);
    if (status != UVM_IS_OK) begin
      `uvm_fatal("USB_RAL", $sformatf("RAL write failed for %s data=0x%08h", label, data))
    end
  endtask

  // Read a register handle through the COMBO RAL frontdoor and return its low
  // 32 bits without comparing an expected value. Pass resolved USER as the RAL
  // extension and fail on a null handle or unsuccessful status, identified by
  // label. Like ral_write32(), rely on the caller's timeout and leave counts alone.
  task ral_read32(string label, uvm_reg register_handle, output logic [31:0] data, input usb_axi_user_override user_override = null);
    uvm_status_e status;
    uvm_reg_data_t register_data;
    usb_axi_user_override effective_user;
    uvm_reg_map target_map;

    effective_user = usb_axi_user_override::resolve(user_override);
    target_map = map_for(USB_DEV0_CSR);
    if (register_handle == null) begin
      `uvm_fatal("USB_RAL", $sformatf("RAL register handle is missing for %s", label))
    end
    `uvm_info("USB_RAL", $sformatf("Reading %s through combo RAL map", label), UVM_HIGH)
    register_handle.read(status, register_data, UVM_FRONTDOOR, target_map, this, -1, effective_user);
    if (status != UVM_IS_OK) begin
      `uvm_fatal("USB_RAL", $sformatf("RAL read failed for %s", label))
    end
    data = register_data[31:0];
  endtask

  // Write one DEV0 or DEV1 packet-memory row through its RAL frontdoor. index is
  // a 64-bit row number, not a byte offset; the map splits data into two 32-bit
  // bus accesses using the resolved USER extension. Bound the entire row write
  // by USB_TRANSFER_TIMEOUT and fail on timeout or bad status. Count one
  // successful row in ral_memory_writes, not two native writes in target_stats.
  task ral_memory_write(usb_target_e target, int unsigned index, logic [63:0] data, input usb_axi_user_override user_override = null);
    uvm_status_e status;
    usb_axi_user_override effective_user;
    uvm_mem target_memory;
    uvm_reg_map target_map;
    bit operation_done;

    effective_user = usb_axi_user_override::resolve(user_override);
    target_memory = memory_for(target);
    target_map = map_for(target);
    operation_done = 1'b0;
    fork
      begin
        fork
          begin
            target_memory.write(status, index, uvm_reg_data_t'(data), UVM_FRONTDOOR, target_map, this, -1, effective_user);
            operation_done = 1'b1;
          end
          begin
            #(USB_TRANSFER_TIMEOUT);
          end
        join_any
        disable fork;
      end
    join
    if (!operation_done) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL write index %0d timed out after %0t", usb_target_name(target), index, USB_TRANSFER_TIMEOUT))
    end
    if (status != UVM_IS_OK) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL write index %0d failed with status %s", usb_target_name(target), index, status.name()))
    end
    ral_memory_writes[target]++;
  endtask

  // Return one DEV0 or DEV1 packet-memory row through its RAL frontdoor. index
  // selects a 64-bit row; the map assembles two 32-bit bus reads using the resolved
  // USER extension. Bound the entire operation by USB_TRANSFER_TIMEOUT and fail
  // on timeout or bad status. Count one row in ral_memory_reads without changing
  // target_stats or comparing the returned data against an expected value.
  task ral_memory_read(usb_target_e target, int unsigned index, output logic [63:0] data, input usb_axi_user_override user_override = null);
    uvm_status_e status;
    uvm_reg_data_t read_data;
    usb_axi_user_override effective_user;
    uvm_mem target_memory;
    uvm_reg_map target_map;
    bit operation_done;

    effective_user = usb_axi_user_override::resolve(user_override);
    target_memory = memory_for(target);
    target_map = map_for(target);
    data = '0;
    operation_done = 1'b0;
    fork
      begin
        fork
          begin
            target_memory.read(status, index, read_data, UVM_FRONTDOOR, target_map, this, -1, effective_user);
            operation_done = 1'b1;
          end
          begin
            #(USB_TRANSFER_TIMEOUT);
          end
        join_any
        disable fork;
      end
    join
    if (!operation_done) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL read index %0d timed out after %0t", usb_target_name(target), index, USB_TRANSFER_TIMEOUT))
    end
    if (status != UVM_IS_OK) begin
      `uvm_fatal("USB_RAL_MEMORY", $sformatf("%s RAL read index %0d failed with status %s", usb_target_name(target), index, status.name()))
    end
    data = read_data[63:0];
    ral_memory_reads[target]++;
  endtask
endclass
