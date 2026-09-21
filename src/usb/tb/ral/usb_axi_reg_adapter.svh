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
// Bridge the USB unitbench's UVM RAL accesses to native Avery AXI transactions.
// Included by usb_tb_pkg.sv, this file supplies the adapter and completion
// sequence used by usb_env for each of its four independent manager ports.
// Each bus operation is one full 32-bit word; wider RAL memory accesses are
// split by the register maps before reaching this adapter.

// Supply the legacy item end-event notification needed by the RAL path.
class usb_axi_ral_parent_sequence extends uvm_sequence;
  `uvm_object_utils(usb_axi_ral_parent_sequence)

  // Construct the parent-sequence template installed on each RAL adapter.
  function new(string name = "usb_axi_ral_parent_sequence");
    super.new(name);
  endfunction

  // Complete sequencer execution before publishing the item's RAL end event.
  virtual task finish_item(uvm_sequence_item item, int set_priority = -1);
    super.finish_item(item, set_priority);
    // Bridge sequencer completion to the legacy RAL end-event handshake.
    item.end_event.trigger();
  endtask
endclass

// Translate full-word RAL requests and in-place Avery results for one AXI port.
class usb_axi_reg_adapter extends aaxi_uvm_mem_adapter;
  `uvm_object_utils(usb_axi_reg_adapter)

  // usb_env binds the port's sequencer and assigns its fixed transaction ID.
  aaxi_sequencer manager_sequencer;
  aaxi_id_t transaction_id;

  // Select full-word, in-place-response operation and the RAL completion hook.
  function new(string name = "usb_axi_reg_adapter");
    super.new(name);
    // Partial-byte RAL transfers are outside this bench's access contract.
    supports_byte_enable = 1'b0;
    // Avery returns completion/data in the original item, not a separate item.
    provides_responses = 1'b0;
    parent_sequence = usb_axi_ral_parent_sequence::type_id::create("ral_parent_sequence");
  endfunction

  // Allocate a blocking Avery request using the bound manager's bus settings.
  // Reject missing configuration or a transfer wider/narrower than one word.
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    aaxi_master_tr transaction;
    usb_axi_user_override user_override;
    uvm_reg_item reg_item;
    bit is_write;

    if (manager_sequencer == null || manager_sequencer.cfg == null) begin
      `uvm_fatal("USB_RAL_ADAPTER", $sformatf("%s has no configured Avery manager sequencer", get_name()))
    end
    if (rw.n_bits != USB_AXI_DATA_WIDTH) begin
      `uvm_fatal("USB_RAL_ADAPTER", $sformatf("%s received %0d-bit access; expected one %0d-bit AXI word", get_name(), rw.n_bits, USB_AXI_DATA_WIDTH))
    end

    reg_item = get_item();
    if (reg_item == null) begin
      `uvm_fatal("USB_RAL_ADAPTER", "RAL item is unavailable during bus transaction conversion")
    end
    user_override = usb_axi_user_override::resolve(reg_item.extension);

    is_write = rw.kind == UVM_WRITE;
    transaction = aaxi_master_tr::type_id::create(is_write ? "ral_write" : "ral_read");
    // Inherit manager parameters before setting this access's explicit shape.
    manager_sequencer.cfg.cfg_info.copy_master_param(transaction.master_param);
    transaction.slave_param.data_bus_bytes = USB_AXI_DATA_WIDTH / 8;
    transaction.vers = AAXI4;
    transaction.kind = is_write ? AAXI_WRITE : AAXI_READ;
    transaction.addr = rw.addr;
    transaction.id = transaction_id;
    // AXI encodes beat count minus one and log2(bytes per beat): one 4-byte beat.
    transaction.len = 0;
    transaction.size = 2;
    transaction.burst = AAXI_BURST_INCR;
    transaction.lock = AAXI_ALOCK_NOLOCK;
    transaction.cache = 0;
    transaction.prot = 0;
    transaction.region = 0;
    // Use one request USER value for the address and write-data channels.
    transaction.awuser = user_override.value;
    transaction.aruser = user_override.value;
    transaction.wuser_A = new[1];
    transaction.wuser_A[0] = user_override.value;
    transaction.uvm_tr_ctrl = AAXI_TRCTRL_BLOCKING;

    if (is_write) begin
      // Avery stores data by byte; pack low byte first and enable every lane.
      for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
        transaction.data.push_back(rw.data[byte_index * 8 +: 8]);
        transaction.strobes.push_back(1'b1);
      end
    end

    `uvm_info(
      "USB_RAL_ADAPTER",
      $sformatf(
        "%s converted RAL %s addr=0x%08h data=0x%08h user=0x%0h",
        get_name(),
        is_write ? "write" : "read",
        rw.addr,
        rw.data[31:0],
        user_override.value
      ),
      UVM_HIGH
    )
    return transaction;
  endfunction

  // Decode the completed request in place and return its RAL data/status.
  // Malformed reads and non-OKAY responses must not appear as successful reads.
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    aaxi_master_tr transaction;
    logic [31:0] completion_data;

    if (!$cast(transaction, bus_item)) begin
      `uvm_fatal("USB_RAL_ADAPTER", "Avery response item is not an aaxi_master_tr")
    end

    rw.kind = transaction.kind == AAXI_WRITE ? UVM_WRITE : UVM_READ;
    rw.addr = transaction.addr;
    rw.data = '0;
    rw.n_bits = USB_AXI_DATA_WIDTH;
    rw.byte_en = '1;
    rw.status = UVM_IS_OK;

    if (rw.kind == UVM_WRITE) begin
      // Writes have one response; read responses are carried in rresp_Q below.
      if (transaction.resp !== AAXI_RESP_OKAY) begin
        rw.status = UVM_NOT_OK;
      end
    end else begin
      // Validate the single-beat result before indexing response/data queues.
      if (transaction.rresp_Q.size() != 1 || transaction.data.size() != USB_AXI_DATA_WIDTH / 8) begin
        `uvm_error("USB_RAL_ADAPTER", $sformatf("Read addr=0x%08h returned %0d responses and %0d bytes", transaction.addr, transaction.rresp_Q.size(), transaction.data.size()))
        rw.status = UVM_NOT_OK;
        return;
      end
      if (transaction.rresp_Q[0] !== AAXI_RESP_OKAY) begin
        rw.status = UVM_NOT_OK;
      end
      // Reverse reg2bus's little-endian byte packing into the RAL word.
      for (int unsigned byte_index = 0; byte_index < USB_AXI_DATA_WIDTH / 8; byte_index++) begin
        rw.data[byte_index * 8 +: 8] = transaction.data[byte_index];
      end
    end

    // Reconstruct write data only for the trace; incomplete payloads remain unknown.
    completion_data = rw.data[31:0];
    if (rw.kind == UVM_WRITE) begin
      completion_data = 'x;
      if (transaction.data.size() == 4) begin
        for (int unsigned byte_index = 0; byte_index < 4; byte_index++) begin
          completion_data[byte_index * 8 +: 8] = transaction.data[byte_index];
        end
      end
    end

    `uvm_info(
      "USB_RAL_ADAPTER",
      $sformatf(
        "%s completed RAL %s addr=0x%08h data=0x%08h status=%s",
        get_name(),
        rw.kind == UVM_WRITE ? "write" : "read",
        rw.addr,
        completion_data,
        rw.status.name()
      ),
      UVM_HIGH
    )
  endfunction
endclass
