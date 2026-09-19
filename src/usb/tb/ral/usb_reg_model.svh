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
// Handwritten composition layer for the generated USB RAL packages.
// Included by usb_tb_pkg.sv and constructed by usb_env, this model exposes
// DEV0 CSR/HUB, DEV0 packet SRAM, DEV1 CSR, and DEV1 packet SRAM through four
// port-local maps. It provides access without automatic mirror prediction or
// read comparison; test sequences are responsible for checking returned data.
// Keep bus-specific map adjustments here rather than editing generated code.

// Assemble generated blocks and validate packet-memory addressing for the bench.
class usb_reg_model extends uvm_reg_block;
  `uvm_object_utils(usb_reg_model)

  // Independently generated memory types preserve the same public child paths.
  usb_combo combo;
  usb_dev1_csr dev1_csr;
  usb_dev0_mem_ral dev0_mem;
  usb_dev1_mem_ral dev1_mem;

  // Independent ports use bases from the USB-specific configuration.
  uvm_reg_map combo_map;
  uvm_reg_map dev0_mem_map;
  uvm_reg_map dev1_csr_map;
  uvm_reg_map dev1_mem_map;

  // Create the access model without requesting register-model coverage.
  function new(string name = "usb_reg_model");
    super.new(name, UVM_NO_COVERAGE);
  endfunction

  // Reject truncation and aperture wrap before converting a base to UVM's type.
  function void validate_aperture(string port_name, logic [63:0] base_address, logic [63:0] aperture_bytes);
    logic [64:0] last_byte;
    logic [64:0] bus_limit;

    if (USB_AXI_ADDR_WIDTH < 1 || USB_AXI_ADDR_WIDTH > 64 || $bits(uvm_reg_addr_t) < USB_AXI_ADDR_WIDTH) begin
      `uvm_fatal("USB_RAL_MAP", "USB address width must fit both the generated 64-bit constants and uvm_reg_addr_t")
    end
    bus_limit = (65'd1 << USB_AXI_ADDR_WIDTH) - 65'd1;
    if ((^base_address) === 1'bx || (^aperture_bytes) === 1'bx || aperture_bytes === 64'd0) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s has an unknown base/size or an empty aperture", port_name))
    end
    if ((aperture_bytes & (aperture_bytes - 64'd1)) != 0) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s aperture 0x%0h is not a power of two", port_name, aperture_bytes))
    end
    if ((base_address & (aperture_bytes - 64'd1)) != 0) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s base 0x%0h is not aligned to aperture 0x%0h", port_name, base_address, aperture_bytes))
    end
    last_byte = {1'b0, base_address} + {1'b0, aperture_bytes} - 65'd1;
    if (!(({1'b0, base_address} <= bus_limit) === 1'b1) || !((last_byte <= bus_limit) === 1'b1)) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s base=0x%0h bytes=0x%0h exceeds %0d-bit USB addressing", port_name, base_address, aperture_bytes, USB_AXI_ADDR_WIDTH))
    end
  endfunction

  // Retarget both built memory-map levels before locking, independent of generated types.
  function void configure_packet_memory_maps(uvm_reg_block memory_block, uvm_reg_block packet_block);
    if (memory_block === null || packet_block === null) begin
      `uvm_fatal("USB_RAL_MAP", "Cannot retarget an incomplete packet-memory block")
    end
    if (memory_block.default_map === null || packet_block.default_map === null) begin
      `uvm_fatal("USB_RAL_MAP", "Cannot retarget missing packet-memory maps")
    end
    // Leaving an 8-byte generated submap below a 4-byte root can double the
    // memory-element stride. Adjust both maps, but retain 64-bit memory rows.
    memory_block.default_map.configure(memory_block, 0, USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
    packet_block.default_map.configure(packet_block, 0, USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
  endfunction

  // Apply bases once at the roots; defaults preserve usb_env's model.build() call.
  // Root-map bases do not add DUT address translation.
  virtual function void build(
    logic [63:0] combo_base = usb_ral_config_pkg::COMBO_BASE_ADDRESS,
    logic [63:0] dev0_mem_base = usb_ral_config_pkg::DEV0_MEM_BASE_ADDRESS,
    logic [63:0] dev1_csr_base = usb_ral_config_pkg::DEV1_CSR_BASE_ADDRESS,
    logic [63:0] dev1_mem_base = usb_ral_config_pkg::DEV1_MEM_BASE_ADDRESS
  );
    `uvm_info("USB_RAL_MAP", $sformatf("Building %s: combo=0x%0h dev0_mem=0x%0h dev1_csr=0x%0h dev1_mem=0x%0h", get_full_name(), combo_base, dev0_mem_base, dev1_csr_base, dev1_mem_base), UVM_LOW)
    validate_aperture("COMBO", combo_base, 64'd1 << USB_COMBO_LOCAL_ADDR_WIDTH);
    validate_aperture("DEV0_MEM", dev0_mem_base, 64'd8 * USB_DEV0_RAM_DEPTH);
    validate_aperture("DEV1_CSR", dev1_csr_base, 64'd1 << USB_DEV1_CSR_LOCAL_ADDR_WIDTH);
    validate_aperture("DEV1_MEM", dev1_mem_base, 64'd8 * USB_DEV1_RAM_DEPTH);

    combo_map = create_map("combo_map", uvm_reg_addr_t'(combo_base), USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
    dev0_mem_map = create_map("dev0_mem_map", uvm_reg_addr_t'(dev0_mem_base), USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
    dev1_csr_map = create_map("dev1_csr_map", uvm_reg_addr_t'(dev1_csr_base), USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
    dev1_mem_map = create_map("dev1_mem_map", uvm_reg_addr_t'(dev1_mem_base), USB_AXI_DATA_WIDTH / 8, UVM_LITTLE_ENDIAN, 1);
    set_default_map(combo_map);

    // Generated classes are not factory-enabled; construct them directly.
    combo = new("combo");
    combo.configure(this);
    combo.build();
    combo_map.add_submap(combo.default_map, 0);

    dev0_mem = new("dev0_mem");
    dev0_mem.configure(this);
    dev0_mem.build();
    configure_packet_memory_maps(dev0_mem, dev0_mem.packet_mem);
    dev0_mem_map.add_submap(dev0_mem.default_map, 0);

    dev1_csr = new("dev1_csr");
    dev1_csr.configure(this);
    dev1_csr.build();
    dev1_csr_map.add_submap(dev1_csr.default_map, 0);

    // A distinct instance keeps DEV1 storage separate from DEV0's RAL memory.
    dev1_mem = new("dev1_mem");
    dev1_mem.configure(this);
    dev1_mem.build();
    configure_packet_memory_maps(dev1_mem, dev1_mem.packet_mem);
    dev1_mem_map.add_submap(dev1_mem.default_map, 0);
    `uvm_info("USB_RAL_MAP", $sformatf("Built %s with four independent maps; ready for lock and validation", get_full_name()), UVM_LOW)
  endfunction

  // Disable automatic prediction and mirror checks on all four access paths.
  // There is no predictor in usb_env; tests explicitly compare access results.
  function void configure_access_only();
    // FUTUREFIX: Add RAL predictors for all AXI paths, then enable mirror prediction and read checking.
    combo_map.set_auto_predict(0);
    combo_map.set_check_on_read(0);
    dev0_mem_map.set_auto_predict(0);
    dev0_mem_map.set_check_on_read(0);
    dev1_csr_map.set_auto_predict(0);
    dev1_csr_map.set_check_on_read(0);
    dev1_mem_map.set_auto_predict(0);
    dev1_mem_map.set_check_on_read(0);
  endfunction

  // Check one built/locked memory hierarchy against the implemented SRAM shape.
  // Fail construction if any row does not resolve to two adjacent 32-bit words.
  function void validate_packet_memory(string memory_name, uvm_mem memory, uvm_reg_map root_map, int unsigned expected_depth);
    uvm_reg_addr_t addresses[];
    logic [63:0] base_address;
    logic [63:0] expected_low;
    logic [63:0] expected_high;
    logic [64:0] aperture_end;
    int access_bytes;

    if (memory === null || root_map === null) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s packet-memory model is incomplete", memory_name))
    end
    if (!(is_locked() === 1'b1)) begin
      `uvm_fatal("USB_RAL_MAP", "Packet-memory address validation requires a locked model")
    end
    if (!(memory.get_size() === expected_depth) || !(memory.get_n_bits() === 64)) begin
      `uvm_fatal("USB_RAL_MAP", $sformatf("%s shape is %0d x %0d, expected %0d x 64", memory_name, memory.get_size(), memory.get_n_bits(), expected_depth))
    end
    base_address = root_map.get_base_addr(UVM_NO_HIER);
    validate_aperture(memory_name, base_address, 64'd8 * expected_depth);
    aperture_end = {1'b0, base_address} + 65'd8 * expected_depth;
    `uvm_info("USB_RAL_MAP", $sformatf("Checking %s: base=0x%0h rows=%0d, two 32-bit accesses per row", memory_name, base_address, expected_depth), UVM_LOW)

    // Inspect every row, not just endpoints, to catch stride and aperture errors.
    for (int unsigned index = 0; index < expected_depth; index++) begin
      // get_addresses takes a memory-row index and returns physical bus addresses;
      // its return value is bytes per access, not the number of accesses.
      access_bytes = memory.get_addresses(index, root_map, addresses);
      // Each 64-bit row occupies eight bytes: low word first, then high word.
      expected_low = base_address + 64'd8 * index;
      expected_high = expected_low + 64'd4;
      if (!(access_bytes === USB_AXI_DATA_WIDTH / 8) || !(addresses.size() === 2)) begin
        `uvm_fatal("USB_RAL_MAP", $sformatf("%s[%0d] maps to %0d accesses of %0d bytes; expected 2 of %0d", memory_name, index, addresses.size(), access_bytes, USB_AXI_DATA_WIDTH / 8))
      end
      if (!(addresses[0] === expected_low) || !(addresses[1] === expected_high) ||
          !((65'(addresses[1]) + 65'd4 <= aperture_end) === 1'b1)) begin
        `uvm_fatal("USB_RAL_MAP", $sformatf("%s[%0d] maps to 0x%0h/0x%0h; expected 0x%0h/0x%0h", memory_name, index, addresses[0], addresses[1], expected_low, expected_high))
      end
      if (index === 0 || (index + 1) % 256 === 0 || (index + 1) === expected_depth) begin
        `uvm_info("USB_RAL_MAP", $sformatf("%s address comparisons: matched_rows=%0d/%0d mismatches=0", memory_name, index + 1, expected_depth), UVM_LOW)
      end
    end
  endfunction

  // Validate both devices against the same depth constants used by the TB RAMs.
  // usb_env calls this after lock_model so the complete maps are available.
  function void validate_packet_memory_maps();
    if (dev0_mem === null || dev1_mem === null) begin
      `uvm_fatal("USB_RAL_MAP", "Packet-memory blocks are missing")
    end
    if (dev0_mem.packet_mem === null || dev1_mem.packet_mem === null) begin
      `uvm_fatal("USB_RAL_MAP", "Packet-memory child blocks are missing")
    end
    validate_packet_memory("DEV0", dev0_mem.packet_mem.m_mem, dev0_mem_map, USB_DEV0_RAM_DEPTH);
    validate_packet_memory("DEV1", dev1_mem.packet_mem.m_mem, dev1_mem_map, USB_DEV1_RAM_DEPTH);
    `uvm_info("USB_RAL_MAP", "Validated all DEV0 and DEV1 packet-memory element addresses", UVM_LOW)
  endfunction
endclass
