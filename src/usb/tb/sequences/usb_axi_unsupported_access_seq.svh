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
// Unsupported AXI request shapes on every USB AXI region. Per CaliptraSSHardwareSpecification
// "DWORD-only accesses" and CaliptraSSIntegrationSpecification "AXI Access Restrictions":
// - an unaligned address or AxSIZE!=2 rejects the whole burst with SLVERR and never touches the target;
// - a rejected read returns every requested beat with zero data and SLVERR;
// - a rejected write accepts every data beat and returns a single SLVERR;
// - USB ignores WSTRB, so a legal DWORD write with partial or zero strobes writes the whole DWORD.
// Each probe is followed by a legal access: mapped regions check that state is unchanged.
class usb_axi_unsupported_access_seq extends usb_base_seq;
  `uvm_object_utils(usb_axi_unsupported_access_seq)

  typedef enum {REGION_MAPPED, REGION_PAD, REGION_HOLE} region_kind_e;
  // words: consecutive DWORDs from offset a probe may touch; mapped regions seed and check all of them.
  typedef struct {
    string name;
    usb_target_e target;
    logic [31:0] offset;
    logic [31:0] mask;
    region_kind_e kind;
    int unsigned words;
  } region_t;

  // AxSIZE and start-lane pairs; byte lanes follow AXI A3.4.3 for unaligned starts.
  localparam int unsigned SHAPES = 11;
  localparam int unsigned SHAPE_SIZE[SHAPES] = '{2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0};
  localparam int unsigned SHAPE_LANE[SHAPES] = '{1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3};
  // Longest INCR burst (size 2 from lane 3) touches 4 DWORDs.
  localparam int unsigned MAX_BEATS = 4;
  localparam int unsigned MAX_SPAN_WORDS = 4;

  bit completed;
  protected usb_axi_user_override authorized_user;
  protected region_t regions[$];
  protected logic [31:0] combo_csr_offset;
  // Masked contents of the current mapped region's checked words.
  protected logic [31:0] expected_words[$];
  protected int unsigned probes, rejected, single_beat, incr_bursts, fixed_bursts;
  protected int unsigned recoveries, preservation_checks, wstrb_checks;

  function new(string name = "usb_axi_unsupported_access_seq");
    super.new(name);
  endfunction

  // Add one region to probe.
  protected function void add_region(string name, usb_target_e target, logic [31:0] offset, logic [31:0] mask, region_kind_e kind, int unsigned words);
    region_t region;

    region.name = name;
    region.target = target;
    region.offset = offset;
    region.mask = mask;
    region.kind = kind;
    region.words = words;
    regions.push_back(region);
  endfunction

  // Direction label; a ternary of unequal-length literals would pad "read" with a space.
  protected function string direction_name(bit is_write);
    if (is_write) return "write";
    return "read";
  endfunction

  protected function string burst_name(bit is_fixed);
    if (is_fixed) return "FIXED";
    return "INCR";
  endfunction

  // Authorize one random USER on both the Combo and DEV1 policies.
  protected task configure_policies();
    usb_combo_allowlist_t combo_users;
    usb_dev1_allowlist_t dev1_users;

    foreach (combo_users[index]) combo_users[index] = authorized_user.value;
    foreach (dev1_users[index]) dev1_users[index] = authorized_user.value;
    set_axi_user_filter_policies(1'b1, combo_users, 1'b1, dev1_users);
  endtask

  // Legal single-beat DWORD write or read that must return OKAY; no per-target address guard.
  protected task legal_dword(usb_target_e target, logic [31:0] offset, bit is_write, logic [31:0] write_data, output logic [31:0] read_data);
    aaxi_master_tr request;

    request = create_transaction(target, offset, is_write, write_data, authorized_user);
    execute_transaction(target, 32'(request.addr), is_write, request);
    read_data = '0;
    if (is_write) begin
      if (request.resp !== AAXI_RESP_OKAY) begin
        `uvm_fatal("USB_UNSUPPORTED_LEGAL", $sformatf("%s legal DWORD write AXI=0x%016h BRESP=%0h, expected OKAY", usb_target_name(target), request.addr, request.resp))
      end
    end else begin
      read_data = unpack_read_data(target, 32'(request.addr), request);
    end
  endtask

  // Write and read back a random masked value in every checked word of a mapped region.
  protected task seed_region(region_t region);
    logic [31:0] seed, actual, unused;

    expected_words.delete();
    for (int unsigned word = 0; word < region.words; word++) begin
      seed = $urandom() & region.mask;
      legal_dword(region.target, region.offset + 4 * word, 1'b1, seed, unused);
      legal_dword(region.target, region.offset + 4 * word, 1'b0, '0, actual);
      if ((actual & region.mask) !== seed) begin
        `uvm_fatal("USB_UNSUPPORTED_SEED", $sformatf("%s word%0d seed: expected=0x%08h actual=0x%08h mask=0x%08h", region.name, word, seed, actual, region.mask))
      end
      expected_words.push_back(seed);
    end
  endtask

  // Read every checked word and require the masked value to match the seed.
  protected task check_preserved(region_t region, string label);
    logic [31:0] actual;

    foreach (expected_words[word]) begin
      legal_dword(region.target, region.offset + 4 * word, 1'b0, '0, actual);
      if ((actual & region.mask) !== expected_words[word]) begin
        `uvm_error("USB_UNSUPPORTED_STATE", $sformatf("%s changed word%0d: before=0x%08h after=0x%08h mask=0x%08h", label, word, expected_words[word], actual, region.mask))
      end else begin
        preservation_checks++;
      end
    end
  endtask

  // Send one unsupported request and require spec rejection: SLVERR on every read beat with
  // all-zero data, or a single SLVERR for a write. Bursts stay within region.words DWORDs.
  protected task run_probe(region_t region, int unsigned shape, bit is_write, int unsigned beats, bit is_fixed, output string label);
    aaxi_master_tr request;
    int unsigned size = SHAPE_SIZE[shape];
    int unsigned lane = SHAPE_LANE[shape];
    int unsigned first_bytes = (1 << size) - (lane % (1 << size));
    int unsigned total_bytes;
    int unsigned span_words;
    bit ok = 1'b1;

    // INCR beats after the first are size-aligned; FIXED beats repeat the first beat's lanes.
    total_bytes = is_fixed ? beats * first_bytes : first_bytes + (beats - 1) * (1 << size);
    span_words = is_fixed ? 1 : (lane + total_bytes + 3) / 4;
    label = $sformatf("%s size%0d@+%0d %0d-beat %s %s", region.name, size, lane, beats, burst_name(is_fixed), direction_name(is_write));
    if (beats == 0 || beats > MAX_BEATS || span_words > region.words) begin
      `uvm_fatal("USB_UNSUPPORTED_PROBE", $sformatf("%s touches %0d DWORDs, region allows %0d", label, span_words, region.words))
    end

    request = create_transaction(region.target, region.offset, is_write, '0, authorized_user);
    request.set_name(label);
    request.addr += lane;
    request.size = size;
    request.len = beats - 1;
    request.burst = is_fixed ? AAXI_BURST_FIXED : AAXI_BURST_INCR;
    if (is_write) begin
      // opt_auto_unalign_rw_exactly=1: the data queue holds only the active bytes, from the start address.
      request.data.delete();
      request.strobes.delete();
      for (int unsigned index = 0; index < total_bytes; index++) begin
        request.data.push_back(8'($urandom()));
        request.strobes.push_back(1'b1);
      end
      request.wuser_A = new[beats];
      foreach (request.wuser_A[beat]) request.wuser_A[beat] = authorized_user.value;
    end
    execute_transaction(region.target, 32'(request.addr), is_write, request);
    probes++;
    if (beats == 1) single_beat++;
    else if (is_fixed) fixed_bursts++;
    else incr_bursts++;

    if (is_write) begin
      if (request.resp !== AAXI_RESP_SLVERR) begin
        `uvm_error("USB_UNSUPPORTED_RESPONSE", $sformatf("%s AXI=0x%016h: BRESP=%0h, expected SLVERR", label, request.addr, request.resp))
        ok = 1'b0;
      end
    end else begin
      if (request.rresp_Q.size() != beats || request.data.size() != total_bytes) begin
        `uvm_error("USB_UNSUPPORTED_RESPONSE", $sformatf("%s AXI=0x%016h: %0d responses and %0d bytes, expected %0d and %0d", label, request.addr, request.rresp_Q.size(), request.data.size(), beats, total_bytes))
        ok = 1'b0;
      end
      foreach (request.rresp_Q[beat]) begin
        if (request.rresp_Q[beat] !== AAXI_RESP_SLVERR) begin
          `uvm_error("USB_UNSUPPORTED_RESPONSE", $sformatf("%s AXI=0x%016h: beat%0d RRESP=%0h, expected SLVERR", label, request.addr, beat, request.rresp_Q[beat]))
          ok = 1'b0;
          break;
        end
      end
      foreach (request.data[index]) begin
        if (request.data[index] !== 8'h00) begin
          `uvm_error("USB_UNSUPPORTED_DATA", $sformatf("%s AXI=0x%016h: byte%0d=0x%02h, expected 0x00 (data=%p)", label, request.addr, index, request.data[index], request.data))
          ok = 1'b0;
          break;
        end
      end
    end
    if (ok) rejected++;
    `uvm_info("USB_UNSUPPORTED_RESPONSE", $sformatf("%s AXI=0x%016h ID=0x%0h USER=0x%0h resp=%0h rresp=%p bytes=%p", label, request.addr, request.id, authorized_user.value, request.resp, request.rresp_Q, request.data), UVM_LOW)
  endtask

  // Legal DWORD writes with zero and random partial WSTRB must return OKAY and write every byte.
  protected task check_wstrb_ignored(region_t region);
    aaxi_master_tr request;
    logic [3:0] strobe_patterns[2];
    logic [31:0] data, actual;
    string label;

    strobe_patterns[0] = 4'b0000;
    strobe_patterns[1] = 4'($urandom_range(14, 1));
    foreach (strobe_patterns[pattern]) begin
      // Flip every masked bit so a skipped byte lane cannot match.
      data = ~expected_words[0] & region.mask;
      label = $sformatf("%s WSTRB=4'b%04b write data=0x%08h", region.name, strobe_patterns[pattern], data);
      request = create_transaction(region.target, region.offset, 1'b1, data, authorized_user);
      request.set_name(label);
      foreach (request.strobes[lane]) request.strobes[lane] = strobe_patterns[pattern][lane];
      execute_transaction(region.target, 32'(request.addr), 1'b1, request);
      if (request.resp !== AAXI_RESP_OKAY) begin
        `uvm_error("USB_UNSUPPORTED_WSTRB", $sformatf("%s AXI=0x%016h: BRESP=%0h, expected OKAY", label, request.addr, request.resp))
      end
      legal_dword(region.target, region.offset, 1'b0, '0, actual);
      if ((actual & region.mask) !== data) begin
        `uvm_error("USB_UNSUPPORTED_WSTRB", $sformatf("%s: readback=0x%08h mask=0x%08h, expected the whole DWORD written", label, actual, region.mask))
      end else begin
        wstrb_checks++;
      end
      `uvm_info("USB_UNSUPPORTED_WSTRB", $sformatf("%s AXI=0x%016h BRESP=%0h readback=0x%08h", label, request.addr, request.resp, actual), UVM_LOW)
      expected_words[0] = actual & region.mask;
    end
  endtask

  // Seed a mapped region, then run every shape as a write and a read, once single-beat and once as a
  // 2..MAX_BEATS burst; each probe is followed by a legal access. Single-DWORD regions use FIXED bursts.
  protected task run_region(region_t region);
    logic [31:0] unused;
    int unsigned beats;
    bit is_fixed;
    string label;

    if (region.kind == REGION_MAPPED) seed_region(region);
    for (int unsigned shape = 0; shape < SHAPES; shape++) begin
      for (int unsigned direction = 0; direction < 2; direction++) begin
        for (int unsigned variant = 0; variant < 2; variant++) begin
          beats = variant == 0 ? 1 : $urandom_range(MAX_BEATS, 2);
          is_fixed = variant != 0 && (region.words == 1 || $urandom_range(1, 0));
          run_probe(region, shape, direction == 0, beats, is_fixed, label);
          if (region.kind == REGION_MAPPED) begin
            check_preserved(region, label);
          end else begin
            // The bridge must still serve a legal Combo request after a pad or Unmapped probe.
            legal_dword(USB_DEV0_CSR, combo_csr_offset, 1'b0, '0, unused);
          end
          recoveries++;
        end
      end
    end
    if (region.kind == REGION_MAPPED) check_wstrb_ignored(region);
  endtask

  task body();
    usb_axi_user_t axi_user;
    logic [31:0] hub_end, combo_bytes, unused;

    completed = 1'b0;
    probes = 0;
    rejected = 0;
    single_beat = 0;
    incr_bursts = 0;
    fixed_bursts = 0;
    recoveries = 0;
    preservation_checks = 0;
    wstrb_checks = 0;
    if (!std::randomize(axi_user)) `uvm_fatal("USB_UNSUPPORTED_USER", "AXI USER randomization failed")
    authorized_user = usb_axi_user_override::with_value(axi_user);
    randomize_manager_ids();
    configure_policies();
    if (sequencer_for(USB_DEV0_CSR).cfg.cfg_info.opt_auto_unalign_rw_exactly !== 1'b1) begin
      `uvm_fatal("USB_UNSUPPORTED_SETUP", "Write data packing assumes Avery opt_auto_unalign_rw_exactly=1")
    end

    // CaliptraSSHardwareSpecification: Combo AXI memory map, rounded Hub/window sizes.
    hub_end = 32'h1000 + (32'd4 << $clog2(USB_HUB_FIFO_SIZE));
    combo_bytes = 32'd1 << $clog2(hub_end);
    combo_csr_offset = csr_offset(USB_DEV0_CSR, "INTROUTE");
    add_region("DEV0-RAM", USB_DEV0_SRAM, 32'h3000, '1, REGION_MAPPED, MAX_SPAN_WORDS);
    add_region("DEV1-RAM", USB_DEV1_SRAM, 32'h3000, '1, REGION_MAPPED, MAX_SPAN_WORDS);
    add_region("DEV0-CSR", USB_DEV0_CSR, combo_csr_offset, USB_DEV0_ROUTE_MASK, REGION_MAPPED, 1);
    add_region("OCP-Recovery", USB_DEV0_CSR, reg_offset(USB_DEV0_CSR, p_sequencer.reg_model.combo.recovery.DEVICE_ID_1), '1, REGION_MAPPED, 1);
    add_region("Hub", USB_HUB, mem_word_offset(USB_HUB, p_sequencer.reg_model.combo.hub.DESCRIPTOR_LOW.m_mem, 2), '1, REGION_MAPPED, 1);
    // Hub padding has no defined contents, but unsupported request shapes must be rejected.
    add_region("Hub-pad", USB_DEV0_CSR, 32'h1000 + USB_HUB_FIFO_SIZE * 4, '1, REGION_PAD,
               (hub_end - (32'h1000 + USB_HUB_FIFO_SIZE * 4)) >= 4 * MAX_SPAN_WORDS ? MAX_SPAN_WORDS : 1);
    // 0x40..0x7FF is a fixed Combo hole.
    add_region("Unmapped-low", USB_DEV0_CSR, 32'h40, '1, REGION_HOLE, MAX_SPAN_WORDS);
    if (hub_end < combo_bytes) begin
      add_region("Unmapped-high", USB_DEV0_CSR, hub_end, '1, REGION_HOLE, (combo_bytes - hub_end) >= 4 * MAX_SPAN_WORDS ? MAX_SPAN_WORDS : 1);
    end
    add_region("DEV1-CSR", USB_DEV1_CSR, csr_offset(USB_DEV1_CSR, "INTROUTE"), USB_DEV1_ROUTE_MASK, REGION_MAPPED, 1);
    `uvm_info("USB_UNSUPPORTED_SETUP", $sformatf("USER=0x%0h regions=%0d shapes=%0d Hub aperture end=0x%08h Combo bytes=0x%08h", axi_user, regions.size(), SHAPES, hub_end, combo_bytes), UVM_LOW)

    foreach (regions[index]) run_region(regions[index]);

    // Leave interrupt routing cleared on both CSR blocks.
    legal_dword(USB_DEV0_CSR, combo_csr_offset, 1'b1, '0, unused);
    legal_dword(USB_DEV1_CSR, csr_offset(USB_DEV1_CSR, "INTROUTE"), 1'b1, '0, unused);

    `uvm_info("USB_UNSUPPORTED_SUMMARY", $sformatf("rejected=%0d/%0d (single-beat=%0d INCR=%0d FIXED=%0d) legal follow-ups=%0d preservation checks=%0d WSTRB-ignored checks=%0d",
              rejected, probes, single_beat, incr_bursts, fixed_bursts, recoveries, preservation_checks, wstrb_checks), UVM_LOW)
    completed = 1'b1;
  endtask
endclass
