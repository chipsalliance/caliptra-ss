# Comprehensive Summary of SPI Host UVM Testbench Migration

## 1. Executive Summary

This document provides a detailed log and summary of the migration, refactoring, and compilation of the block-level UVM verification environment for **`spi_host`** (`caliptra_ss_spi_host`) on the remote CW workstation environment (`samipmodi.cw.edafarm.goog`).

The testbench has been converted from OpenTitan's legacy TL-UL bus interface and `cip_lib` infrastructure to Caliptra's standard **AXI4** bus interface and `dv_lib` framework. The flat testbench top (`tb.sv`) was compiled, elaborated, and linked into an executable (`simv`) using VCS without any compilation or elaboration errors.

---

## 2. Key Architectural & Migration Decisions

1. **Bus Protocol Migration (TL-UL $\rightarrow$ AXI4)**:
   - Replaced all TL-UL interfaces, adapters, and agent instances with Caliptra's `axi_agent` and `spi_host_axi` top wrapper.
   - Bypassed TL-UL-specific tasks (`tl_access`) in virtual sequences in favor of direct RAL memory writes/reads routed through the AXI register adapter.

2. **Decoupling from OpenTitan IP Dependencies**:
   - Removed all dependencies on OpenTitan system packages (`lc_ctrl_pkg`, `alert_handler_pkg`, `cip_lib`).
   - Replaced `cip_base_*` base classes with standard `dv_base_*` classes from Caliptra's standalone `dv_lib`.

3. **PeakRDL-uvm RAL Model Generation**:
   - Generated a fresh UVM RAL model (`spi_host_ral_pkg.sv`) using PeakRDL.
   - Tailored field configuration calls to remain compatible with standard UVM 1.2 by stripping unsupported `mubi_access` parameters.

---

## 3. Detailed Summary of Modifications & Fixes

### A. AXI Agent & Infrastructure (`tools/dv-classes/axi_agent/`)
* **`axi_reg_adapter.svh`**: Added dynamic `$cast` in `bus2reg` to safely downcast base `uvm_sequence_item` to `axi_reg_op_item`.
* **`axi_mgr_agent.svh`**: Fixed `layer_vseq.start()` invocation to explicitly pass `null` as required by UVM 1.2.
* **`seq_lib/axi_mgr_register_layer_vseq.svh`**: Qualified AXI response enums (`axi_read_data_item::RRespOkay` and `axi_write_response_item::BRespOkay`).
* **`axi_mgr_write_response_driver.svh` & `axi_mgr_read_data_driver.svh`**: Replaced illegal clocking block output sampling (`mgr_cb.bready` / `mgr_cb.rready`) with direct internal interface wire reads (`bready_internal` / `rready_internal`).
* **`axi_fixed_*.svh` Items**: Added missing `` `uvm_object_utils(...) `` factory registrations across all 4 request/response sequence item classes (`axi_fixed_read_req_item`, `axi_fixed_read_rsp_item`, `axi_fixed_write_req_item`, `axi_fixed_write_rsp_item`).
* **`axi_reset_monitor_*.svh`**: Added missing `set_vif` function implementations for all 5 channel reset monitors (`aw`, `w`, `b`, `ar`, `r`).
* **`seq_lib/axi_mgr_*_fixed_vseq.svh`**: Wrapped multi-statement thread branches inside `fork...join` blocks with `begin...end` blocks and cast `uvm_sequence_item` outputs from response router.

### B. Environment, Configuration & Scoreboard (`src/spi_host/dv/env/`)
* **`spi_host_env_cfg.sv`**:
  - Declared `num_interrupts` as a local member variable.
  - Removed unsupported `is_active` setting on `m_axi_agent_cfg`.
  - Initialized RAL via `initialize_ral(32, 32, 4)`.
* **`spi_host_scoreboard.sv`**:
  - Overrode callback `post_write` and `post_read` methods as `task`s (matching `uvm_reg_cbs` definitions in UVM 1.2) instead of `function void`.
  - Fixed compiler argument count mismatch by omitting parameter string in implicit constructor calls (`reg_cb = new()`).
  - Replaced illegal task calls (`csr_rd`) inside `mem_write` / `mem_read` functions with zero-delay `get_mirrored_value()` calls.
  - Provided fallback `4'hf` byte enable mask for memory callbacks.
  - Commented out legacy TL-UL interrupt covergroup sampling calls (`intr_test_cg`, `intr_cg`, `intr_pins_cg`).

### C. Virtual Sequences (`src/spi_host/dv/env/seq_lib/`)
* **`spi_host_base_vseq.sv`**:
  - Added stubs for missing legacy base class methods (`check_interrupts`, `run_common_vseq_wrapper`).
  - Replaced raw `tl_access_inner` calls in `access_data_fifo` with standard RAL memory calls (`ral.txdata.write` and `ral.rxdata.read`).
* **`spi_host_status_stall_vseq.sv` & `spi_host_stress_all_vseq.sv`**:
  - Changed sequence handle declarations from parameterized `uvm_sequence` to base class `uvm_sequence_base` to match `create_seq_by_name()` return type.

### D. Testbench Top & Build Specification
* **`src/spi_host/dv/tb.sv`**:
  - Updated `intg_error` declaration from `logic` to `wire` so it can bind to the `inout` port of `pins_if #(1)`.
* **`src/spi_host/config/spi_host_tb_flat.vf`**:
  - Created a single flat filelist linking all RTL source files, interfaces (`axi_*_if.sv`, `clk_rst_if.sv`, `pins_if.sv`, `spi_if.sv`), agent packages, and environment packages in strict compilation dependency order.

---

## 4. Final Build Verification Command

```bash
source /workspace/mnt/env/sim/vcs.env
CALIPTRA_SS_ROOT=~/caliptra/github/caliptra-ss_folder/caliptra-ss_spi_host \
CALIPTRA_ROOT=$CALIPTRA_SS_ROOT/third_party/caliptra-rtl \
vcs -sverilog -full64 -ntb_opts uvm-1.2 -timescale=1ns/1ps -notice -kdb -debug_access+all \
    +define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
    +define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 +define+SIMULATION +define+INC_ASSERT \
    -top tb -f ~/caliptra/github/caliptra-ss_folder/caliptra-ss_spi_host/src/spi_host/config/spi_host_tb_flat.vf
```

**Status**:
- **0 Compilation Errors**
- **0 Elaboration Errors**
- Generated executable **`~/caliptra/github/caliptra-ss_folder/caliptra-ss_spi_host/simv`** successfully.
