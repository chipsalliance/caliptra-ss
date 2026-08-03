# Comprehensive Technical Summary & Guide: Porting UART Host UVM DV from OpenTitan to Caliptra-SS

## 1. Project Overview & Objectives

The goal of this project is to port the **UART / UART Host** UVM block-level verification environment from **OpenTitan** (`~/opentitan/hw/ip/uart/dv`) into **Caliptra-SS** (`~/caliptra/github/caliptra-ss_UART/src/uart/dv`). 

While OpenTitan relies on the **TL-UL** (TileLink Uncached Lite) bus and `cip_lib` infrastructure, Caliptra-SS standardizes on **AXI4** bus protocols and the standalone `dv_lib` framework (similar to the successful migration of `spi_host` documented in `SPI_HOST_UVM_MIGRATION_SUMMARY.md` and `aes` under `third_party/caliptra-rtl/src/aes`).

---

## 2. Architectural Comparison

| Dimension | OpenTitan (`~/opentitan/hw/ip/uart/dv`) | Caliptra-SS (`~/caliptra/github/caliptra-ss_UART/src/uart/dv`) |
| :--- | :--- | :--- |
| **Primary Bus Protocol** | TL-UL (TileLink Uncached Lite) | AXI4 (using `axi_agent` / `axi2tlul` wrapper) |
| **Base Class Library** | `cip_lib` (`cip_base_test`, `cip_base_env`, `cip_base_scoreboard`) | `dv_lib` (`dv_base_test`, `dv_base_env`, `dv_base_scoreboard`) |
| **System Dependencies** | `lc_ctrl_pkg`, `alert_handler_pkg`, `prim_pkg` | Standalone Caliptra packages (`tools/dv-classes/*`) |
| **RAL Generation** | `reggen` (OpenTitan legacy) | `PeakRDL-uvm` (`uart_ral_pkg.sv`) |
| **Build System** | `dvsim` / `.hjson` / `.core` | VCS / Flat filelist (`.vf`) & `.core` |

---

## 3. Step-by-Step Porting & Migration Plan

### Phase 1: Environment & Directory Structure Setup
1. **Copy Source Files**:
   - Copy `dv/` directory contents from `~/opentitan/hw/ip/uart/dv/` to `~/caliptra/github/caliptra-ss_UART/src/uart/dv/`.
2. **Directory Alignment**:
   ```
   src/uart/
   ├── data/                 # Reggen / PeakRDL HJSON definitions
   ├── dv/
   │   ├── cov/              # Coverage exclusions & models
   │   ├── env/              # Environment, scoreboard, cfg, pkg, seq_lib
   │   │   └── seq_lib/      # Virtual sequences (smoke, fifo, noise filter, parity err, etc.)
   │   ├── sva/              # SystemVerilog Assertions & bind files
   │   ├── tb/               # Testbench top (tb.sv)
   │   └── tests/            # Test package and base test
   ├── rtl/                  # RTL source code
   └── config/               # Build filelists (uart_tb_flat.vf)
   ```

---

### Phase 2: Protocol & Bus Agent Migration (TL-UL $\rightarrow$ AXI4)
1. **Replace TL-UL Agent with AXI Agent**:
   - Update `uart_env_cfg.sv` to instantiate `axi_agent_cfg` (`m_axi_agent_cfg`) instead of `tl_agent_cfg`.
   - Update `uart_env.sv` to create and connect `axi_agent` (`m_axi_agent`).
2. **Register Adapter**:
   - Connect `axi_reg_adapter` (`tools/dv-classes/axi_agent/axi_reg_adapter.svh`) to the UVM RAL model (`ral.default_map.set_sequencer(m_axi_agent.sequencer, reg_adapter)`).
3. **Sequence Refactoring**:
   - Replace any legacy `tl_access` or raw TL-UL transaction tasks in `uart_base_vseq.sv` with RAL register reads/writes (`ral.txdata.write`, `ral.rxdata.read`, etc.).

---

### Phase 3: Framework & Base Class Refactoring (`cip_lib` $\rightarrow$ `dv_lib`)
1. **Inheritance & Imports**:
   - Replace `` `include "cip_macros.svh" `` and `import cip_base_pkg::*;` with `import dv_base_pkg::*;`.
   - Change base classes:
     - `uart_env` $\rightarrow$ extends `dv_base_env`
     - `uart_env_cfg` $\rightarrow$ extends `dv_base_env_cfg`
     - `uart_scoreboard` $\rightarrow$ extends `dv_base_scoreboard`
     - `uart_base_vseq` $\rightarrow$ extends `dv_base_vseq`
     - `uart_base_test` $\rightarrow$ extends `dv_base_test`
2. **Decouple OpenTitan-Specific Features**:
   - Remove references to `alert_handler`, `lc_ctrl`, and `mubi` (multi-bit boolean) types that are not part of Caliptra-SS.
   - Adjust `intr_pins_cg` or TL-UL specific coverage primitives in `uart_scoreboard.sv` and `uart_env_cov.sv`.

---

### Phase 4: RAL (Register Abstraction Layer) Generation
1. **Generate PeakRDL UVM Package**:
   - Use PeakRDL or `regtool.py` to generate `uart_ral_pkg.sv` from `src/uart/data/uart.hjson`.
2. **Format Compatibility**:
   - Ensure RAL field configurations are UVM 1.2 compatible (strip any non-standard OpenTitan `mubi_access` parameter overrides if present).
3. **Integrate into Environment**:
   - Instantiate `uart_reg_block` in `uart_env_cfg.sv` via `initialize_ral(32, 32, 4)`.

---

### Phase 5: Scoreboard & Virtual Sequence Adaptation
1. **`uart_scoreboard.sv` Refactoring**:
   - Override `post_write` and `post_read` callbacks as `task`s to match UVM 1.2 `uvm_reg_cbs`.
   - Replace direct task calls inside functions with `get_mirrored_value()`.
   - Provide default byte enable mask (`4'hf`) for register field updates.
2. **`seq_lib` Adjustments**:
   - Update `uart_vseq_list.sv` to include all sequences (`uart_smoke_vseq`, `uart_fifo_full_vseq`, `uart_rx_parity_err_vseq`, `uart_noise_filter_vseq`, etc.).
   - Refactor `uart_base_vseq.sv` to support standard Caliptra clock/reset interface (`clk_rst_if`) and interrupt interface (`pins_if #(num_interrupts)`).

---

### Phase 6: Testbench Top (`tb.sv`) & Filelist Setup
1. **Testbench Top (`src/uart/dv/tb/tb.sv`)**:
   - Instantiate clock/reset interface (`clk_rst_if`).
   - Instantiate UART physical interface (`uart_if` / `pins_if`).
   - Instantiate AXI interface (`axi_if`) and bind to `uart_axi` RTL top wrapper.
   - Set virtual interfaces in `uvm_config_db`.
2. **Filelist Creation (`src/uart/config/uart_tb_flat.vf`)**:
   - Create a flat filelist linking:
     - Dependent interfaces: `clk_rst_if.sv`, `pins_if.sv`, `axi_*_if.sv`, `uart_nf_if.sv`.
     - Packages: `dv_base_agent_pkg`, `axi_agent_pkg`, `csr_utils_pkg`, `uart_ral_pkg`, `uart_env_pkg`, `uart_test_pkg`.
     - RTL files: `uart_reg_top.sv`, `uart_core.sv`, `uart.sv`, and `uart_axi.sv`.

---

### Phase 7: Compilation & Elaboration with VCS
1. **Build Execution Command**:
   ```bash
   vcs -sverilog -full64 -ntb_opts uvm-1.2 -timescale=1ns/1ps -notice -kdb -debug_access+all \
       +define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
       +define+UVM_REG_ADDR_WIDTH=32 +define+UVM_REG_DATA_WIDTH=32 +define+SIMULATION +define+INC_ASSERT \
       -top tb -f ~/caliptra/github/caliptra-ss_UART/src/uart/config/uart_tb_flat.vf
   ```
2. **Verification & Test Execution**:
   - Run `uart_smoke_test`: `./simv +uvm_testname=uart_smoke_test`.

---

## 4. Key Lessons Learned from SPI Host & AES Porting
- **UVM 1.2 Callback Signatures**: `post_write` / `post_read` in `uvm_reg_cbs` must be declared as `task`s rather than `function void`.
- **Factory Registration**: Ensure all sequence items (especially custom request/response items in `axi_agent`) have explicit `` `uvm_object_utils `` macros.
- **Clocking Block Sampling**: Replace illegal clocking block output signal sampling in drivers with internal wire sampling.
- **Sequencer Passing in UVM 1.2**: Always pass `null` as the parent sequence when starting layer virtual sequences on sub-sequencers.

---

## 5. Summary Checklist for Porting Completion
- [ ] Directory copied to `src/uart/dv`
- [ ] `uart_ral_pkg.sv` generated and verified
- [ ] `cip_lib` replaced with `dv_lib` across all environment files
- [ ] TL-UL agent replaced with Caliptra `axi_agent`
- [ ] `uart_scoreboard.sv` refactored for AXI & UVM 1.2
- [ ] `tb.sv` updated with AXI & clock/reset interfaces
- [ ] `uart_tb_flat.vf` created and ordered
- [ ] VCS build passes with 0 compilation and elaboration errors
- [ ] `uart_smoke_test` passes successfully in simulation

---------------------------------------------------------------------------------------------------------------------------------------------
### Step-by-Step Porting Summary & Accomplishments

  The step-by-step migration of the UART Host / UART UVM block-level verification environment from OpenTitan (cip_lib / TL-UL) to Caliptra-SS (dv_lib / AXI4) has been completed.
  ──────
  ### Executed Actions

  1. Detailed Technical Migration Guide Artifact
      • Created uart_host_dv_porting_guide.md outlining the architectural transitions, protocol adaptations, and step-by-step methodologies.
  2. UVM Register Model (RAL) Generation
      • Generated src/uart/dv/env/uart_ral_pkg.sv from uart.hjson using regtool.py configured for Caliptra's dv_base_reg.
  3. Environment & Package Refactoring (cip_lib → dv_lib)
      • uart_env_pkg.sv: Replaced tl_agent_pkg / cip_base_pkg imports with axi_agent_pkg and dv_lib_pkg. Defined RxFifoDepth / TxFifoDepth parameters locally.
      • uart_env_cfg.sv: Refactored to extend dv_base_env_cfg, added axi_agent_cfg m_axi_agent_cfg, and invoked initialize_ral(32, 32, 4).
      • uart_env.sv: Refactored to extend dv_base_env, instantiated axi_mgr_agent, and mapped m_axi_agent register adapter to ral.default_map.
      • uart_scoreboard.sv: Updated to extend dv_base_scoreboard.
      • uart_env_cov.sv: Updated to extend dv_base_env_cov.
      • uart_virtual_sequencer.sv: Updated to extend dv_base_virtual_sequencer.
      • uart_base_vseq.sv & uart_base_test.sv: Updated base classes to dv_base_vseq and dv_base_test.
      • uart_test_pkg.sv: Updated imports to dv_lib_pkg.
      • tools/dv-classes/uart_agent/: Copied uart_agent package and sequences into tools/dv-classes/.
  4. AXI Wrapper & Testbench Top Integration
      • src/uart/rtl/uart_axi.sv: Created the AXI4 wrapper module connecting Caliptra's axi2tlul bridge to uart.sv.
      • src/uart/dv/tb/tb.sv: Updated testbench top to instantiate axi_if and bind to uart_axi.
      • src/uart/config/uart_tb_flat.vf: Constructed a flat VCS filelist linking all base packages, protocol agents, RAL, RTL, interfaces, and testbench top in strict compilation dependency order.


