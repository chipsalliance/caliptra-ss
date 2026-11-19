# Caliptra-SS SPI_HOST DV Document

## Goals
* **DV**
  * Verify the production `spi_host_axi` subsystem wrapper (`axi2tlul` + `caliptra_ss_spi_host`) end-to-end in dynamic SystemVerilog/UVM simulation for the Caliptra-SS target configuration (`NumCS = 2`, `CmdDepth = 8`, `TxDepth = 72` + 1-word `ByteSelect` = `73` words, `RxDepth = 64` words, `ByteOrder = 1`, `AxiAw = 32`, `AxiDw = 32`, `AxiUw = 32`, `AxiIw = 1`).
  * Exercise all testpoints in [`spi_host_testplan.hjson`](../data/spi_host_testplan.hjson) with independent end-to-end scoreboard checking (zero `uvm_hdl_read` oracle dependencies), separating completed legal-transfer coverage from rejected-command negative outcomes.
* **Protocol & Pin Assertions (SVA)**
  * Continuously verify AMBA AXI4 manager/subordinate channel compliance (`axi_*_if` and `axi_sub`), TL-UL device protocol compliance (`tlul_assert`), accepted-command SPI launch/sample data and output-enable stability (`spi_host_data_stable_sva`), multi-CS mutual exclusion (`$onehot0(~cio_csb_o)`), and passthrough tie-off invariants.

## Design & Register Specification
* **DUT Top-Level (Production AXI Subsystem Wrapper)**: [`src/spi_host/rtl/spi_host_axi.sv`](../rtl/spi_host_axi.sv) (`spi_host_axi`)
* **AXI-to-TL-UL Gasket**: [`src/axi2tlul/rtl/axi2tlul.sv`](../../axi2tlul/rtl/axi2tlul.sv), [`src/axi2tlul/rtl/sub2tlul.sv`](../../axi2tlul/rtl/sub2tlul.sv)
* **SPI Host Core**: [`src/spi_host/rtl/spi_host.sv`](../rtl/spi_host.sv) (`caliptra_ss_spi_host`)
* **Register Definitions**:
  * SystemRDL: [`src/spi_host/rtl/spi_host.rdl`](../rtl/spi_host.rdl)
  * HJSON RAL Spec: [`src/spi_host/data/spi_host.hjson`](../data/spi_host.hjson)
  * Generated RTL Package / Top: [`src/spi_host/rtl/spi_host_reg_pkg.sv`](../rtl/spi_host_reg_pkg.sv), [`src/spi_host/rtl/spi_host_reg_top.sv`](../rtl/spi_host_reg_top.sv)
  * UVM RAL Package: [`src/spi_host/dv/env/spi_host_ral_pkg.sv`](env/spi_host_ral_pkg.sv)

## Testbench Architecture
The SPI_HOST UVM verification environment is built on `dv_base_env` / `dv_lib_pkg` and resides under [`src/spi_host/dv/`](.).

### Top-Level Testbench (`src/spi_host/dv/tb.sv`)
[`tb.sv`](tb.sv) instantiates `spi_host_axi #(.NumCS(2), .CmdDepth(8), .AxiAw(32), .AxiDw(32), .AxiUw(32), .AxiIw(1))` directly as `dut` alongside:
* **Clock, Reset & Gated Waveform Dumping**: `clk_rst_if` driving `clk` and active-low `rst_n`; FSDB/SVA dumping is gated on `+dump_waves` or `+waves` so batch regressions incur zero unconditional waveform overhead.
* **Production AXI4 Bus & Shared Agent (`tools/dv-classes/axi_agent/`)**: `axi_if` connected to `dut.s_axi_w_if` / `dut.s_axi_r_if` and driven by `axi_mgr_agent` across all five AXI4 channels (`aw_if`, `w_if`, `b_if`, `ar_if`, `r_if`), supporting configurable `axi_reg_adapter::m_subword_target_addr` (`SPI_HOST_TXDATA_OFFSET = 0x28`), sub-word `WSTRB` / `AxUSER[21:18]` byte masks, narrow/FIXED/INCR/WRAP bursts, `SLVERR` propagation under `BREADY`/`RREADY` backpressure, and in-flight reset cancellation.
* **SPI Bus, Dual NOR Flash BFMs & Directed Peripheral Responders**: `spi_if` (`tools/dv-classes/spi_agent/`) with tri-state `sd[3:0]` pullups and two pad-enable-gated `spiflash` instances (`gen_spi_flash[0..1]`), which can be disabled via `spi_if.set_flash_model_en(0)` when running strict Winbond W25Q01JV datasheet-enforcing, delayed-MISO `FULLCYC`, or reactive `spi_device_driver` responders.
* **Reactive SPI Device Path Status**: `cfg.en_reactive_device_rsp` defaults to `0` because `tb.sv` connects dual NOR flash models and directed protocol responders; `spi_device_cmd_rsp_seq` + `spi_device_driver` (multi-CS `csb_sel`, 1-byte command framing, MSB-on-highest-lane Dual/Quad bit ordering, non-conflicting `ReadDual = 0x33` opcode, and exact `RXDATA` payload comparison) are validated in `spi_host_closure_vseq`.
* **Interrupt, Integrity & Passive FSM Observer Interfaces**: `pins_if #(2)` monitoring `{intr_spi_event_o, intr_error_o}`, `pins_if #(1)` monitoring `intg_error_o`, `spi_passthrough_if` (widened across `cio_csb_o[1:0]` / `cio_csb_en_o[1:0]` and providing contention-free `inject_cmd_intg_err` control for TL-UL `cmd_intg` SECDED fault injection on `dut.tl_h2d`), and purely passive `spi_host_fsm_if` (zero internal RTL `force` statements on FSM state).

### Compile-Time Configuration Parameters
| Parameter | Value | Description |
| :--- | :---: | :--- |
| `SPI_HOST_NUM_CS` (`NumCS`) | `2` | Dual active-low chip selects (`CS0`, `CS1`) with `CONFIGOPTS_0` (`0x14`) and `CONFIGOPTS_1` (`0x18`); passthrough muxing is structurally disabled (`gen_passthrough_ignore`). |
| `SPI_HOST_CMD_DEPTH` (`CmdDepth`) | `8` | 8-entry command descriptor FIFO (`u_cmd_queue`). |
| `SPI_HOST_TX_DEPTH` (`TxDepth`) | `72` | 72-word `u_tx_fifo` + 1-word greedy `u_select` packer stage = `73` words total capacity (`TXFULL == 1` at `TXQD == 73`). |
| `SPI_HOST_RX_DEPTH` (`RxDepth`) | `64` | 64-word `u_rx_fifo` (`RXFULL == 1` at `RXQD == 64`; `65` words incl. `u_merge` stage for `RXSTALL`). |
| `SPI_HOST_BYTEORDER` (`ByteOrder`) | `1` | Little-Endian byte ordering (`STATUS.BYTEORDER == 1`). |

## Stimulus, Scoreboard & Assertion Verification
* **Smoke vs. Directed Closure Separation**:
  * `spi_host_smoke`: Concise fast smoke test executing dual-CS transfers without replaying heavy closure/fault/reset routines in derived sequences (`speed`, `dual_cs`, `performance`, `upper_range_clkdiv`, `stress_all`).
  * `spi_host_closure`: Dedicated closure sequence executing checked `512`-byte (`LEN = 511`) `TxOnly`/`RxOnly`/`Bidir` streaming transfers, `CMDQD = 8` / `TXQD = 73` / watermark `0..255` boundary checks, bus-level wrong-direction `RXDATA` write (`0x24`) & `TXDATA` read (`0x28`) `SLVERR` + FIFO-preservation checks, AXI4 gasket bursts & shared `axi_agent` null-copy / oversized-ID controls, TL-UL `cmd_intg` fault injection, reactive responder validation, and TX/RX/floating-`Z`/unexpected-zero-RX negative controls.
* **Timing, Reset, Pause, Isolation, Performance & Flash Sequences**:
  * `spi_host_speed` & `spi_host_upper_range_clkdiv`: Sweeps `CSNLEAD/TRAIL/IDLE` through `15`, exercises controlled delayed-MISO transitions distinguishing `FULLCYC = 0` from `FULLCYC = 1` (with DUT-poked and scoreboard fault controls), checks two-sided `ConfigSwitch` (`WaitIdle` + `CSBSwitch`) idle intervals and all-CSB-high `CPOL` switch placement (with early-transition and missing-`CPOL`-switch controls), and verifies unforced (`fast_mode = 0`) physical SCK half-periods at `CLKDIV = 0x0100` and `0xFFFF`.
  * `spi_host_error_cmd`, `spi_host_event`, `spi_host_overflow_underflow`: Verifies reserved `SPEED = 2'b11` (`RsvdSpd`) rejection and pin non-execution across all 4 directions, plus directed one-hot `EVENT_ENABLE` (all 6 bits) and isolated enabled/masked `UNDERFLOW`/`OVERFLOW` verification.
  * `spi_host_sw_reset` & `spi_host_spien`: Verifies observed mid-transfer overlap, `SW_RST` pin return (`CSB = '1`, `SCK = CPOL`, `SD_EN = '0`), empty-`RXDATA` read (`0x0` + `UNDERFLOW`), non-reset CSR retention across `SW_RST`, continuous clock-by-clock `SCK`/`CSB`/`SD`/`SD_EN` stability across `SPIEN == 0`, negative violation controls, and lossless recovery.
  * `spi_host_dual_cs`, `spi_host_performance`, `spi_host_flash`, and CIP `csr_*` / `intr_test`: Verifies single-bit mid-command `CPOL`/`CPHA` updates and physical wrong-CS routing controls (`dual_cs`), `>= 85%` peak Quad streaming bit-rate utilization with `<= 4`-clock inter-SCK gaps and zero stalls (`performance`), synthetic `spiflash` mixed-lane vs. strict Winbond W25Q01JV Rev B datasheet conformance (`flash`), and connected scoreboard recovery checking in `csr_mem_rw_with_rand_reset` even under `csr_tests_mode` (`+en_scb=0`) with separate bus-accepted vs. RAL-call overlap counters.
* **Assertions (`spi_host_bind.sv` & `spi_host_cov_if.sv`, active under `+define+CLP_ASSERT_ON` + `+define+INC_ASSERT`)**:
  * `tlul_assert #(.EndpointType("Device"))` bound on `caliptra_ss_spi_host` (runtime and final assertions enabled; `TLUL_COVER` OpenTitan `tl_agent`-only properties excluded in `cov_hier.cfg`).
  * `spi_host_data_stable_sva #(.NumCS(2))`: Provides active `!rst_ni` bound counterparts (`PassthroughNumCSCompat_Bound_A`, `BidirOnlyInStdMode_Bound_A`, `ValidSpeed_Bound_A`, `ValidCSID_Bound_A`) for RTL inline assertions; selects launch/sample edges from accepted-command FSM registers (`u_fsm.cpol_q`, `u_fsm.cpha_q`, `u_fsm.full_cyc_q`) rather than live CSRs; checks dedicated host outputs `cio_sd_o & cio_sd_en_o` and `cio_sd_en_o` both at SCK sampling edges and continuously on every core `clk_i` cycle (`CORE_CLK_SAMPLE_PHASE_STABLE_P`), and checks resolved pad loopback `cio_sd_i` on host-driven lanes (`cio_sd_en_o & {4{cio_sck_en_o}}`) when `!fsm_full_cyc_i`.
  * `spi_host_cov_if #(.NumCS(2))`: Per-CS `csb_pin_cg[0..1]`, 11 per-CS SVA protocol `cover property` items across `CS0` and `CS1`, and `$onehot0(~cio_csb_o)` mutual-exclusion assertion (all collected in `-cm assert` while excluded from RTL code coverage).
  * **Scoped Assertion Notes**:
    * `EnableAlertTriggerSVA = 0` is single-sourced via `defparam` in [`tb.sv`](tb.sv) for `u_reg.u_prim_reg_we_check.u_caliptra_prim_onehot_check` because Caliptra-SS exports single-wire `intg_error_o` rather than an OpenTitan differential alert channel.
    * `spi_host_csr_assert_fpv` is not elaborated because OpenTitan's standalone FPV CSR generator is not packaged in Caliptra-SS; CSR reset, RW, bit-bash, aliasing, and integrity error paths are verified dynamically in UVM.

## Coverage Scope, Waivers & CI Integration
* **Hierarchy Configuration ([`cov_hier.cfg`](../config/cov_hier.cfg))**: Instruments `tb.dut` (`spi_host_axi`, `u_axi2tlul_spi_host`, `u_caliptra_ss_spi_host`, `u_reg`, `u_window`, `u_cmd_queue`, `u_data_fifos`, and `u_spi_core.*`). Pre-verified TL-UL/SECDED/onehot bus primitives (`u_axi2tlul_cmd_intg_gen`, `u_chk`, `u_prim_reg_we_check`, `u_rsp_intg_gen`, `u_reg_if`, `u_socket`, `u_adapter_rx/tx`) and wire-through RO status subregs are scoped out; bound DV/SVA modules (`u_spi_cov_if`, `spi_host_data_stable_assert`) are excluded from `line+tgl+fsm+cond+branch` code coverage while remaining active in `-cm assert`. Quoted `tb.dut` code coverage therefore does not measure the internal combinational SECDED tree inside `u_reg.u_chk`, while bus-level `cmd_intg` and `data_intg` fault injection and `intg_error_o` latching are verified dynamically.
* **VCS Exclusion File ([`cov_waivers.el`](../config/cov_waivers.el))**:
  * Single-sourced in [`spi_host_sim_cfg.hjson`](spi_host_sim_cfg.hjson) (stale Xcelium `.vRefine` reference removed).
  * Explicitly separates `[DESIGN-UNR]` invariants (`ClearOnRead = 1` in `caliptra_prim_packer_fifo`, `~under_rst` factor in `caliptra_prim_fifo_sync`, mutually exclusive FSM/shift-reg handshakes, one-hot `reg_we_err`) and `[TARGET-CFG]` structural ties (`NumCS = 2` disabling `passthrough_i.passthrough_en`; `ByteOrder = 1`, `TxDepth = 72`, `RxDepth = 64`), while keeping `[SW-CONTRACT-UNR]` (`RsvdSpd` in `u_fsm`/`u_shift_reg`) and `axi2tlul` gasket parameterization unwaived.
* **CI & Nightly Regression**:
  * Both `all` and `nightly` (`en_sim_modes: ["cov"]`, 23 tests) regressions are defined in [`spi_host_sim_cfg.hjson`](spi_host_sim_cfg.hjson). In `chipsalliance/caliptra-ss`, proprietary EDA simulations (Synopsys VCS) execute on internal EDA farm runners (attested for PR gates via `.github/workflows/pre-run-check.yml` / `stamp_repo.sh`), while public GitHub Actions (`ubuntu-22.04`) runs license, RDL parity, and repository hygiene checks.

## Confirmed Design-Owner Architectural Contracts (Nov 12, 2026)
Design owner **Harry Callahan (`hcallahan@lowrisc.org`, Nov 12, 2026)** confirmed **Option A** (maintaining exact RTL parity with upstream OpenTitan with zero RTL modifications and documenting the HW/SW contracts in `caliptra-ss`) for all five specification questions raised in PR #1298:
1. **Same-CS `CSAAT = 1` Continuation with Changed `CONFIGOPTS` (Comment #1 — Confirmed Option A)**: `spi_host_fsm.sv:197-235` checks `config_changed` on the `Idle` path and closes `IdleCSBActive` only on a `CSID` change (`command_i.csid != csid_q`). Software is contractually required to close an active transaction with `CSAAT = 0` before modifying `CONFIGOPTS[cs]` for the same chip select.
2. **Invalid-`CSID` (`CSID >= NumCS`) Queue Retention & Recovery Contract (Comment #2 — Confirmed Option A)**: `spi_host.sv:189-262` clamps out-of-range `CSID` to `'0` and enqueues `command_valid` into `u_cmd_queue` while asserting `ERROR_STATUS.CSIDINVAL` (`enb_error = 1`, halting `u_spi_core`). Firmware must issue `CONTROL.SW_RST` to flush the offending descriptor before clearing `ERROR_STATUS`; clearing `CSIDINVAL` via W1C alone without `SW_RST` unhalts the core and executes the retained descriptor on clamped `CS0` (verified in `spi_host_dual_cs_vseq.sv`).
3. **`ERROR_ENABLE` Masking Scope — Interrupt-Only vs. Core Halt (Comment #3 — Confirmed Option A)**: Upstream documentation claiming `ERROR_ENABLE = 0` *"allows the IP to continue operating"* was inaccurate; per `spi_host.sv:409,487-495`, `ERROR_ENABLE` masks `intr_error_o` generation only, while `enb_error = |sw_error_status` unconditionally halts `u_spi_core` until `ERROR_STATUS` is cleared (verified with `SPIEN = 1` across `ERROR_ENABLE = 1/0` and W1C-only recovery in `spi_host_error_cmd_vseq.sv`).
4. **`CPHA = 1` + `FULLCYC = 1` Architectural Restriction (Comment #4 — Confirmed Option A)**: `spi_host_fsm.sv:275` reflects the intended architectural limitation: full-cycle receive sampling (`FULLCYC = 1`) is supported only when `CPHA = 0`.
5. **`RXWM` Equality Boundary — `>=` ("Reaches or Exceeds") (Comment #25 — Confirmed Option A)**: `spi_host_data_fifos.sv:129` (`rx_wm_o = (rx_qd_o >= rx_watermark_i)`) is the intended behavior, matching upstream OpenTitan PR #32013; `STATUS.RXWM` and `EVENT_ENABLE.RXWM` descriptions in [`spi_host.hjson`](../data/spi_host.hjson) are reconciled to `>=`, and explicit below/equal/above checks are verified in `spi_host_event_vseq.sv` and `spi_host_closure_vseq.sv`.

## Building and Running Tests
Tests and regressions are executed via the pinned `caliptra-rtl` `dvsim` package (inside the Nix shell or via `uv run`) or directly with VCS against [`spi_host_tb_flat.vf`](../config/spi_host_tb_flat.vf):
```console
# Option 1: Pinned dvsim via Nix development shell
$ nix develop ./third_party/caliptra-rtl#caliptra-dvsim
$ dvsim src/spi_host/dv/spi_host_sim_cfg.hjson -i spi_host_smoke
$ dvsim src/spi_host/dv/spi_host_sim_cfg.hjson -i nightly --cov

# Option 2: Direct uv invocation against pinned third_party/caliptra-rtl/tools/dvsim/python
$ uv run --project third_party/caliptra-rtl/tools/dvsim/python dvsim \
    src/spi_host/dv/spi_host_sim_cfg.hjson -i all --cov

# Option 3: Standalone VCS flat-filelist build & run (pass +dump_waves or +waves for FSDB)
$ export CALIPTRA_SS_ROOT=$(pwd)
$ vcs -sverilog -full64 -ntb_opts uvm-1.2 -timescale=1ns/1ps \
    +define+UVM +define+UVM_NO_DEPRECATED +define+UVM_REGEX_NO_DPI \
    +define+SIMULATION +define+CLP_ASSERT_ON +define+INC_ASSERT -top tb \
    -f $CALIPTRA_SS_ROOT/src/spi_host/config/spi_host_tb_flat.vf -R \
    +UVM_TESTNAME=spi_host_base_test +UVM_TEST_SEQ=spi_host_smoke_vseq
```

## Testplan
* [`src/spi_host/data/spi_host_testplan.hjson`](../data/spi_host_testplan.hjson)
