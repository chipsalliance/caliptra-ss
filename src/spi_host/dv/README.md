# Caliptra-SS SPI_HOST DV Document

## Goals
* **DV**
  * Verify all `caliptra_ss_spi_host` IP features in dynamic SystemVerilog/UVM simulation across dual chip-select (`NumCS = 2`) and 8-entry command queue (`CmdDepth = 8`) configurations.
  * Exercise all testpoints in [`spi_host_testplan.hjson`](../data/spi_host_testplan.hjson) with end-to-end scoreboard checking enabled across all functional, error, reset, CSR, and interrupt tests.
* **Protocol & Pin Assertions (SVA)**
  * Continuously verify TL-UL device protocol compliance, SPI whole-cycle data/enable stability across `CS0`/`CS1`, and passthrough pin invariants via bound SystemVerilog assertions.

## Design & Register Specification
* **RTL Top-Level**: [`src/spi_host/rtl/spi_host.sv`](../rtl/spi_host.sv) (`caliptra_ss_spi_host`)
* **AXI Subsystem Wrapper**: [`src/spi_host/rtl/spi_host_axi.sv`](../rtl/spi_host_axi.sv)
* **Register Definitions**:
  * SystemRDL: [`src/spi_host/rtl/spi_host.rdl`](../rtl/spi_host.rdl)
  * HJSON RAL Spec: [`src/spi_host/data/spi_host.hjson`](../data/spi_host.hjson)
  * Generated RTL Package / Top: [`src/spi_host/rtl/spi_host_reg_pkg.sv`](../rtl/spi_host_reg_pkg.sv), [`src/spi_host/rtl/spi_host_reg_top.sv`](../rtl/spi_host_reg_top.sv)
  * UVM RAL Package: [`src/spi_host/dv/env/spi_host_ral_pkg.sv`](env/spi_host_ral_pkg.sv)

## Testbench Architecture
The SPI_HOST UVM verification environment is built on `dv_base_env` / `dv_lib_pkg` and resides under [`src/spi_host/dv/`](.).

### Top-Level Testbench (`src/spi_host/dv/tb.sv`)
[`tb.sv`](tb.sv) instantiates `caliptra_ss_spi_host #(.NumCS(2), .CmdDepth(8))` alongside:
* **Clock & Reset Interface**: `clk_rst_if` driving `clk` and active-low `rst_n`.
* **AXI Manager Sub-Interfaces**: `axi_write_request_if`, `axi_write_data_if`, `axi_write_response_if`, `axi_read_request_if`, and `axi_read_data_if` driven by `axi_mgr_agent` (`tools/dv-classes/axi_agent/`) through the testbench AXI-to-TL-UL bridge (propagating byte strobes, `SLVERR` error responses, and TL-UL `cmd_intg` ECC fault injection).
* **SPI Bus & Dual NOR Flash Models**: `spi_if` (`tools/dv-classes/spi_agent/`) with tri-state `sd[3:0]` pullups and two `spiflash` behavioral NOR flash instances (`gen_spi_flash[0..1]`, one per chip select `CS0` and `CS1`).
* **Interrupt & Integrity Pins**: `pins_if #(2)` monitoring `{intr_spi_event_o, intr_error_o}` and `pins_if #(1)` monitoring/controlling `intg_error_o` fault injection (replacing OpenTitan's alert channel interface in Caliptra-SS).
* **Passthrough & Passive FSM Observer Interfaces**: `spi_passthrough_if` and `spi_host_fsm_if` (purely passive observer exposing `u_fsm.state_q`, `u_fsm.bit_cntr_q`, and `u_fsm.sw_rst_i` with zero internal RTL `force` statements).

### Compile-Time Configuration Parameters
| Parameter | Value | Description |
| :--- | :---: | :--- |
| `SPI_HOST_NUM_CS` (`NumCS`) | `2` | Dual active-low chip selects (`CS0`, `CS1`) with independent `CONFIGOPTS_0` (`0x14`) and `CONFIGOPTS_1` (`0x18`) CSRs; passthrough muxing is structurally disabled (`gen_passthrough_ignore`). |
| `SPI_HOST_CMD_DEPTH` (`CmdDepth`) | `8` | 8-segment command descriptor FIFO depth (`u_cmd_queue`). |
| `SPI_HOST_TX_DEPTH` (`TxDepth`) | `72` | 72-word TX data FIFO (`73` words including `u_select` packer stage). |
| `SPI_HOST_RX_DEPTH` (`RxDepth`) | `64` | 64-word RX data FIFO. |
| `SPI_HOST_BYTEORDER` (`ByteOrder`) | `1` | Little-Endian byte ordering across `TXDATA` and `RXDATA` windows. |

### Key Package Types (`src/spi_host/dv/env/spi_host_env_pkg.sv`)
```systemverilog
typedef struct {
  rand bit        cpol;
  rand bit        cpha;
  rand bit        fullcyc;
  rand bit [3:0]  csnlead;
  rand bit [3:0]  csntrail;
  rand bit [3:0]  csnidle;
  rand bit [15:0] clkdiv;
} spi_host_configopts_t;

typedef struct {
  rand bit        spien;
  rand bit        output_en;
  rand bit        sw_rst;
  rand bit [31:0] csid;
  rand bit [7:0]  tx_watermark; // CONTROL[15:8], reset 8'h00
  rand bit [7:0]  rx_watermark; // CONTROL[7:0],  reset 8'h7F
} spi_host_ctrl_t;

typedef struct {
  rand spi_mode_e mode;         // Standard (0), Dual (1), Quad (2), RsvdSpd (3)
  rand spi_dir_e  direction;    // None (0), RxOnly (1), TxOnly (2), Bidir (3)
  rand bit        csaat;        // COMMAND[9]
  rand bit [8:0]  len;          // COMMAND[8:0] (transfer length = len + 1)
} spi_host_command_t;
```

### Bus & Peripheral Agents
* **AXI Manager Agent (`tools/dv-classes/axi_agent`)**: Drives frontdoor CSR and `TXDATA`/`RXDATA` window transactions via `axi_mgr_register_layer_vseq` and `axi_reg_adapter` (preserving sub-word `byte_en` strobes and handling in-flight reset cancellation via `axi_status_item` without `UVM_FATAL [PUTRSP]`).
* **SPI Agent (`tools/dv-classes/spi_agent`)**: Configured in `Device` monitor mode with 4-state `logic [3:0] plain_data_q[$]` per-SCK-edge bus sampling (`enable_plain_sampling = 1`) across `CS0` and `CS1` (`CSB_WIDTH = 2`, `NUM_CSB = 2 ** CSB_WIDTH = 4`).

## Stimulus & Self-Checking Strategy

### Virtual Sequences (`src/spi_host/dv/env/seq_lib/`)
All 15 functional sequences and `spi_host_intr_test` (16 tests / 155 seeds; zero `+en_scb=0` overrides in `src/spi_host/dv/`) run with end-to-end scoreboard checking enabled (`en_scb = 1`), alongside the 6 common CIP CSR sequences (`18` seeds under `csr_tests_mode`):
* `spi_host_smoke_vseq`: Dual-CS NOR flash page program & quad-read, all segment speed/direction/CSAAT transitions, all 8 valid `TXDATA` byte-enable masks (including `4'b0110`), partial-word (`1, 2, 3, 5, 9` byte) `TxOnly`/`RxOnly`/`Bidir` checks, `OUTPUT_EN = 0 -> 1` queued-command execution, `CS1` Mode 3 transfer, sub-word CSR `SLVERR` & backpressure retention, TL-UL `cmd_intg` fault injection, and negative scoreboard self-checks (TX mismatch, RX mismatch, and 4-state floating-`1'bz` active-lane rejection on `8'h00` payloads).
* `spi_host_dual_cs_vseq`: Independent `CONFIGOPTS_0` / `CONFIGOPTS_1` timing, same-address `CS0`/`CS1` flash isolation, `CSAAT = 1` active CS switching (`IdleCSBActive -> WaitTrail -> CSBSwitch`) across `CPHA = 0/1`, mid-flight `CONFIGOPTS_1` queued-command snapshotting, `CS1` mode/lead/trail/idle fault negative controls, and `CSID >= NumCS` `csidinval` error recovery.
* `spi_host_speed_vseq` & `spi_host_upper_range_clkdiv_vseq`: Scoreboard-checked `Bidir` and `TxOnly` transfers sweeping `CPOL`, `CPHA`, `FULLCYC`, `CSNLEAD`, `CSNTRAIL`, `CSNIDLE`, and `CLKDIV` across `CS0` and `CS1`, including 100% unforced (`fast_mode = 0`) `Bidir` TX+RX and physical SCK half-period verification at `CLKDIV = 16'h0100` (`257` core clocks) and max `CLKDIV = 16'hFFFF` (`65,536` core clocks).
* `spi_host_sw_reset_vseq`: Randomized mid-transfer `CONTROL.SW_RST` assertions plus passive FSM state observation (`WaitLead`, `CSBSwitch`, `WaitTrail`, `WaitIdle`, `InternalClkHigh`) triggering real bus `CONTROL.SW_RST` writes and post-reset checked `Bidir` recovery.
* `spi_host_error_cmd_vseq` & `spi_host_overflow_underflow_vseq`: Bus-driven `csidinval`, `cmdinval`, `cmdbusy`, `accessinval` (all 8 invalid byte masks), `underflow`, and `overflow` error/interrupt verification with post-error checked `Bidir` recovery.
* `spi_host_event_vseq`, `spi_host_spien_vseq`, `spi_host_status_stall_vseq`, `spi_host_idlecsbactive_vseq`, `spi_host_passthrough_mode_vseq`, `spi_host_flash_vseq`, `spi_host_performance_vseq`, `spi_host_stress_all_vseq`: Event watermarks, mid-transfer `SPIEN` stall/resume, TX/RX FIFO stall stretching, `CSAAT = 1` parking, passthrough tie-off verification (`NumCS = 2`), and multi-sequence stress.
* Common CIP tests (`spi_host_base_vseq`): `csr_hw_reset`, `csr_rw`, `csr_bit_bash`, `csr_aliasing`, `same_csr_outstanding`, `intr_test`, and `csr_mem_rw_with_rand_reset` (concurrent CSR + `TXDATA`/`RXDATA` AXI traffic overlapping randomized `HARD` reset assertion + post-reset checked `Bidir` recovery).

### Scoreboard (`src/spi_host/dv/env/spi_host_scoreboard.sv`)
* **4-State Pin Integrity (`SCB-PIN-01`)**: Preserves 4-state `logic` samples from `spi_if.sio` through `spi_monitor` and `plain_data_fifo`; explicitly flags `1'bz`/`1'bx` (`$isunknown`) on active driven TX lanes (`sio[0]` in `Standard`, `sio[1:0]` in `Dual`, `sio[3:0]` in `Quad`) even when expected TX data is `8'h00`, while permitting high-Z on unused lanes.
* **Per-CS Mode, Divider & Timing Prediction**: Snapshots `CSID` and `CONFIGOPTS[csid]` per queued command, tracks `pending_lead_cfg_q[cs]` across back-to-back and `CSAAT = 1` envelopes, and checks `CSNLEAD`, `CSNTRAIL`, `CSNIDLE`, and `CSAAT` (`csaat == 0` deassertion & extra-SCK check vs. `csaat == 1` hold check) per active chip select.
* **Command Queue Staging**: Models `u_cmd_queue` (`staged_cmd_q`) across `CONTROL.SPIEN`, `CONTROL.OUTPUT_EN`, `ERROR_STATUS` (`enb_error`), and `CONTROL.SW_RST`.
* **Operational Timing Coverage**: Samples `config_opts_cg` and `different_ch_settings_cg` upon completed scoreboard-checked segments in `compare_tx_trans()` rather than on raw CSR writes.

### Assertions (`src/spi_host/dv/sva/`)
[`spi_host_bind.sv`](sva/spi_host_bind.sv) is instantiated in `tb.sv` and binds:
* `tlul_assert #(.EndpointType("Device"))`: Verifies TL-UL request/response protocol and integrity invariants on `caliptra_ss_spi_host`.
* `spi_host_data_stable_sva #(.NumCS(2))`: Verifies `cio_sd_i` and `cio_sd_en_o` remain stable across the active SCK sampling phase for the active chip select's `(CPOL, CPHA)` mode.
* Passthrough assertions (`Sck_A`, `Sck_En_A`, `Csb_A`, `Csb_En_A`, `S_En_A`, `Sd_O_A`, `Sd_I_A` in `tb.sv` and `PassthroughNumCSCompat_A` / `PassthroughConn_A` in `spi_host.sv`).
* **Scope Note on `spi_host_csr_assert_fpv`**: The `spi_host_csr_assert_fpv` bind in [`spi_host_bind.sv`](sva/spi_host_bind.sv) remains intentionally commented out because standalone OpenTitan FPV CSR assertion collateral is not packaged in Caliptra-SS; CSR reset, read/write, bit-bash, aliasing, write-enable one-hot (`u_prim_reg_we_check`, with only disconnected alert-port `AssertConnected_A` disabled), and bus-integrity checks are verified dynamically across the UVM CSR test suite and `spi_host_smoke_vseq`.

### Coverage Scope & Exclusions (`src/spi_host/config/`)
* **Hierarchy Configuration ([`cov_hier.cfg`](../config/cov_hier.cfg))**: Collects code coverage on `tb.dut` (`caliptra_ss_spi_host`, `u_reg` decode & writable/RW1C CSR subregs, `u_cmd_queue`, `u_data_fifos`, and `u_spi_core.*`) while scoping out pre-verified `caliptra_prim`/`tlul` bus-socket primitives, pure wire-through RO status subregs, `u_window`, and bound DV/SVA collateral.
* **Waivers ([`cov_waivers.el`](../config/cov_waivers.el))**: Wired into `vcs_cov_excl_files` in both [`spi_host_common_sim_cfg.hjson`](spi_host_common_sim_cfg.hjson) and [`spi_host_sim_cfg.hjson`](spi_host_sim_cfg.hjson), waiving structurally unreachable FSM/shift-register/packer/sync-FIFO condition rows (e.g., `ClearOnRead = 0`, `Secure = 0`, validated `speed != 2'b11`, `TxDepth`/`RxDepth < 128` MSB depth bits) and tied-off TL-UL bridge port bits on `tb.dut` / `u_reg`.

## Building and Running Tests
Tests and regressions are executed with `dvsim.py` against [`spi_host_sim_cfg.hjson`](spi_host_sim_cfg.hjson):
```console
# Run smoke test
$ python3 third_party/caliptra-rtl/tools/dvsim/dvsim.py \
    src/spi_host/dv/spi_host_sim_cfg.hjson -i spi_host_smoke

# Run full 22-test regression with code and functional coverage
$ python3 third_party/caliptra-rtl/tools/dvsim/dvsim.py \
    src/spi_host/dv/spi_host_sim_cfg.hjson -i all --cov
```

## Testplan
* [`src/spi_host/data/spi_host_testplan.hjson`](../data/spi_host_testplan.hjson)
