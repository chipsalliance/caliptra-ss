# Caliptra SS UART DV Document

## Goals

*   **DV**
    *   Verify all Caliptra Subsystem (`caliptra-ss`) UART IP features and its
        AXI4 subordinate wrapper (`uart_axi`) by running dynamic simulations
        with a SystemVerilog/UVM-based testbench.
    *   Develop and run all tests based on the [testplan](#testplan) below
        towards closing code, assertion, and functional coverage on the IP and
        all of its sub-modules.
*   **Assertions / Protocol Compliance**
    *   Verify AXI4 subordinate interface behavior, internal TileLink-UL
        protocol compliance (`tlul_assert`), and security countermeasures
        (incoming H2D and outgoing D2H bus command/response/data SECDED
        integrity and one-hot register write-enable checks) via SVA assertions.

## Design Features

For detailed information on Caliptra SS UART design features, please see the
[UART design specification](../README.md). Key hardware parameters in
`caliptra-ss`:

*   **External Bus Interface:** AXI4 Subordinate (`uart_axi` wrapping `axi2tlul`
    and `caliptra_ss_uart`)
*   **Serial Interface:** 2-pin full-duplex asynchronous UART (`cio_rx_i`,
    `cio_tx_o`, `cio_tx_en_o`)
*   **FIFOs:** 32-byte TX FIFO and 64-byte RX FIFO (`caliptra_prim_fifo_sync`)
*   **Interrupts:** 9 interrupt lines (`tx_watermark`, `rx_watermark`,
    `tx_done`, `rx_overflow`, `rx_frame_err`, `rx_break_err`, `rx_timeout`,
    `rx_parity_err`, `tx_empty`)

## Testbench Architecture

The Caliptra SS UART testbench is constructed on top of the `caliptra-ss` DV
library (`dv_lib_pkg`, `csr_utils_pkg`, `dv_utils_pkg`) and uses an AXI4 Manager
VIP agent (`axi_agent`) to drive register and FIFO accesses into the `uart_axi`
DUT.

### Top-Level Testbench

The top-level testbench is located at `src/uart/dv/tb/tb.sv`. It instantiates
the top-level AXI-wrapped UART DUT module `uart_axi`
(`src/uart/rtl/uart_axi.sv`), which integrates:

*   `axi2tlul` (`src/axi2tlul/rtl/axi2tlul.sv`): AXI4 subordinate (`axi_sub`)
    and AXI-to-TLUL shim (`sub2tlul`) with SECDED command/data integrity
    generation (`axi2tlul_cmd_intg_gen`).
*   `caliptra_ss_uart` (`src/uart/rtl/uart.sv`): UART register block
    (`caliptra_ss_uart_reg_top`) and UART core (`caliptra_ss_uart_core`,
    `caliptra_ss_uart_tx`, `caliptra_ss_uart_rx`).

In addition, `tb.sv` instantiates the following interfaces, connects them to the
DUT, and registers their virtual interface handles in `uvm_config_db`:

*   **Clock and reset interface:** `clk_rst_if`
    (`third_party/caliptra-rtl/tools/dv-classes/common_ifs/clk_rst_if.sv`)
*   **AXI4 subordinate interfaces:** `axi_if`, `axi_read_request_if`,
    `axi_read_data_if`, `axi_write_request_if`, `axi_write_data_if`, and
    `axi_write_response_if` (`tools/dv-classes/axi_agent/`)
*   **UART serial I/O interface:** `uart_if`
    (`tools/dv-classes/uart_agent/uart_if.sv`)
*   **Interrupt pin interface:** `pins_if #(NUM_MAX_INTERRUPTS) intr_if`
    (`third_party/caliptra-rtl/tools/dv-classes/common_ifs/pins_if.sv`)
*   **Security countermeasure & internal monitor interfaces:** `uart_sec_cm_if`
    and `uart_nf_if` (`src/uart/dv/env/`)

### Common DV Utility Components

The following shared packages provide generic base classes, register access
utilities, and helper macros across `caliptra-ss`:

*   `common_ifs` (`third_party/caliptra-rtl/tools/dv-classes/common_ifs`)
*   `dv_utils_pkg` (`third_party/caliptra-rtl/tools/dv-classes/dv_utils`)
*   `csr_utils_pkg` (`third_party/caliptra-rtl/tools/dv-classes/csr_utils`)
*   `dv_lib_pkg` (`third_party/caliptra-rtl/tools/dv-classes/dv_lib`)

### Global Types & Methods

All common types, watermark/break helper functions, and parameters
(`MAX_RX_WATERMARK_LVL`, `MAX_TX_WATERMARK_LVL`, `NUM_INTRS`, `uart_intr_e`) are
defined in `uart_env_pkg` (`src/uart/dv/env/uart_env_pkg.sv`).

### AXI Agent

`uart_env` instantiates `axi_mgr_agent` (`tools/dv-classes/axi_agent`), which
drives and independently monitors AXI4 read and write transactions across all 5
AXI channels (`AR`, `R`, `AW`, `W`, `B`). It is paired with `axi_reg_adapter` to
translate UVM RAL operations (including per-transaction byte-enable extensions
via `axi_reg_op_item` on `uvm_reg_item::extension`) into AXI4 bus
transactions.

### UART Agent

`uart_agent` (`tools/dv-classes/uart_agent`) is used to drive and monitor serial
UART RX/TX transactions and collect serial functional coverage on direction,
data, parity, baud rate, and mid-transfer resets. Supported baud rates
(`baud_rate_e`) include: `9600`, `115200`, `128Kbps`, `230400`, `256Kbps`,
`1Mbps (1000000)`, and `1.5Mbps (1500000)`.

### UVM RAL Model

The UART UVM RAL model (`uart_reg_block`) is defined in
`src/uart/dv/env/uart_ral_pkg.sv` (generated from `src/uart/data/uart.hjson`)
and compiled via FuseSoC core `lowrisc:dv:uart_ral_pkg`.

### Stimulus Strategy

#### Test Sequences

All virtual test sequences reside in `src/uart/dv/env/seq_lib/` and extend
`uart_base_vseq` (`src/uart/dv/env/seq_lib/uart_base_vseq.sv`). Commonly used
tasks in `uart_base_vseq` include:

*   `uart_init`: Configures UART control, baud rate (`NCO`), interrupt enable,
    timeout, and FIFO watermark CSRs with randomized values.
*   `send_tx_byte` / `write_wdata_with_mask` / `access_data_fifo`: Writes single
    or multi-byte payloads to `WDATA` over AXI while propagating explicit byte
    enables (`wstrb = 4'b0001` for partial-word byte writes) through both the
    AXI bus transaction and RAL/scoreboard prediction.
*   `send_rx_byte` / `drive_rx_error_byte`: Drives a serial byte (with optional
    parity or framing error) onto `cio_rx_i` via `uart_agent`.

Key test sequences in `src/uart/dv/env/seq_lib/`:

*   `uart_smoke_vseq`: Basic TX/RX byte transmission, reception, CSR/FIFO
    storage isolation, partial-word (`4'b0001`) bus-write checks, and
    status/FIFO/interrupt scoreboard negative fault-injection self-tests.
*   `uart_tx_rx_vseq`: Concurrent randomized full-duplex TX/RX transfers with
    mid-frame `STATUS`/`FIFO_STATUS` reads, random inter-byte delays, TX FIFO
    buffering while `CTRL.TX == 0`, and `CTRL.NCO == 0` baud-tick gating.
*   `uart_fifo_full_vseq`: Fills TX and RX FIFOs to capacity (32-byte TX FIFO,
    64-byte RX FIFO) and drains them.
*   `uart_fifo_overflow_vseq`: Drives beyond FIFO capacity to verify RX/TX FIFO
    overflow behavior, `rx_overflow` interrupt, and full 64-byte drain integrity
    after overflow.
*   `uart_fifo_reset_vseq`: Exercises `FIFO_CTRL.RXRST` and `FIFO_CTRL.TXRST`
    across all FIFO fill levels.
*   `uart_intr_vseq`: Exhaustively verifies all 9 UART interrupts
    (`tx_watermark`, `rx_watermark`, `tx_done`, `rx_overflow`, `rx_frame_err`,
    `rx_break_err`, `rx_timeout`, `rx_parity_err`, `tx_empty`), including
    frame-error RX FIFO exclusion (normal and near-full `rxlvl == 63` boundary),
    full-FIFO dropped-byte timeout non-restart, boundary `TIMEOUT_CTRL.VAL` (`0`
    and `24'hFF_FFFF`), and line break detection across all programmable break
    character levels (`RXBLVL`: 2, 4, 8, 16 chars).
*   `uart_rx_parity_err_vseq`: Verifies even and odd parity checking and
    `rx_parity_err` assertion.
*   `uart_rx_oversample_vseq`: Tests 16x oversampling and `VAL` register
    capture.
*   `uart_noise_filter_vseq` & `uart_rx_start_bit_filter_vseq`: Verifies
    3-sample majority noise filtering across all 16 oversample bit positions
    (`CTRL.NF=1` vs. `CTRL.NF=0`) and start-bit glitch rejection.
*   `uart_tx_ovrd_vseq`: Deterministically and randomly verifies direct TX pin
    override control via `OVRD.TXEN` and `OVRD.TXVAL`.
*   `uart_loopback_vseq`: Verifies system loopback (`CTRL.SLPBK`), line loopback
    (`CTRL.LLPBK`), and RX FIFO isolation during line loopback.
*   `uart_perf_vseq` & `uart_long_xfer_wo_dly_vseq`: Back-to-back streaming
    performance, zero-delay transfers, continuous `±3%` (`±2%` at 1 Mbps on
    `<48 MHz` clocks) RX baud-rate tolerance across `8N1`/`8E1`/`8O1`, and
    `+8.5%` out-of-tolerance drift detection.
*   `uart_reg_access_err_vseq` & `uart_sec_cm_vseq`: Verifies AXI error
    responses (`SLVERR`), unmapped/sub-word accesses, one-hot write-enable fault
    injection (`u_prim_reg_we_check`), and TileLink H2D command/data ECC
    check-bit and payload-bit SECDED fault injection.
*   `uart_axi_toggle_vseq`: Exercises AXI4 burst types (`FIXED`, `INCR`,
    `WRAP`), burst lengths, transfer sizes, stall cycles, address/data bus
    toggles, and shared `axi_agent` self-checks (null cloning, out-of-range ID
    reporting/wire-masked routing, and `en_assert` active-width SVA masking).
*   `uart_stress_all_vseq` & `uart_stress_all_with_rand_reset_vseq`: Runs
    randomized combinations of all sequences with and without asynchronous
    hardware resets (`rst_ni`).
*   `uart_common_vseq`: Runs automated CSR verification suites (`csr_hw_reset`,
    `csr_rw`, `csr_bit_bash`, `csr_aliasing`, `same_csr_outstanding`,
    `csr_mem_rw_with_rand_reset`, and `intr_test`).

#### Functional Coverage

Functional coverage is collected across 17 covergroups in the AXI monitors, UART
agent, and UART environment:

*   **AXI4 Channel Covergroups (`tools/dv-classes/axi_agent/`):**
    *   `axi_monitor_ar_cg` (`axi_monitor_ar.svh`) & `axi_monitor_aw_cg`
        (`axi_monitor_aw.svh`): Burst type (`FIXED`, `INCR`, `WRAP`), burst
        size, burst length, lock, handshake stall cycles, and `cx_burst_len`
        cross.
    *   `axi_monitor_w_cg` (`axi_monitor_w.svh`): Write strobes (`wstrb`),
        `wlast`, and stall cycles.
    *   `axi_monitor_b_cg` (`axi_monitor_b.svh`) & `axi_monitor_r_cg`
        (`axi_monitor_r.svh`): Response status (`OKAY`, `SLVERR`), `rlast`, and
        stall cycles.
*   **UART Agent Covergroups
    (`tools/dv-classes/uart_agent/uart_agent_cov.sv`):**
    *   `uart_cg`: Direction (`UartTx`, `UartRx`), data byte values, parity
        enable/odd-even mode, and baud rate.
    *   `uart_reset_cg`: Asynchronous reset across every bit position (start, 8
        data, parity, stop) for both TX and RX.
*   **UART Environment Covergroups (`src/uart/dv/env/uart_env_cov.sv`):**
    *   `rx_fifo_level_cg` & `tx_fifo_level_cg`: All RX/TX FIFO occupancy levels
        (`0..64` RX, `0..32` TX) crossed with FIFO reset.
    *   `baud_rate_w_core_clk_cg`: Cross of all supported baud rates and core
        clock frequencies.
    *   `tx_watermark_cg` & `rx_watermark_cg`: All TX and RX watermark interrupt
        levels.
    *   `rx_break_err_cg`: Break interrupt across all 4 `RXBLVL` settings
        (`0..3`).
    *   `rx_timeout_cg`: RX timeout interrupt across disjoint small (`[0:20]`),
        medium (`[21:50]`), and large (`[51:24'hff_ffff]`) timeout intervals.
    *   `rx_parity_err_cg`: Parity error interrupt across even and odd parity
        modes.
    *   `noise_filter_cg`: All 3-bit majority noise filter sample combinations.
    *   `intr_test_cg`: Dedicated coverage of software-forced interrupts via
        `INTR_TEST` across all 9 UART interrupt bits (strictly separated from
        natural hardware interrupt covergroups).

### Self-Checking Strategy

#### Scoreboard

`uart_scoreboard` (`src/uart/dv/env/uart_scoreboard.sv`) performs end-to-end
checking across CSR and serial interfaces:

*   **CSR Callback & AXI Read-Address Tracking (`uart_reg_cbs` +
    `read_request_vif`):** Tracks frontdoor CSR
    pre-read/pre-write/post-write/post-read phases and AXI `AR` handshakes
    (`process_axi_read_addr_phase`), independently predicts `STATUS` (`TXFULL`,
    `RXFULL`, `TXEMPTY`, `RXEMPTY`, `TXIDLE`, `RXIDLE`), `FIFO_STATUS` (`TXLVL`,
    `RXLVL`), and `INTR_STATE` (`[8:0]` plus hardware interrupt output pins
    `intr_vif`), and checks reserved-zero CSR fields on reads.
*   **UART Serial Analysis FIFOs (`uart_tx_fifo`, `uart_rx_fifo`):** Compares
    transmitted serial frames against accepted `WDATA` byte writes (including
    when `CTRL.TX == 0`), predicts `RDATA` reads across full 64-byte FIFO drains
    (including after `rx_overflow`), and models loopback, noise filtering,
    parity/framing/break errors, RX timeouts, and FIFO/hardware resets.

#### Assertions

*   **TL-UL Protocol, Security Countermeasure & UART Invariant Assertions:**
    `src/uart/dv/sva/uart_bind.sv` enforces an elaboration-time `CLP_ASSERT_ON`
    compile guard, binds `tlul_assert` (`src/tlul/rtl/tlul_assert.sv`) to
    `caliptra_ss_uart`, instantiates `tlul_rsp_intg_chk`
    (`FpvSecCmTlulRspIntgCheck_A`) to verify outgoing D2H response/data SECDED
    integrity, checks H2D integrity and one-hot write-enable error latching
    (`RegWeOnehotCheck_A`, `FpvSecCmTlulIntgCheck_A`,
    `FpvSecCmTlulIntgBlocksSideEffect_A`, `UartIntgErrSticky_A`,
    `UartIntgErrKnown_A`), and asserts `UartTxDataStable_A`,
    `UartTxIdleImpliesEmpty_A`, and `UartFifoLevelBound_A`.
*   **RTL Assertions (`+define+CLP_ASSERT_ON`):** Both
    `src/uart/dv/uart_sim_cfg.hjson` and `src/uart/Makefile` compile with
    `+define+CLP_ASSERT_ON` and `-assert svaext`, activating all concurrent
    `CALIPTRA_ASSERT` and `CALIPTRA_ASSERT_KNOWN` checks across `uart.sv`,
    `uart_reg_top.sv`, `axi_sub_*`, `caliptra_prim_fifo_sync`,
    `caliptra_prim_onehot_check`, and `tlul_assert`.

## Building and Running Tests

Tests and regressions are built and executed using `dvsim`
(`src/uart/dv/uart_sim_cfg.hjson` inside the Nix shell launched via
`nix develop --no-write-lock-file 'git+file://.?submodules=1#caliptra-dvsim'`) or
standalone via `src/uart/Makefile`:

*   **Run a single test via `dvsim` (e.g. `uart_smoke`):**

    ```console
    $ dvsim src/uart/dv/uart_sim_cfg.hjson -t vcs -i uart_smoke
    ```

*   **Run a single test or quick smoke suite via standalone
    `src/uart/Makefile`:**

    ```console
    $ CALIPTRA_SS_ROOT=$(pwd) make -C src/uart vcs SEQ=uart_smoke_vseq SEED=1
    $ CALIPTRA_SS_ROOT=$(pwd) make -C src/uart smoke
    ```

*   **Run the `smoke` regression (7 simulation test targets configured in
    `uart_sim_cfg.hjson` with `reseed: 1`):**

    ```console
    $ dvsim src/uart/dv/uart_sim_cfg.hjson -t vcs -i smoke
    ```

*   **Run the `ci` regression (all 26 simulation test targets, 1 seed each):**

    ```console
    $ dvsim src/uart/dv/uart_sim_cfg.hjson -t vcs -i ci
    ```

*   **Run the full `nightly` regression with code, assertion, and functional
    coverage (26 simulation test targets, 1,278 seeds):**

    ```console
    $ dvsim src/uart/dv/uart_sim_cfg.hjson -t vcs -i nightly
    ```

### Regression Targets & Seed Breakdown

The configuration in `src/uart/dv/uart_sim_cfg.hjson` (together with
`tools/dvsim/tests/csr_tests.hjson` and `tools/dvsim/tests/intr_test.hjson`)
defines **26 simulation test targets** totaling **1,278 simulation seeds** (plus
4 non-simulation `dvsim` build/coverage pipeline steps: `default`,
`cover_reg_top`, `cov_merge`, and `cov_report`):

*   **Automated CSR tests (`cover_reg_top` build mode — 6 targets, 18 seeds):**
    `uart_csr_hw_reset` (1), `uart_csr_rw` (5), `uart_csr_bit_bash` (1),
    `uart_csr_aliasing` (1), `uart_same_csr_outstanding` (5), and
    `uart_csr_mem_rw_with_rand_reset` (5).
*   **Automated interrupt CSR test (`cover_reg_top` build mode — 1 target, 10
    seeds):** `uart_intr_test` (10).
*   **Functional, protocol-error, countermeasure & stress tests (`default` build
    mode — 19 targets, 1,250 seeds):** 17 targets at `reseed: 50` (850),
    `uart_fifo_reset` at `reseed: 300` (300), and
    `uart_stress_all_with_rand_reset` at `reseed: 100` (100).

### Coverage Configuration & Exclusions

*   **Compile-time hierarchy configuration (`-cm_hier`):**
    `src/uart/dv/cov/uart_cover.cfg`
*   **Coverage exclusion file (`-elfile`):** `src/uart/dv/cov/uart_cov_excl.el`

## Testplan

*   [UART Testplan](../data/uart_testplan.hjson)
*   [UART Security Countermeasures Testplan](../data/uart_sec_cm_testplan.hjson)
