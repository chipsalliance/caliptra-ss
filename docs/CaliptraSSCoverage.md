# Caliptra Subsystem Coverage Dashboard

This section provides an overview of the coverage for the Caliptra Subsystem (SS) and its components. Each subsystem block is linked to its coverage dashboard and notes for further insights.

| Subsystem Block             | Description                                      | Line      | Toggle    | Condition | Branch    | Link to Coverage                  | Notes                                                   |
|-----------------------------|--------------------------------------------------|-----------|-----------|-----------|-----------|-----------------------------------|---------------------------------------------------------|
| **Caliptra SS Top**         | Top-level block of the Caliptra Subsystem.       | 100.00%   |  97.40%   | 100.00%   | 100.00%   | [SS Top Coverage](#)              |                                                         |
| **I3C instance**            | Core implementing the I3C protocol.              |           |  96.71%   |           |           |                                   | Only toggle coverage                                    |
| **I3C Core**                | I3C core.                                        |           |           |           |           | [I3C Core Coverage](#)            | Reusable Module                                    |
| **MCI**                     | Memory Controller Interface.                     | 100.00%   |  97.99%   | 100%      | 100.00%   | [MCI Coverage](#)                 | [MCI Coverage Analysis](#mci-coverage-analysis-summary) |
| **Fuse CTRL (Baseline)**    |                                                  |           |           |           |           | [FCC Baseline Coverage](#)        | Reusable Module                                    |
| **Fuse CTRL (Delta)**       | Fuse Controller with delta changes.              |  97.69%   | 100.99%   | 100.00%   | 100.00%   | [FCC Coverage](#)                 | [Fuse Controller Coverage Notes](#fuse-controller-coverage-analysis)   |
| **LCC (Baseline)**          | Life cycle controller baseline config.           |           |           |           |           | [LCC Baseline Coverage](#)        | Reusable Module                                    |
| **LCC (Delta)**             | Life cycle controller with delta changes.        | 100.00%   | 100.00%   | 100.00%   | 100.00%   |                                   | [LCC Coverage Notes](#life-cycle-controller-coverage-analysis)        |
| **AXI2TLUL**                | AXI to TLUL protocol conversion gasket.          | 100.00%   | 100.00%   | 100.00%   | 100.00%   | [AXI2TLUL Gasket Coverage](#)     | [AXI2TLUL Coverage Notes](#axi2tlul-coverage-analysis)  | 
| **mcu_rom_i**               | MCU ROM instance.                                |           | 100.00%   |           |           |                                   |                                                         |
| **MCU_wrapper**             | Instance of VeeR-EL2 RISC-V Core                 |           | 96.23%    |           |           |                                   | Only toggle coverage                                    |
| **MCU**                     | VeeR-EL2 RISC-V core.                            |           |           |           |           | [VeeR Core Coverage](#)           | Reusable Module                                    |
   ---
## Caliptra Core Coverage Dashboard
This section provides an overview of the coverage for the Caliptra Core and its components. Each core block is linked to its coverage dashboard and notes for further insights.

| Calitptra Core Block   | Description                                         | Line    | Toggle  | Condition | Branch  | Link to Coverage                    | Notes      |
|------------------------|-----------------------------------------------------|---------|---------|-----------|---------|-------------------------------------|-----------------------------|
| **Caliptra Core Top**  | Top-level block of the Caliptra Core.               |         |         |           |         | [Caliptra Core Coverage](#)         | [Coming Soon](#)            |
| **VeerEl2 Core**       | Instance of the VeeR-EL2 RISC-V core.               |         |         |           |         | [RISCV VeeR El2 Coverage](#)        | [Coming Soon](#)            |
| **MLDSA**              | Multi-Lane Digital Signature Accelerator.           |         |         |           |         | [MLDSA FPV Coverage](/docs/coverage_reports/Adams%20Bridge%20FPV%20Coverage%20Report%20from%20Lubis%200611.pdf)             | MLDSA went through FPV and the coverage shows the instance/interface here.            |
| **AES**                | Advanced Encryption Standard block for crypto ops.  |         |         |           |         | [AES Coverage](/docs/coverage_reports/Caliptra%20FPV%20Coverage%20Report%20from%20Lubis.pdf)                  | [Coming Soon](#)            |
| **SOC Interface**      | Interface block for System-on-Chip communication.   |         |         |           |         | [SOC Interface Coverage](#)          | [Coming Soon](#)            |
| **cryptos (ECC, HMAC, SHA, DOE)** | | | | | [Crypto FPV Coveage](/docs/coverage_reports/Caliptra%20FPV%20Coverage%20Report%20from%20Lubis.pdf) |silicon proven through 1.x |


---

# Coverage Analysis Notes

## MCI Coverage Analysis Summary

### Module: i_boot_seqr

#### Coverage Metrics
- **Line Coverage:** complete With exclusions
- **Toggle Coverage:** Complete with exclusions
    - Exclusions on mci_boot_seq_brkpoint and mcu_no_rom_config because we expect these to be static while MCI is out of reset.
    - The following signals only a posedge is seen due to signals being set before MCI is out of reset and the signal propagates through a synchronizer.
        - mci_boot_seq_brkpoint_sync
        - mcu_no_rom_config_sync
    - The following signals only see posedge due to test only validating a flow where the signal is set to trigger a particular MCI flow. This 
        - mci_bootfsm_go
    - Signals that are set only when MCI is out of reset meaning only posedge is seen
        - mcu_reset_once
        - mcu_reset_once_next 
- **FSM Coverage:** Complete with exclusions
   - Transitions into BOOT_IDLE (warm reset) are architecturally only allowed in BOOT_WAIT_CPTRA_GO and BOOT_WAIT_MCU_RST_REQ. All other transitions are not allowed unless it is a cold reset. Cold reset is no different than what we test on all our boot sequences, so no need to add this coverage in our DV env
- **Condition Coverage:** Complete with exclusions
   - Line 356 - expected since (1,0) event is captured by an above case meaning this will never be hit.
- **Branch Coverage:** Complete with exclusions
    - Exclusions due to missing "ELSE" statements that are OK to be missing and we don't expect the FSM to be in "default" state. 

### Module: i_mci_axi_sub_decode

#### Coverage Metrics
- **Line Coverage:** Complete
- **Toggle Coverage:** Complete with exclusions
    - Straps with no expected toggling
        - strap_mci_soc_config_axi_user
            - Randomized in testing
        - strap_mcu_ifu_axi_user
            - Randomized in testing
        - strap_mcu_lsu_axi_user
            - Randomized in testing
        - strap_mcu_sram_config_axi_user
            - Randomized in testing
        - mci_soc_config_req_disable
            - Have directed test setting before MCI is out of reset
        - mci_soc_config_req_force_enable
            - Have directed test setting before MCI is out of reset
- **FSM Coverage:** NA
 
- **Condition Coverage:** Complete

- **Branch Coverage:** Complete

### Module: i_mci_mcu_sram_ctrl

#### Coverage Metrics
- **Line Coverage:** Complete
- **Toggle Coverage:** With exclusions
    - Exclusions due to tieoffs
    - Missing coverage due to not crossing dmi with AXI traffic generating a DMI AXI Collision error. TB is hard to hit this scenario and we are OK with not detecting this error since it is not core functionality and more of a "nice to have" feature

- **FSM Coverage:** NA
 
- **Condition Coverage:** Complete

- **Branch Coverage:** Complete

### Module: i_mci_mcu_trace_buffer

#### Coverage Metrics
- **Line Coverage:** Complete
- **Toggle Coverage:** With exclusions
    - Exclusions added for tieoffs within our design.
    - Exclusions added due to pointers not getting full coverage because size of trace buffer does not fully utilize the 32 bit pointers
- **FSM Coverage:** NA

- **Condition Coverage:** Complete with exclusions

- **Branch Coverage:** Complete with exclusions
    - Exclusions due to "MISSING ELSE" statements

### Module: i_mci_reg_top

#### Coverage Metrics
- **Line Coverage:** With exclusions
- **Toggle Coverage:** With exclusions
    - Many exclusions added due to tieoffs in our design example are agg error signals tied off a SS level.
    - Many exclusions due to counters we only care about it toggling once. Example the interrupt timers
    - The readback_array was also excluded because this is redundant coverage showing if we read certain registers. Better to look at the actual registers than this readback array. 
- **FSM Coverage:** NA
 
- **Condition Coverage:** With exclusions

- **Branch Coverage:** With exclusions

### Module: i_mci_wdt_top

#### Coverage Metrics
- **Line Coverage:** Complete
- **Toggle Coverage:** Complete with exclusions
    - Only missing toggle are the timer1_count and timer2_count upper bits. These counters do not connect externally and we have verified much of this logic within Caliptra. We deem it OK that some of the upper bits haven't been hit after inspecting the RTL. 
- **FSM Coverage:** NA
 
- **Condition Coverage:** 

- **Branch Coverage:** Complete

### Module: mcu_mbox*

#### Coverage Metrics
- **Line Coverage:** Complete
- **Toggle Coverage:** With exclusions
    - Exclusions due to tieoffs in the design
    - MBOX_SRA.addr upper bits never toggle due to size of SRAM in our TB. We tested 2MB SRAM in a size TB but never put into regression. When our ENV supports multiple models we will add this coverage
- **FSM Coverage:** NA
 
- **Condition Coverage:** Complete with exclusions
    - Some impossible conditions cannot be met, so excluded from coverage

- **Branch Coverage:** Complete


---
## Life Cycle Controller Coverage Analysis

The Caliptra-SS life-cycle controller is almost congruent to its OpenTitan
counterpart with two exceptions:

  1. Modified scrap transition flow: Transitions into SCRAP and RMA modes are now
     guarded by a physical pin.
  2. The KMAC block is now integrated directly into the lc_ctrl package.

Functionally, these changes only affect the lc_ctrl_fsm unit which we
analyze more thoroughly below. For the other, modules please
refer to the OpenTitan coverage dashboard:

  https://reports.opentitan.org/hw/ip/lc_ctrl_volatile_unlock_enabled/dv/latest/cov_report/dashboard.html
  https://reports.opentitan.org/hw/ip/lc_ctrl_volatile_unlock_disabled/dv/latest/cov_report/dashboard.html
  https://reports.opentitan.org/hw/ip/kmac_masked/dv/latest/cov_report/dashboard.html
  https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/latest/cov_report/dashboard.html

### Module: lc_ctrl_fsm

#### Line Coverage: 

An invalid transition error is not covered during the token check phases. This
is the second check of this nature. Since there is no update on the error logic,
OpenTitan coverage needs to be taken into account.

  - RTL: lc_ctrl_fsm.sv+492

#### Toggle Coverage: 

Three error ports (token_hash_err_i, token_if_fsm_err_i, otp_prog_err_i) are
not toggled. The former two are toggled, while programming the new lc state
and counter. The logic drives these error signals are not updated and
therefore OpenTitan coverage report is referred.

#### Branch Coverage: 

The transition from the FSM idle state into SCRAP is not covered but will be
covered in upcoming release.

  - RTL: lc_ctrl_fsm.sv+289

The remaining uncovered branches relate directly to the uncovered lines and
toggles mentioned above.

## Fuse Controller Coverage Analysis

The fuse_ctrl is an adapted lightweight variant of the OpenTitan otp_ctrl (Earlgrey-PROD.M6- https://github.com/lowRISC/opentitan/releases/tag/Earlgrey-PROD-M6)
with some of the modules having been removed (KDI, flash interface, EDN).
Some of these units do not contain any changes with respect to their
OpenTitan counterparts:

 - otp_ctrl_ecc_reg
 - otp_ctrl_lci
 - otp_ctrl_lfsr_timer
 - otp_ctrl_part_buf
 - otp_ctrl_part_unbuf
 - otp_ctrl_scrmbl
 - otp_ctrl_token_const

For these units, the reader can refer to the OpenTitan coverage dashboard.

  https://reports.opentitan.org/hw/ip/otp_ctrl/dv/latest/cov_report/dashboard.html

Other modules are part of a customizable, autogenerated group (with the
exception of the newly added fuse_ctrl_filter) based on the shape of the
partition MMAP. From this table, the register file and packages are
bootstrapped via a supplied Python script (gen_fuse_ctrl_partitions.py):

 - otp_ctrl_part_pkg
 - otp_ctrl_prim_reg_top
 - otp_ctrl_reg_pkg

Note that unlike other blocks in Caliptra-SS, the fuse_ctrl uses the OpenTitan
register collateral through an AXI-TLUL adapter; as such its correctness and
robustness is backed by its corresponding OpenTitan test-suite. The remaining
entities contain minor adjustments to streamline their integration into the
Caliptra-SS SoC. We will take a closer look at those:

 - otp_ctrl
 - otp_ctrl_dai
 - otp_ctrl_core_reg_top
 - fuse_ctrl_filter

### Module: otp_ctrl

The top-level otp_ctrl unit features the heaviest modifications with respect to
the baseline OpenTitan variant. It contains the following additions/removals:

  1. FIPS zeroization flow: Broadcasted secrets can be cleared by asserting a
     new input port signal.
       - RTL: otp_ctrl.sv+1314-1350

  2. Removal of unused modules and their associated signals and logic: The
     fuse_ctrl does not feature the key derivation interface, entropy
     distribution network nor any TLUL primitives.
       - Coverage: The top-level still contains some residuals of the TLUL-SRAM
         adapter and is excluded from the report. All other removals are
         properly covered.

  3. Updated alerts: The two-way OpenTitan alert ports have been replaced with
     single-bit signals.
       - Coverage: Not all alerts (fatal_bus_integ_error, fatal_macro_error)
         are exhaustively toggled. This will be remedied by increasing the
         repetition number of the randomized tests or by more directed attempts
         to toggle those faults. All other alerts, which follow the same logic
         are covered.
       - RTL: otp_ctrl.sv+517-644

  4. New volatile lock for the vendor public-key hashes. The optional
     VENDOR_HASHES_PROD_PARTITION will be incrementally locked through a new
     register VENDOR_PK_HASH_VOLATILE_LOCK.
     
       - Coverage: Two conditions in the below statement are not covered. The
         relate to DAI writes that do not target the
         VENDOR_HASHES_PROD_PARTITION while a volatile lock is active. This will
         be fixed by amending the corresponding test with upcoming release. Low-risk as the
         correctness of the cone has been verified.
      	 ```
         // if (1 && 1 && 0 && 1) and if (1 && 1 && 1 && 0) are not covered.
      	 if (dai_cmd == DaiWrite && reg2hw.vendor_pk_hash_volatile_lock != '0 &&
             dai_addr >= prod_vendor_hash_start &&
             dai_addr < prod_vendor_hash_end) begin
           ...
         end
         ```
       - RTL: otp_ctrl.sv+375-412

  5. On-the-fly decoding of life-cycle states: In the fuse_ctrl, individual
     partition can write-restricted to particular life-cycle states. This
     requires an on-the-fly decoding mechanism.
       - RTL: otp_ctrl.sv+415-440

  6. AXI filter wiring: The new fuse_ctrl_filter discards DAI requests based
     on rules in a predefined access table.

       - RTL: otp_ctrl.sv+1024-1076

  7. Incremental broadcast of unlock tokens: Test unlocked state transition
     tokens are broadcasted based on the current life-cycle phase.

       - RTL: otp_ctrl.sv+1352-1370

### Module: otp_ctrl_dai

As mentioned above, the only change to the direct access interface is the
inclusion of a discard signal stemming from the fuse_ctrl_filter module.
It's a lightweight addition that only causes minor functional changes
in the FSM where the write state is now aborted when the discard port
is asserted.

  - RTL: otp_ctrl_dai.sv+415-445

### Module: otp_ctrl_core_reg_top

This module instantiates the fuse_ctrl register file whose shape is determined
both by the MMAP file (read lock and digest registers) and the otp_ctrl.hjson
data sheet the defines the remaining CSRs. Note that the only truly new
register that is not tied to a partition and not found in OpenTitan is the
public-key hash volatile lock.

  - Coverage: Near complete. This is tracked through a dedicated covergroup
    that records whether all writable registers are written and all readable
    ones are read correctly.

### Module: fuse_ctrl_filter

The AXI filter is the only custom unit in the Caliptra-SS fuse_ctrl as such
the coverage metrics are analyzed individual below.

#### Line Coverage: 
Two branches in the IDLE_ST and WDATA_ST are unaccounted for. Each 64-bit
AXI write request should normally cover both of them.

  1. fuse_ctrl_filter.sv+141-145
     ```
      end else if (second_write_addr) begin
        latch_data_id0     = 1'b0;
        latch_data_id1     = 1'b1;
        clear_records      = 1'b0;
        table_fsm_next_st  = WDATA_ADDR_ST;
     ```

  2. fuse_ctrl_filter.sv+189-193
     ```
     end else if (first_write_addr) begin
       table_fsm_next_st = WDATA_ADDR_ST;
       latch_addr_id     = 1'b0;
       latch_data_id0    = 1'b1;
       latch_data_id1    = 1'b0;
     ```

#### Toggle Coverage:

  1. The strap input ports are untoggled as they are set to constant values
     in the testbench. They are excluded from the coverage.

  2. fuse_ctrl_filter.sv+51: The upper bits of the latched fuse address are
     untoggled since the partitions do not occupy the full 32-bit address
     space. They are excluded from coverage.

  3. fuse_ctrl_filter.sv+103: The AXI user ID table is constant and cannot
     be toggled. It is excluded from coverage.

#### FSM Coverage: Complete

Transitions reverting back to the reset state are excluded from coverage
as they cannot be triggered with the existing testbench.

#### Branch Coverage:

The previously mentioned uncovered lines also cause the corresponding branches
to be uncovered.

## AXI2TLUL Coverage Analysis

### Module: axi2tlul

**Overall Coverage:**  
- *Justified Exclusions:*
  - `axi_sub` has been excluded from coverage as it is covered under Caliptra core coverage.
  - TL-UL integrity generation and check are excluded as they are not used in Caliptra SS.


### Module: sub2tlul  
*(instantiated by axi2tlul; contains core gasket logic)*

- **Statement Coverage:**
  - *Note:* Transaction does not transition from `valid_put_txn` (write) to `no_txn` (idle). This is a hole in coverage.

- **Toggle Coverage:**
  - *Note:* Signals where bits are not expected to toggle or where we are not testing toggle of all bits (e.g., data, addr) are excluded.

- **FSM Coverage:** 
  - *Note:* There is no transition from `valid_get_txn` (read) to `valid_put_txn` (write). This is a hole in coverage.

- **Condition Coverage:**
  - *Lines 98-99:*  
    ```systemverilog
    else if (cur_txn == valid_put_txn && tl_i.d_opcode == AccessAck && tl_i.d_valid)
      cur_txn <= no_txn
    ```
    - The scenario where all three conditions are true is never met. Only two conditions are met: `cur_txn == valid_put_txn` and `tl_i.d_opcode == AccessAck`, but `tl_i.d_valid` is false.
    - This appears to be a TL-UL bug, as `d_valid` indicates that the AccessAck response on the D channel is valid.

- **Branch Coverage:**   
  - The branch on lines 98-99 is never hit because the condition never evaluates to true. This appears to be a TL-UL bug.

- **Justified Exclusions:**  
  - Branches where certain combinations of conditions cannot occur based on protocol behavior have been excluded.
