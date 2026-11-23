# caliptra_ss_usb_dev_reg_rw

Single UVM + firmware test that performs register read/write access checking on
BOTH embedded USB device controllers (USBDC0 / dev0 and USBDC1 / dev1) in one
run.

## What it does

The MCU firmware (`caliptra_ss_usb_dev_reg_rw.c`) walks a shared register
disposition table over both device register banks:

- USBDC0 at `USB_DEV0_REG_BASE_ADDR` (0x2000_1000)
- USBDC1 at `USB_DEV1_REG_BASE_ADDR` (0x2001_0000)

Both banks are directly reachable from the MCU LSU AXI master, so the firmware
uses the absolute `USB_DEV0_*` / `USB_DEV1_*` macros (not the compile-time
`USB_DEV_SEL` selection) and requires no RTL change.

Per register the test applies one of two methodologies:

- **RW_CHECK**: write a masked random value, read it back, and require the
  read-back RW bits to equal what was written (compared under `rw_mask`).
- **RO_CHECK**: prove immutability of the read-only bits by performing three
  DIFFERENT writes (0x00000000, 0xA5A5A5A5, 0x5A5A5A5A), reading after each,
  and requiring the RO-masked bits to be identical across all three reads
  (i.e. the register ignored every write).

A register may declare both masks (e.g. DEVCMDSTAT, LPM, INTPLL): the RW compare
runs on `rw_mask` first, then the RO immutability check runs on `ro_mask`.

## DEVCMDSTAT (0x00) handling

Only the side-effect-free RW configuration bits are exercised as writable
(PLL_ON, LPM_SUP, and the four IntOnNAK_* bits). The link/device-state bits
(DEV_ADDR, DEV_EN, DCON, DSUS, LPM_SUS) and the write-1-to-clear change bits are
deliberately NOT written. The reserved / read-only bits are proven immutable.

## RTL hazards honored by construction

1. **Write-before-read**: reading a device register that was never written
   since reset drives X and fires the fatal `DataKnown_A` assertion on the
   dev*_axi read response path. Every included register (RW and RO) is written
   before it is read.
2. **Address aliasing**: the device register file decodes only `haddr[5:2]` (a
   16-register / 4-bit window), so any offset >= 0x40 aliases back into
   0x00-0x3C. The table contains no offset >= 0x40.

## Excluded registers

EPLISTSTART (0x08), DATABUFSTART (0x0C), EPSKIP (0x14), INTSTAT (0x20) and
INTSETSTAT (0x28) are not accessed: they are DMA pointers or W1C/W1S /
self-clearing registers whose write semantics are not a plain RW or RO compare.

## SV side

`caliptra_ss_usb_dev_reg_rw_test` extends `caliptra_ss_usb_base_test` and sets
`caliptra_ss_usb_mem_rw_sequence` as the `main_phase` default sequence on
the host virtual sequencer. This is a standalone register test: the sequence
does NOT bring up the USB link or drive any USB traffic. It simply holds the
run-phase objection open long enough for the firmware to check both banks and
halt. The verdict is produced by two judges:

- the firmware DEBUG_OUT byte (`TB_CMD_TEST_PASS` / `TB_CMD_TEST_FAIL`), and
- the UVM error count checked in `caliptra_ss_usb_base_test::final_phase`.

## HUB_ULPIDEBUG / USB_PHY_REGISTER_ACCESS classification

`usb_hub_phy_access_sweep()` in the firmware exercises the indirect
UTMI+/ULPI PHY access registers on the hub bank (`HUB_ULPIDEBUG`, offset
0x3C) by launching a real `PHY_ACCESS` for a walking-ones/zeros sweep over
`PHY_ADDR`/`PHY_WDATA`, crossed with `PHY_RW`. Only `PHY_MODE=0` (UTMI)
launches a real access - see the `PHY_MODE=1` row below. Target bits for
`USB_PHY_REGISTER_ACCESS` coverage fall into four classes:

| Field / bits                               | Class     | Reason |
|---------------------------------------------|-----------|--------|
| `PHY_ADDR[7:0]`, `PHY_WDATA[15:8]`, `PHY_RW[24]`, `PHY_MODE[31]` (bit toggle only), `PHY_ACCESS[25]` | Testable | Directly driven by this sweep in UTMI mode (`PHY_MODE=0`); `PHY_ACCESS` one-shot set/clear is exercised by every launch. `PHY_MODE[31]`'s own bit toggle is exercised by the plain RW walk (`hub_phydebug_fields`), independent of the live-launch sweep. |
| `PHY_RDATA[23:16]` 1->0 transition           | Testable (partial) | Pre-loaded non-zero via the plain RW path, then cleared by the next real access (HW overwrites it unconditionally on `hub_phy_endtoggle`). |
| `PHY_RDATA[23:16]` 0->1 transition           | TB gap    | `caliptra_ss_top_tb.sv` ties `cptra_ss_usb_utmi_vstatus_i` to constant 0 ("Not modeled by VIP"); in UTMI mode `phy_readdata <= utmi_vstatus`, so `hub_phy_rdata` is always 0 after a real access regardless of `PHY_ADDR`/`PHY_MODE`. A genuine HW-driven 0->1 is not reachable without a TB model change to drive a non-zero `cptra_ss_usb_utmi_vstatus_i`. Not worked around here; reported as a TB gap. |
| `PHY_MODE=1` (ULPI) live `PHY_ACCESS` launch | Waiver    | `phy_endtoggle_r` only toggles via `set_ulpi_phy_endtoggle` (`usb_pie.m.vhdl`), which is driven by the `ulpi_ext_reg` sequencer and requires a live ULPI bus handshake (`ulpi_dir`/`ulpi_nxt` from an actual ULPI PHY). This SoC integration has no ULPI PHY attached (UTMI only), so a `PHY_MODE=1` `PHY_ACCESS` launch can never self-clear - confirmed by a real run (`HUB_ULPIDEBUG.PHY_ACCESS did not self-clear`, `mode=1`). Chip-level waiver (no ULPI PHY on this integration), not a TB gap or RTL bug; the sweep therefore only launches real accesses with `PHY_MODE=0`. |
| Device-bank `USBREG_PHY_*` / `REG_PHY_*` (DEV0/DEV1 PHYDEBUG word, offset 0x3C) | Waiver | `usb_reg_if.m.vhdl:269-276`: with `C_USB_HUB => TRUE` (both device banks in this integration), every `usbreg_phy_*` output is hardwired to `(others => '0')` / `'0'`, and the register select itself is gated `when not(C_USB_HUB)`. These bits can never toggle on this compound by construction; legitimate waiver, not an RTL bug. |


A previous version of `usb_hub_phy_access_sweep()` also attempted to assert
the `PHY_RDATA` 1->0 transition via a dedicated check (pre-load the field,
launch an access with `PHY_ADDR=0`/`PHY_WDATA=0`, and flag a non-zero
readback as a possible RTL issue). That check was removed: it could not
distinguish "HW cleared `PHY_RDATA` via the endtoggle handshake" from "the
field was simply never touched by HW", since nothing else in the same access
writes a non-zero value into `PHY_RDATA` to be cleared. The walking-ones/
zeros sweep above still exercises the toggle through the pre-load-then-clear
pattern per sweep iteration without relying on that vacuous assertion.

## Running

```
+UVM_TESTNAME=caliptra_ss_usb_dev_reg_rw_test
```

See `caliptra_ss_usb_dev_reg_rw.yml` for the build/plusarg wiring.

