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

## Running

```
+UVM_TESTNAME=caliptra_ss_usb_dev_reg_rw_test
```

See `caliptra_ss_usb_dev_reg_rw.yml` for the build/plusarg wiring.
