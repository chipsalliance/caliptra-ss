# caliptra_ss_usb_dev1_ram_rw

USBDC1 (device1) variant of `caliptra_ss_usb_dev_ram_rw`. Single UVM + firmware
test that performs random read/write access checking on the DMA/SRAM region
(RAM) of the second embedded USB device controller (USBDC1).

This is the dev1 counterpart of `caliptra_ss_usb_dev_ram_rw`. The firmware
source is identical and device-neutral; the retarget to USBDC1 is done entirely
at build time by `BUILD_CFLAGS="-DUSB_DEV_SEL=1"` in the yml, which resolves
`USB_DEV_DMA_BASE_ADDR` to the dev1 DMA/SRAM base (0x2001_0100). No source
address change is required. See `claude_md/15_usb_dev1_replication.md` for the
`USB_DEV_SEL` mechanism.

## What it does

The MCU firmware (`caliptra_ss_usb_dev1_ram_rw.c`) exercises the device RAM
window directly over the MCU LSU AXI master:

- RAM base: `USB_DEV_DMA_BASE_ADDR` (0x2001_0100 for DEV1 under `-DUSB_DEV_SEL=1`)
- Window: from the DMA base to the end of the 4 KB s7 NIC aperture, addressed as
  32-bit words at a 4-byte stride (`USB_DEV_RAM_WORDS` = 960 words).

Two phases run back to back:

- **Phase 1 - deterministic sweep**: write a known per-word pattern
  (`(i * 0x9E3779B1) ^ 0xA5A5A5A5`) to every word, then read every word back and
  compare. This catches gross addressing / aliasing faults cleanly.
- **Phase 2 - random walk**: for `USB_DEV_RAM_ITERS` (256) iterations pick a
  random word and a random 32-bit value (both from `xorshift32()`), write it, and
  record the last value written to each touched word in a shadow array. After all
  writes complete, read every touched word back and compare against the shadow.
  Writing all values first and comparing afterward proves the words are
  independent storage (a write to word A must not disturb word B). This random
  walk is repeated `USB_DEV_RAM_LOOPS` (5) times.

## Why no bring-up is needed

The dev1 DMA/SRAM region is directly reachable from the MCU LSU AXI master (the
NIC400 maps 0x2001_0000-0x2001_FFFF to `cptra_ss_mcu_lsu_m0`). This is a
standalone RAM-access test: it drives no USB traffic, brings up no hub and no USB
core, and runs no DMA, so the whole RAM window is free scratch space and can be
randomized safely.

## SV side

`caliptra_ss_usb_dev1_ram_rw_test` extends `caliptra_ss_usb_base_test` and sets
`caliptra_ss_usb_dev1_ram_rw_sequence` as the `main_phase` default sequence on
the host virtual sequencer. The sequence does NOT bring up the USB link or drive
any USB traffic; it simply holds the run-phase objection open long enough for the
firmware to finish and halt. The verdict is produced by two judges:

- the firmware DEBUG_OUT byte (`TB_CMD_TEST_PASS` / `TB_CMD_TEST_FAIL`), and
- the UVM error count checked in `caliptra_ss_usb_base_test::final_phase`.

## Running

```
+UVM_TESTNAME=caliptra_ss_usb_dev1_ram_rw_test
```

See `caliptra_ss_usb_dev1_ram_rw.yml` for the build/plusarg wiring (note the
`BUILD_CFLAGS="-DUSB_DEV_SEL=1"` dev1 retarget).
