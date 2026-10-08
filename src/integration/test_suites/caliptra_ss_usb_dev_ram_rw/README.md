# caliptra_ss_usb_dev_ram_rw

Single UVM + firmware test that performs random read/write access checking on
the DMA/SRAM region (RAM) of an embedded USB device controller. By default it
targets USBDC0 (dev0); building the firmware with `-DUSB_DEV_SEL=1` re-targets
USBDC1 (dev1) with no source change.

## What it does

The MCU firmware (`caliptra_ss_usb_dev_ram_rw.c`) exercises the device RAM
window directly over the MCU LSU AXI master:

- RAM base: `USB_DEV_DMA_BASE_ADDR` (0x2000_1100 for DEV0, 0x2001_0100 for DEV1)
- Window: from the DMA base to the end of the 4 KB s5 NIC aperture, addressed as
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
  independent storage (a write to word A must not disturb word B).

## Why no bring-up is needed

The DMA/SRAM region is directly reachable from the MCU LSU AXI master. This is a
standalone RAM-access test: it drives no USB traffic, brings up no hub and no USB
core, and runs no DMA, so the whole RAM window is free scratch space and can be
randomized safely. The former `DataKnown_A` write-before-read hazard is not a
concern here because every read is preceded by a write to the same word.

## SV side

`caliptra_ss_usb_dev_ram_rw_test` extends `caliptra_ss_usb_base_test` and sets
`caliptra_ss_usb_mem_rw_sequence` as the `main_phase` default sequence on the
host virtual sequencer. The sequence does NOT bring up the USB link or drive any
USB traffic; it simply holds the run-phase objection open long enough for the
firmware to finish and halt. The verdict is produced by two judges:

- the firmware DEBUG_OUT byte (`TB_CMD_TEST_PASS` / `TB_CMD_TEST_FAIL`), and
- the UVM error count checked in `caliptra_ss_usb_base_test::final_phase`.

## Running

```
+UVM_TESTNAME=caliptra_ss_usb_dev_ram_rw_test
```

See `caliptra_ss_usb_dev_ram_rw.yml` for the build/plusarg wiring.
