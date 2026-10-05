# caliptra_ss_usb_hub_ram_rw

Single UVM + firmware test that verifies the read/write behavior and the
write-lock protection of the USB hub descriptor array (`ep0_mem`) of the
compound USB IP. It drives no USB link bring-up and no USB traffic - the MCU
firmware does all of the checking directly over the LSU AXI master.

## Hub descriptor array background

The embedded USB hub keeps its descriptors (device, configuration, hub class,
device qualifier, other-speed configuration) and its SETUP-match table in an
internal 172-word (`C_NWORDS` = 172) 32-bit flip-flop array named `ep0_mem`
inside the compound IP (`usb_ep0_hub_descr.m.vhdl`). The array self-initializes
from a ROM constant at reset, so firmware has nothing to program. The whole
array is reachable from the MCU LSU AXI master over the `hub_axi` aperture at
`USB_HUB_DESC_DEVICE_BASE` (= `SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR`,
0x2000_1000); word `i` lives at `base + i*4`. The aperture spans
0x2000_1000 .. 0x2000_12AF (exactly 172 words), and word 15 is
`SOC_USB_COMBO_HUB_CONTROL` (0x2000_103C) = `C_HUB_CS`, which confirms the base.

## Write-lock rule (from the RTL)

```
hub_write_lock <= ep0_mem(C_HUB_CS)(0) and ep0_mem(C_HUB_CS)(16)
write allowed only if (hub_write_lock='0' OR waddr=C_HUB_CS) and waddr < 172
```

`C_HUB_CS` is word 15 (byte offset 0x3C), the Hub Control/Status register:

- bit 0  = HUB_EN
- bit 16 = HUB_CONNECT (DCON)

So the array is writable while at most one of HUB_EN / HUB_CONNECT is set, and
freezes (every word except word 15) once BOTH are set. Word 15 is ALWAYS
writable - it is explicitly exempted from the lock - so firmware can clear
HUB_CONNECT afterwards to release the lock again. HUB_EN alone does not lock the
array.

## What it does

The MCU firmware (`caliptra_ss_usb_hub_ram_rw.c`) runs
`USB_HUB_RAM_LOOPS` (3) iterations of a two-phase check (Option B):

- **Phase A - UNLOCKED** (HUB_EN=1, HUB_CONNECT=0): the lock is deasserted. For
  every word except word 15, read the current value, write a random value
  forced to differ from it, read it back, and require the readback to equal the
  written value. This proves each word is writable when unlocked and that
  neighboring words decode independently.
- **Phase B - LOCKED** (HUB_EN=1, HUB_CONNECT=1): the lock is asserted. First
  capture the current value of every word except word 15 into a shadow array
  (the post-lock baseline). Then attempt a random write to every word except
  word 15, and after all writes complete read every word back and require it to
  still equal the captured baseline. Writing all attempts first and comparing
  afterward proves the whole array is frozen (a dropped write must not disturb
  any word).

Between loops word 15 is cleared (HUB_EN=0, HUB_CONNECT=0), which is always
allowed, so the next loop starts from a clean, unlocked state.

Word 15 (`C_HUB_CS`) is never given a random value: it holds the enable/connect
controls and is always writable, so a random write there would change the lock
state or disconnect the hub mid-test. It is driven only by the explicit
phase-control writes.

## Why no bring-up is needed

The descriptor array is directly reachable from the MCU LSU AXI master. This is
a standalone memory-access test: it brings up no hub and no USB core and drives
no USB traffic, so the array is free scratch space that can be perturbed
safely.

## SV side

`caliptra_ss_usb_hub_ram_rw_test` extends `caliptra_ss_usb_base_test` and sets
`caliptra_ss_usb_hub_ram_rw_sequence` as the `main_phase` default sequence on
the host virtual sequencer. The sequence does NOT bring up the USB link or drive
any USB traffic; it simply holds the run-phase objection open long enough for
the firmware to finish and halt. The verdict is produced by two judges:

- the firmware DEBUG_OUT byte (`TB_CMD_TEST_PASS` / `TB_CMD_TEST_FAIL`), and
- the UVM error count checked in `caliptra_ss_usb_base_test::final_phase`.

## Running

```
+UVM_TESTNAME=caliptra_ss_usb_hub_ram_rw_test
```

See `caliptra_ss_usb_hub_ram_rw.yml` for the build/plusarg wiring.
