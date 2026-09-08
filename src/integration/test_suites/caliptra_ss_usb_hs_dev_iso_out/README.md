# High-Speed Device Isochronous OUT + IN Test

**Testcase:** `caliptra_ss_usb_hs_dev_iso_out`

## Overview

Verifies HS isochronous OUT and IN transfers on EP2 across 3 rounds, with a
rotating data pattern each round, and a separate FRAME_INT (SOF) interrupt
test phase. Runs on the hub-composite IP.

## Topology (hub-composite IP)

USBDC0 sits behind the on-chip 2-port USB hub. `boot_usb_core()` programs
USBDC0 and brings the hub up in phase 1 (`usb_hub_init_and_connect()`: HUB
RAM + `HUB_EN`); the test's `main()` calls `usb_hub_connect()` (phase 2,
`HUB_CONNECT`). Registers use the `USB_DEV0_*` bank; EP2 OUT/IN buffer
addresses use `USB_EP_ENTRY_ABS_ADDR()`. EP2 OUT is armed as isochronous
(`USB_EP_ENTRY_TYPE_PERIODIC` with the RF bit clear); EP2 IN entries must
NOT set `USB_EP_ENTRY_TYPE_PERIODIC` (bit 26 on IN entries is the data
Toggle bit, not the Type bit).

## Operation

After enumeration, MCU firmware arms EP2 OUT (ISO, 1024 bytes) for round 0.
For each of `N_ISO_ROUNDS = 3` rounds:

1. Firmware waits for the EP2 OUT INTSTAT completion bit (this is the only
   reliable completion signal - ISO IN has no host ACK, so the hardware
   never clears the IN entry's Active bit or sets an IN completion
   interrupt).
2. On EP2 OUT completion, firmware verifies the received bytes against the
   expected ramp pattern `byte[i] = (i + round * ISO_ROUND_OFFSET) % 256`,
   then fills the EP2 IN SRAM with the inverse pattern
   `byte[i] = 255 - ((i + round * ISO_ROUND_OFFSET) % 256)` and arms both
   EP2 IN buffer entries (two 512-byte halves of the 1024-byte transfer).
3. Firmware immediately arms EP2 OUT for the next round (rounds 1, 2) so the
   state machine advances as soon as the corresponding OUT token arrives.

After all 3 rounds complete, firmware runs a separate FRAME_INT test phase:
enables `INTEN.FRAME_INT_EN`, counts SOF (FRAME_INT) events over a fixed
poll window (expects >= `FRAME_INT_MIN_COUNT`), then disables
`FRAME_INT_EN` and verifies the disable took effect by reading back `INTEN`
(not `INTSTAT`, since hardware continues to assert the INTSTAT bit at every
SOF boundary regardless of the enable).

## What Is Verified

- Hub-composite bring-up (`usb_hub_init_and_connect()` + `usb_hub_connect()`)
- EP2 isochronous OUT reception across 3 rounds, each with a distinct
  rotating byte pattern
- EP2 isochronous IN data served correctly for each round (VIP host performs
  the data-integrity check on the IN side)
- Correct double-buffered IN arming (two 512-byte buffer entries per
  1024-byte IN transfer)
- FRAME_INT (SOF) interrupt generation, counting, and enable/disable via
  `INTEN.FRAME_INT_EN`

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_iso_out_sequence.svh` | SVT VIP: hub-aware enumeration, 3-round ISO OUT + IN sequence |
| `caliptra_ss_usb_hs_dev_iso_out_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_iso_out.c` | MCU firmware: 3-round ISO OUT/IN state machine + FRAME_INT test phase |
| `caliptra_isr.h` | Boilerplate ISR declarations (shared across USB tests) |
| `cptra_bringup.c` | Shared Caliptra bring-up preamble |
| `caliptra_ss_usb_hs_dev_iso_out.yml` | Simulation run config |

