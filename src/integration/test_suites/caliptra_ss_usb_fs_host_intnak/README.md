# Full-Speed Interrupt-on-NAK Test

**Testcase:** `caliptra_ss_usb_fs_host_intnak`

## Overview

Verifies that the device correctly NAKs bulk OUT tokens on an un-armed endpoint
and that the INTONNAK interrupt fires as expected.

## Operation

VIP host enumerates the FS device. MCU firmware enables the INTONNAK_AO bit but
deliberately does NOT arm EP1 OUT. VIP host sends a BULK OUT token to EP1.
The device returns NAK.

## What Is Verified

- Device returns NAK on un-armed EP1 OUT endpoint
- INTONNAK_AO bit enables interrupt-on-NAK behavior
- INTONNAK interrupt fires when NAK is returned

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_host_intnak_sequence.svh` | SVT VIP sequence sending bulk OUT token |
| `caliptra_ss_usb_fs_host_intnak_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_host_intnak.c` | MCU firmware enabling INTONNAK_AO |
| `caliptra_ss_usb_fs_host_intnak.yml` | Simulation run config |
