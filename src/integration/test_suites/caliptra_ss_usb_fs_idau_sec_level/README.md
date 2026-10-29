# Full-Speed IDAU Security Level Test

**Testcase:** `caliptra_ss_usb_fs_idau_sec_level`

## Overview

Verifies USB FS link attachment and that MCU firmware can access USB registers
through the IDAU security region.

## Operation

VIP host brings up the FS link. MCU firmware reads the DEVCMDSTAT SPEED field after
DCON is asserted and checks that speed==1 (FS mode).

## What Is Verified

- USB link attaches at FS speed (DEVCMDSTAT.SPEED == 1)
- IDAU security region allows MCU firmware to access USB registers without fault
- DEVCMDSTAT register readable after FS link up

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_idau_sec_level_sequence.svh` | SVT VIP FS link sequence |
| `caliptra_ss_usb_fs_idau_sec_level_test.svh` | UVM test class |
| `caliptra_ss_usb_fs_idau_sec_level.c` | MCU firmware reading DEVCMDSTAT.SPEED |
| `caliptra_ss_usb_fs_idau_sec_level.yml` | Simulation run config |
