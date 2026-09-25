# USB HS Device DMA Skip-State Test

**Testcase:** `caliptra_ss_usb_hs_dev_skip`

## Overview

Verifies the nominal USB DMA endpoint-skip flow for an active EP1 OUT
command/status entry in the Caliptra SS RISC-V MCU environment. The skip
operation exercises the DMA FSM path:

`IDLE -> READ_EPINFO_SKIP -> WAIT_ON_GNT_FOR_SKIP_UPDATE -> IDLE`

The MCU firmware performs all DUT-side programming and checking. The UVM
testbench acts only as a USB host and supplies protocol traffic.

## Operation

1. The VIP establishes the HS link and enumerates the device.
2. After the SET_CONFIGURATION status phase, firmware programs an active EP1
   OUT entry at USB SRAM offset `0x10` and sets `EPSKIP[2]`.
3. Firmware waits for the skip operation to complete and checks:
   - `EPSKIP[2]` is cleared by hardware.
   - The EP1 OUT entry's Active bit is cleared.
   - All other EP1 OUT command/status fields remain unchanged.
   - The EP1 OUT interrupt is asserted.
4. Firmware re-arms EP1 OUT.
5. The VIP sends a 16-byte bulk OUT payload containing bytes `0xA0` through
   `0xAF`.
6. Firmware checks that the residual count is zero and the received payload
   matches the transmitted bytes.

Physical endpoint index 2 is EP1 OUT because the hardware index is formed from
the endpoint number and direction.

## What Is Verified

- Nominal traversal of the `READ_EPINFO_SKIP` and
  `WAIT_ON_GNT_FOR_SKIP_UPDATE` DMA states
- Hardware clearing of the requested `EPSKIP[2]` bit
- Active-bit clearing in the skipped EP1 OUT command/status entry
- Preservation of all non-Active fields in the skipped entry
- EP1 OUT interrupt generation when an active entry is skipped
- Successful EP1 OUT re-arm and bulk OUT transfer after skip completion
- Zero NBytes residual and correct received data for the recovery transfer
- Firmware ownership of all device-side programming and checking, with the
  testbench limited to USB protocol traffic

## SRAM Layout

| Offset | Contents |
|--------|----------|
| `0x010` | EP1 OUT command/status entry |
| `0x200` | EP1 OUT receive buffer (16 bytes) |

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_skip_sequence.svh` | HS enumeration and protocol-only recovery traffic |
| `caliptra_ss_usb_hs_dev_skip_test.svh` | UVM test and EP1 configuration |
| `caliptra_ss_usb_hs_dev_skip.c` | Firmware skip programming and verification |
| `cptra_bringup.c` | Caliptra core mailbox bring-up firmware |
| `caliptra_isr.h` | Caliptra core interrupt-service definitions |
| `caliptra_ss_usb_hs_dev_skip.yml` | Simulation run configuration |
