# USB HS Device NBytes Residual Test

**Testcase:** `caliptra_ss_usb_hs_dev_nbyte`

## Overview

Verifies that the DMA NBytes residual field is correctly decremented by the USB
device controller after receiving short bulk OUT packets on EP1 in the
Caliptra SS RISC-V MCU environment.

## Operation

The VIP host enumerates the HS device (SET_ADDRESS, SET_CONFIGURATION) and then
sends 5 successive bulk OUT short packets to EP1.  The packet lengths are
1, 2, 3, 4, and 5 bytes respectively.

For each iteration `i` (1..5):

1. EP1 OUT is armed with NBytes budget = 32 (0x20).
2. The VIP host sends `i` bytes.
3. After the transfer completes (Active bit clears / EP1OUT interrupt fires)
   the MCU firmware checks:
   - NBytes residual == 32 - i  (hardware decremented by actual bytes received)
   - Buffer address offset advanced by exactly one 64-byte chunk
   - Received byte pattern: buf[j] == j+1 for j = 0..i-1
   - FRAME_INT is also asserted in INTSTAT when EP1OUT fires
4. EP1 OUT is re-armed with toggle-reset (TR=1, TV=0) ready for the next
   iteration.

## What Is Verified

- Correct NBytes residual after short-packet bulk OUT transfers (non-zero
  residual = partial fill)
- Buffer address pointer advances by one 64-byte aligned slot per short packet
- Received data byte pattern matches expected sequence
- FRAME_INT co-assertion with EP1OUT interrupt
- Data toggle reset between successive transfers

## SRAM Layout

| Offset   | Contents                         |
|----------|----------------------------------|
| 0x000    | EP command/status list (EP0 OUT, EP0 IN, EP1 OUT at word 4) |
| 0x100    | EP0 SETUP buffer                 |
| 0x140    | EP0 OUT buffer                   |
| 0x180    | EP0 IN buffer                    |
| 0x200    | EP1 OUT receive buffer (32 bytes)|

## Test Components

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hs_dev_nbyte_sequence.svh` | SVT VIP HS short-packet bulk OUT sequence (5 transfers: 1-5 bytes each) |
| `caliptra_ss_usb_hs_dev_nbyte_test.svh` | UVM test class |
| `caliptra_ss_usb_hs_dev_nbyte.c` | MCU firmware: 5-iteration NBytes residual and byte-pattern verification |
| `caliptra_ss_usb_hs_dev_nbyte.yml` | Simulation run config |
