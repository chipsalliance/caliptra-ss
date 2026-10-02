# caliptra_ss_usb_hs_dev_int_loopback

USB High-Speed device test for an **INTERRUPT** endpoint exercised in both
directions (host -> device OUT, then device -> host IN loopback).

Full design rationale, with RTL citations, is in
`docs/usb_int_ep_randomized_test_spec.md`.

## What is being tested

This is the first test in the suite that arms an endpoint as *interrupt*.
The EP command/status entry is built as `T=1, RF=1`:

```
OUT entry: ACTIVE | TYPE_PERIODIC | RF_INT | NBYTES(64) | ABS_ADDR(buf)
IN  entry: ACTIVE |                          NBYTES(64) | ABS_ADDR(buf)
```

`USB_EP_ENTRY_RF_INT` existed in `libs/usb/usb.h` but was unused until now.

### Why the IN entry looks different

Bit 26 is the endpoint Type bit only on OUT entries. On IN entries the same
bit is the data Toggle bit (0 = DATA0). Setting `USB_EP_ENTRY_TYPE_PERIODIC`
on an IN entry therefore corrupts the toggle instead of selecting periodic
mode. This asymmetry is a property of the NXP IP_3511HS (Integration Guide
4.2.3) and must not be "cleaned up".

## Packet size

64 bytes. Per `usb_dma.m.vhdl` the maxpacket encoding `"00"` covers FS
control/bulk/interrupt and HS control, so a 64-byte body is valid at both FS
and HS with no re-encoding. HS interrupt endpoints may use 512 or 1024 bytes;
that is left to a future high-bandwidth variant.

## Endpoint number: currently fixed, to be randomized

The IP supports EP0..EP15 (`MAX_ENDPOINT_ADDRESS := 16` in
`usb_subcmp_pkg.p.vhdl`), so a data endpoint may legally be EP1..EP15.

This revision of the test forces `USB_INT_EP_FIXED = 2` and reuses the
known-good EP2 SRAM map, but every offset is computed from the endpoint
number, so enabling randomization later is a one-line change plus the SRAM
relocation described below.

### The EP >= 8 SRAM collision (why randomization is not enabled yet)

The EP list entry for EP(n) lives at `0x10 * (2*n)`, which overlaps the
current data-buffer map:

| EP | OUT entry | collides with          |
| -- | --------- | ---------------------- |
| 8  | 0x100     | SETUP buffer  (0x100)  |
| 10 | 0x140     | EP0 OUT buffer (0x140) |
| 12 | 0x180     | EP0 IN buffer  (0x180) |
| 15 | 0x1E0     | needs list room to 0x1F0 |

Randomizing over the full EP1..EP15 range requires relocating the SETUP and
EP0 buffers above 0x1F0 first. This is why every pre-existing periodic
endpoint test only ever used EP2.

## Pass criteria

- Firmware: the received OUT payload matches `byte[i] = i`, and the hardware
  clears the Active bit of the IN entry (the host ACKed the interrupt IN,
  which - unlike isochronous IN - it does).
- UVM sequence: the 64 bytes read back on interrupt IN match the bytes sent
  on interrupt OUT.

## Run

```
+UVM_TESTNAME=caliptra_ss_usb_hs_dev_int_loopback_test
```
