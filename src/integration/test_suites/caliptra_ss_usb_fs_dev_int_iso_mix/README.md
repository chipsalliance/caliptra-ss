# caliptra_ss_usb_fs_dev_int_iso_mix

Mixed-endpoint USB 2.0 **Full Speed** device test: two INTERRUPT endpoints (EP1
and EP3) and one ISOCHRONOUS endpoint (EP2) are armed at the same time and
driven in the order EP1 -> EP2 -> EP3, so the device DMA and the shared EP
command/status list are exercised with two different transfer types live
simultaneously.

This is the Full Speed counterpart of `caliptra_ss_usb_hs_dev_int_iso_mix`.
Unlike the HS test, which repeats the group twice (`N_LOOPS = 2`), the FS
version runs a **single loop** (`N_LOOPS = 1`): at Full Speed every token costs
~16x more simulation time than at High Speed, so a second loop would not add
coverage proportional to its runtime.

The test is a merge of:

- the INTERRUPT loopback phases of `caliptra_ss_usb_hs_dev_int_iso_mix`
- `caliptra_ss_usb_fs_dev_iso_out` (Full Speed ISOCHRONOUS OUT/IN rules)

## Phase order

The host sequence (`caliptra_ss_usb_fs_dev_int_iso_mix_sequence`) runs three
traffic phases after hub + USBDC0 enumeration, once:

| Phase | Endpoint | Type | Traffic |
|---|---|---|---|
| 0 | EP1 | INTERRUPT | OUT 64 B (ramp `i % 256`), then IN 64 B loopback compare |
| 1 | EP2 | ISOCHRONOUS | OUT 2 x 512 B tokens, then IN buf0 512 B + IN buf1 512 B, expected `255 - (i % 256)` |
| 2 | EP3 | INTERRUPT | OUT 64 B (ramp `(i + 85) % 256`), then IN 64 B loopback compare |

All three OUT endpoints are armed once `DEVCMDSTAT.DEV_ADDR != 0`, so EP1 and
EP3 stay armed across the whole ISO phase and EP2 stays armed across both
INTERRUPT phases. The firmware is phase-agnostic and simply services whichever
endpoint the host drives next.

## Full Speed deltas versus the HS test

VIP / UVM test side (`caliptra_ss_usb_fs_dev_int_iso_mix_test`), the standard FS
conversion block also used by `caliptra_ss_usb_fs_dev_iso_out_test`:

- `high_speed_capable = 0` on the host, host and device speed forced to FS, and
  `connected_bus_speed` / `functionality_support` set to FS.
- EP0 is re-stamped as an FS endpoint with `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE`.
  Without this every SETUP trips the VIP `tend_to_end_delay_check`.
- `tddis` widened to 2 s (sim-scaled) so it exceeds the 1 ms FS SOF period while
  staying int32-safe; `tinactivity` widened as well or the link SUSPENDs in the
  middle of a control transfer.
- `drive_reset_time` is set explicitly, because an FS-only VIP host otherwise
  walks DISCONNECTED -> ENABLED without ever driving SE0.
- Both EP2 ISO slots must use `SVT_USB_FS_ISOC_MAX_PACKET_SIZE` (1023); larger
  values make the VIP `is_valid()` fail in `build_phase`.

Firmware side:

- Boots through `boot_usb_core_fs()` + `usb_hub_connect()` so the device
  suppresses the HS chirp.
- ISO OUT is re-armed **per 512 B token** (`USB_FS_ISO_OUT_BUF_BYTES = 512`,
  `USB_FS_ISO_OUT_TOKENS_PER_ROUND = 2`): at FS the 512 B payload is a short
  packet for the endpoint buffer, so hardware clears the Active bit after each
  token (UM11295 Table 843).
- ISO IN is armed `ACTIVE | TYPE_PERIODIC | RF_ISO` for both buf0 and buf1 and
  `USB_DEV_EPBUFCFG` bit 5 is set to enable EP2 IN ping-pong. RF must select ISO
  or the 64 B FS bulk maxpacket truncates the 512 B buffer.
- The event model is the same POLLED `INTSTAT` / entry-Active-bit model as the HS
  mix firmware (not the ISR mailbox model of `fs_dev_iso_out.c`).
- Budgets: `USB_POLL_TIMEOUT = 150000` spins, `ISO_IN_READ_WINDOW = 2000` spins,
  test `device_timeout = 35000 us`.

## Resource map

Identical to the HS test - no overlap between the endpoint families. EP0 keeps
data region `0x000-0x1FF`.

| Resource | EP1 (INTERRUPT) | EP2 (ISOCHRONOUS) | EP3 (INTERRUPT) |
|---|---|---|---|
| EP-list OUT word | `0x010` | `0x020` | `0x030` |
| EP-list IN buf0 | `0x018` | `0x028` | `0x038` |
| EP-list IN buf1 | - | `0x02C` | - |
| SRAM OUT buffer | `0x200` (64 B) | `0x600` (1024 B) | `0x240` (64 B) |
| SRAM IN buffer | `0x400` (64 B) | `0xA00` (1024 B) | `0x440` (64 B) |

The EP command/status list is a table of 16-byte blocks indexed by LOGICAL
endpoint (`0x10*n` OUT, `0x10*n + 8` IN buf0, `0x10*n + 0xC` IN buf1). The
highest slot used here (`0x038`) stays below the SETUP buffer at `0x100`; a
runtime boundary assert guards this.

## Completion-signal asymmetry

- INTERRUPT OUT and IN: the host ACKs, so hardware clears the entry Active bit.
  That bit (not the `INTSTAT` bit `2*n`, which is not reliable for an arbitrary
  endpoint) is the completion signal.
- ISO OUT: hardware reliably sets `INTSTAT EP2OUT` per token.
- ISO IN: no host ACK, so hardware neither clears the Active bit nor sets
  `INTSTAT EP2IN`. Firmware must not poll either; it only guarantees the SRAM
  payload is in place and then spins for a bounded read window.

Also note bit 26 is the Type (periodic) bit only on OUT entries; on IN entries
it is the data Toggle bit and must be left clear.

## Pass criteria

Firmware side (MCU log):

- `EP1 INTERRUPT OUT data check PASSED`
- `EP1 INTERRUPT loopback round 1/1 PASSED`
- `EP2 ISO OUT data check PASSED`
- `EP2 ISO IN read window elapsed - round 1/1 complete`
- `EP3 INTERRUPT OUT data check PASSED`
- `EP3 INTERRUPT loopback round 1/1 PASSED`
- `USB FS dev mixed INT EP1 + ISO EP2 + INT EP3 PASSED (1 loop of EP1 -> EP2 -> EP3)`

Host side (UVM log): no data mismatches in either INTERRUPT IN compare or in the
two ISO IN buffer compares, and the final sequence summary reports PASS. On a
timeout the firmware prints the per-endpoint `rounds=` and `iso_rounds=`
counters so the stalled phase is identifiable.

## Running

```
make -f tools/scripts/Makefile \
     TESTNAME=caliptra_ss_usb_fs_dev_int_iso_mix \
     CALIPTRA_TESTNAME=cptra_bringup \
     CALIPTRA_AUX=soc_ifc_ss \
     CALIPTRA_SS_CLK_FREQ=400 \
     mcu_program.hex cptra_program.hex
```

UVM test name: `caliptra_ss_usb_fs_dev_int_iso_mix_test`.
