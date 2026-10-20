# caliptra_ss_usb_hs_dev_int_iso_mix

Mixed-endpoint USB 2.0 High Speed device test: one INTERRUPT endpoint (EP1) and
one ISOCHRONOUS endpoint (EP2) are armed at the same time and driven in an
interleaved order, so the device DMA and the shared EP command/status list are
exercised with two different transfer types live simultaneously.

The test is a merge of:

- `caliptra_ss_usb_hs_dev_int_loopback` (INTERRUPT OUT + IN loopback)
- `caliptra_ss_usb_hs_dev_iso_out` (ISOCHRONOUS OUT 1024 B + 2x IN 512 B)

## Phase order

The host sequence (`caliptra_ss_usb_hs_dev_int_iso_mix_sequence`) runs three
traffic phases after hub + USBDC0 enumeration:

| Phase | Endpoint | Type | Traffic |
|---|---|---|---|
| 0 | EP1 | INTERRUPT | OUT 64 B (ramp `i`), then IN 64 B loopback compare |
| 1 | EP2 | ISOCHRONOUS | OUT 1024 B (ramp `i % 256`), then IN buf0 512 B + IN buf1 512 B |
| 2 | EP1 | INTERRUPT | OUT 64 B (ramp `(i + 85) % 256`), then IN 64 B loopback compare |

Both OUT endpoints are armed once `DEVCMDSTAT.DEV_ADDR != 0`, so EP1 stays
armed across the whole ISO phase and EP2 stays armed across the whole second
INTERRUPT phase. The firmware is phase-agnostic and simply services whichever
endpoint the host drives next.

## Resource map

No overlap between the two endpoint families. EP0 keeps data region
`0x000-0x1FF`; the ISO side keeps the offsets proven by the standalone
`iso_out` test and only the INTERRUPT side was relocated.

| Resource | EP1 (INTERRUPT) | EP2 (ISOCHRONOUS) |
|---|---|---|
| EP-list OUT word | `0x010` | `0x020` |
| EP-list IN buf0 | `0x018` | `0x028` |
| EP-list IN buf1 | - | `0x02C` |
| SRAM OUT buffer | `0x200` (64 B) | `0x600` (1024 B) |
| SRAM IN buffer | `0x400` (64 B) | `0xA00` (1024 B) |

The EP command/status list is a table of 16-byte blocks indexed by LOGICAL
endpoint (`0x10*n` OUT, `0x10*n + 8` IN buf0, `0x10*n + 0xC` IN buf1). The
highest slot used here (`0x02C`) stays well below the SETUP buffer at `0x100`;
a runtime boundary assert guards this.

## Completion-signal asymmetry

- INTERRUPT OUT and IN: the host ACKs, so hardware clears the entry Active bit.
  That bit (not the `INTSTAT` bit `2*n`, which is not reliable for an arbitrary
  endpoint) is the completion signal.
- ISO OUT: hardware reliably sets `INTSTAT EP2OUT`.
- ISO IN: no host ACK, so hardware neither clears the Active bit nor sets
  `INTSTAT EP2IN`. Firmware must not poll either; it only guarantees the SRAM
  payload is in place and then spins for a bounded read window.

Also note bit 26 is the Type (periodic) bit only on OUT entries; on IN entries
it is the data Toggle bit and must be left clear.

## Pass criteria

Firmware side (MCU log):

- `[int round 0] EP1 INTERRUPT OUT data check PASSED`
- `EP1 INTERRUPT loopback round 0 PASSED`
- `EP2 ISO OUT data check PASSED`
- `[int round 1] EP1 INTERRUPT OUT data check PASSED`
- `EP1 INTERRUPT loopback round 1 PASSED`
- `USB HS dev mixed INT EP1 (2 rounds) + ISO EP2 PASSED`

Host side (UVM log): no data mismatches in either INTERRUPT IN compare or in
the two ISO IN buffer compares, and the final sequence summary reports PASS.

## Running

```
make -f tools/scripts/Makefile \
     TESTNAME=caliptra_ss_usb_hs_dev_int_iso_mix \
     CALIPTRA_TESTNAME=cptra_bringup \
     CALIPTRA_AUX=soc_ifc_ss \
     CALIPTRA_SS_CLK_FREQ=400 \
     mcu_program.hex cptra_program.hex
```

UVM test name: `caliptra_ss_usb_hs_dev_int_iso_mix_test`.

# File contains AI-generated response based on internal company sources
