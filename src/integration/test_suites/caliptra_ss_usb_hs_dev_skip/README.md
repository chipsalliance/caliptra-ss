# caliptra_ss_usb_hs_dev_skip

USB 2.0 High-Speed **device mode** test for the `EPSKIP` (endpoint skip)
mechanism of the NXP USB device controller (`third_party/usb2`).

## What EPSKIP does

`EPSKIP` (`SOC_USBHSD_EPSKIP`, device register offset `0x14`) has one bit per
*physical* endpoint (EP0 OUT = 0, EP0 IN = 1, EP1 OUT = 2, EP1 IN = 3, ...).

Once firmware sets the `Active` bit of an endpoint command/status list entry the
entry belongs to hardware and firmware must not touch it. `EPSKIP` is the only
legal way to take ownership back before the transfer completes naturally.

When firmware writes a skip bit, the DMA engine (which round-robin scans all skip
bits from its IDLE state, with no dependency on USB bus traffic):

1. fetches the endpoint entry from USB SRAM,
2. clears its `Active` bit and writes the word back,
3. self-clears the `EPSKIP` bit,
4. sets `INTSTAT[phys_ep]` **only** if `Active` was really `1`,
5. leaves `EPINUSE` untouched (double buffering is not advanced by a skip).

See USB Integration Guide sections 4.2.2.6, 4.2.3 (`A` bit) and 4.2.4.2.1, and
`third_party/usb2/src/ip_xxx_3511/RTL/usb_dma.m.vhdl` (`READ_EPINFO_SKIP` /
`WAIT_ON_GNT_FOR_SKIP_UPDATE`) plus `usb_reg_if.m.vhdl` (`dma_clear_skip`).

## Test phases

| Phase | Scenario | Checks |
|-------|----------|--------|
| E | skip EP1 IN while `Active = 0` | skip bit self-clears, **no** EP1 IN interrupt |
| A | skip an idle armed EP1 OUT (2048 B, no traffic) | `Active` cleared, residual and address untouched, EP1 OUT interrupt set, `EPINUSE` unchanged |
| D | skip an armed EP1 IN the host never polls (64 B) | `Active` cleared, residual untouched, EP1 IN interrupt set |
| B | skip EP1 OUT mid transfer: 2048 B armed, host sends 512 B | `Active` cleared, residual `== 1536`, EP1 OUT interrupt set, received data pattern `0xB0000000 + i` intact |
| C | re-arm EP1 OUT (512 B) and complete normally | `Active` cleared by completion, residual `== 0`, data pattern `0xC0000000 + i` |

Firmware self-checks every item and prints `PASS`/`FAIL` lines, ending with
`USB HS dev SKIP test - PASSED` or `... FAILED (n errors)`.

## Run

```bash
cd $CALIPTRA_SS
pb fe build --tb caliptra_ss_lib::caliptra_ss_top_tb
bash ~/scripts/pb_run_ss_test_script.sh caliptra_ss_usb_hs_dev_skip
```

UVM side: `caliptra_ss_usb_hs_dev_skip_test` /
`caliptra_ss_usb_hs_dev_skip_sequence` in
`src/integration/testbench/uvm/usb/`.
