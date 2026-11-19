# caliptra_ss_usb_hs_dev_epinfo_rate_feedback

Suffix / message id: `USB_DMA_EPINFO_RATE_FEEDBACK`. Directed, High Speed,
hub + USBDC0. Code-coverage test for the `READ_EPINFO` decode of
`third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_dma.m.vhdl` (the
copy the regression compiles, merged-coverage page `mod9.html`).

## Field encoding (resolved from the RTL)

`usb_dma` is built with `RAM_DATAWIDTH = 64`, so each EP-list read returns
two descriptor words. `epinfo_addr(2)` selects the word that is decoded. It is
`'1'` on a SETUP or when the endpoint's EPINUSE bit is set (lines 1167-1169).

| Bit, buffer 0 / buffer 1 | Field | Effect in READ_EPINFO |
|---|---|---|
| 28 / 60 | TR | toggle reset: load TV |
| 27 / 59 | TV / RF | TV when TR = 1; RF when TR = 0 |
| 26 / 58 | T | periodic |

When TR = 0, T = 0, RF = 1 and the endpoint is not EP0, the decode enters
rate-feedback mode. It clears the toggle and sets `epinfo_ratefeedbackmode`
(lines 350-353 / 384-387). In this integration that signal is left `open` at
`ip_xxx_3511_hs_mem_compound_structure.a.vhdl:1356`, so the only visible effect
is the toggle clear.

## Legs

Endpoint: EP5 OUT (physical index 10). EPBUFCFG stays single-buffered, so
EPINUSE is controlled only by firmware.

| Leg | Buffer | Descriptor | Lines | Host PID |
|---|---|---|---|---|
| 0 | 0 | TR=0 T=0 RF=1 | 386, 387 | DATA0 |
| 1 | 0 | TR=1 TV=1 | 376 | DATA1 |
| 2 | 1 | TR=0 T=0 RF=1 | 352, 353 | DATA0 |
| 3 | 1 | TR=1 TV=1 | 341, 342, 346 | DATA1 |
| 4 | 1 | TR=1 TV=0 | 341, 344, 346 | DATA0 |

The VIP carries a running bulk OUT toggle that flips on every ACK, because
nothing calls `reconfigure()` after enumeration. The legs are ordered so that
the toggle each descriptor fetch sets equals the PID the host sends. Every
packet is therefore consumed, and each leg must complete on both sides.

If a set/clear path did not act, the device would ACK the packet and silently
discard it (`usb_pie.m.vhdl:2746-2760`). Active would then never clear, and
the firmware leg counter would stall. That shows up as a firmware FAIL plus a
missing completion on the next leg, not as a silent pass.

## Not stimulated: lines 334, 356, 357

These lines need buffer 1 **and** endpoint 0, which is structurally impossible:

* For EP0, buffer 1 is only selected by a SETUP, and a SETUP takes the earlier
  branch at line 278.
* `usb_reg_if.m.vhdl:234` ties `reg_ep_bufinuse(1 downto 0)` to `'0'`.

They need a designer waiver. See `claude_md/40_usb_dma_epinfo_rate_feedback.md`,
which also raises the question of whether rate feedback is used in data-centre
parts at all.

## Files

| File | Note |
|---|---|
| `caliptra_ss_usb_hs_dev_epinfo_rate_feedback.c` | Arms each leg (descriptor plus EPINUSE), checks Active, payload and EPTOGGLE. Verdict is FAIL-only. |
| `caliptra_ss_usb_hs_dev_epinfo_rate_feedback.yml` | `+UVM_TESTNAME=caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test` |
| `cptra_bringup.c` | Symlink to `../libs/usb/bringup/cptra_bringup.c` |
| `.../uvm/usb/caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence.svh` | Five BULK OUTs; each must complete |
| `.../uvm/usb/caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test.svh` | `endpoint_cfg[1]` re-stamped to EP5 BULK OUT |

## Status

**Code and docs only: not compiled or simulated.** First-run checks:

```
grep 'RF leg' mcu_console.log        # 5 x "armed" + 5 x "done", no FAIL
grep '^UVM_ERROR' vcs_sim.log        # must be EMPTY (no report catcher)
grep 'USB_DMA_EPINFO_RATE_FEEDBACK' svt_debug.transcript
```

The per-leg `EPTOGGLE[10]` values are derived from reading the RTL and are only
reported, not asserted. Confirm them on the first run, then decide whether to
turn them into checks.

<!-- File contains AI-generated response based on internal company sources -->
