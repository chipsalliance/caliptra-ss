# caliptra_ss_usb_hs_dev_disabled_ep

USB High-Speed directed test: a BULK OUT token addressed to a **disabled**
endpoint of USBDC0 must get no response at all - no ACK, no NAK, no STALL.

Topology: hub enabled, USBDC0 behind hub downstream port 1, device address 2.
Probe endpoint: **EP4 OUT**.

## What "disabled" means on this controller

Enabling or disabling an endpoint is **not** a control-register operation. The
three endpoint CSRs are buffer controls, not enables:

| Offset | Register | Function |
|---|---|---|
| 0x14 | EPSKIP | One-shot, self-clearing abort of the endpoint's current buffer. Firmware writes a 1; hardware clears it again once the DMA has deactivated the buffer (`usb_reg_if.m.vhdl:689` firmware write, `usb_reg_if.m.vhdl:782` hardware clear). Not a persistent enable. |
| 0x18 | EPINUSE | Double buffering: which of buffer 0/1 the hardware is using. |
| 0x1C | EPBUFCFG | Single versus double buffering per endpoint. |

The only enable in the register interface is the whole-device DEV_EN
(`usb_reg_if.m.vhdl:187`, `usbreg_deviceenabled <= reg_dev_enable`).

The per-endpoint enable is the **D (Disabled) field, bit 30, of the endpoint
command/status list word in system memory**. From the register documentation
(`docs/usb/usb_register_structure.md` section 1.17, accessories repo):

> D (Disabled) RW - 0: EP enabled, 1: EP disabled. On bus reset, FW should
> disable all EPs. FW can modify only when Active is 0.

RTL path:

```
usb_dma.m.vhdl:300    epinfo_disabled <= dma_rdata(30);
                      -- forced to '0' when the endpoint number is 0, so the
                      -- D field has no effect on EP0
usb_pie.m.vhdl:2482   OUT path
usb_pie.m.vhdl:2366   IN / PING path
                      if epinfo_disabled = '1' then
                        -- ep is disabled. no data nor handshake must be returned
```

The packet handler returns to idle and ends the transfer without driving
anything onto the bus.

## Why EP4

`USB_C_DEV0_NBPHYSEP` is 28 (`src/integration/rtl/caliptra_ss_top.sv`), i.e.
14 OUT/IN physical endpoint pairs, so endpoint numbers 0..14 are all backed by
real hardware. EP4 is therefore a genuine endpoint whose silence can only be
caused by the D bit. It is also used by no other test in the tree - only EP0,
EP1 and EP2 appear anywhere else - so nothing else can perturb it.

Descriptor offset. The endpoint command/status list layout is fixed: EP0 OUT
(0x000), EP0 SETUP (0x004), EP0 IN (0x008), reserved (0x00C), then four words
(16 bytes) per endpoint number, being OUT buffer 0 / OUT buffer 1 / IN buffer 0
/ IN buffer 1. Endpoint N OUT buffer 0 is therefore at
`0x010 + (N - 1) * 0x10`, which reproduces the 0x010 used by
`caliptra_ss_usb_hs_dev_bulk_out` for EP1 and the 0x020 used by the iso tests
for EP2, and gives **0x040 for EP4 OUT**.

## Relationship to caliptra_ss_usb_hs_dev_unsupported_ep

Three distinct causes of device silence exist in this IP and must not be
confused:

| Cause | Observable | Covered by |
|---|---|---|
| No hardware behind the endpoint number (EP15) | silence | `caliptra_ss_usb_hs_dev_unsupported_ep` |
| D = 1, endpoint disabled (EP4) | silence | this test |
| D = 0 and Active = 0 | NAK, i.e. a handshake | incidental in other tests |

The third row is why ordering matters: if the probe arrived before the D bit was
written, EP4 would NAK instead of staying silent, and the host-side verdict
would fail loudly rather than pass by accident.

The `USB_EP_ENTRY_DISABLED` macro in
`src/integration/test_suites/libs/usb/usb.h` had **no users anywhere in the
firmware tree** before this test, so the D-bit RTL path was entirely
unverified.

## Firmware behaviour

1. Boot the MCU and the USB core in HS device mode behind the on-chip hub.
2. Service enumeration (bus reset and EP0 SETUP packets).
3. Once the device has been assigned a non-zero address, write the EP4 OUT
   descriptor at `USB_DMA_BASE_ADDR + 0x040` with `USB_EP_ENTRY_DISABLED` set
   and ACTIVE deliberately clear (the documentation allows D to be modified only
   while Active is 0, and an armed-and-disabled endpoint is not a legal
   combination). Read the word back and log it - that console line is the
   device-side proof the endpoint was disabled before the probe arrived.
4. Re-apply the D bit after any bus reset, since a reset re-initializes the
   endpoint list.
5. Fail if the EP4 OUT interrupt ever fires (a disabled endpoint never has its
   ACTIVE cleared by hardware, so it cannot raise an endpoint interrupt), or if
   the descriptor stops reading back as disabled / becomes ACTIVE.

Verdict is FAIL-only: a never-reset `total_errors` drives a single
`SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL)` at the end. `TB_CMD_TEST_PASS` is never
sent, because it finishes the simulation before the UVM `final_phase` and would
mask the host-side verdict.

## Host-side verdict

`caliptra_ss_usb_hs_dev_disabled_ep_sequence.svh` sends one 8-byte BULK OUT to
device address 2 / EP4 and requires total bus silence afterwards. The verdict
is the shared `caliptra_ss_usb_handshake_counter_callback`, which counts
device-sourced ACK / NAK / STALL packets on the host link monitor. The window
self-arms when the OUT token is really seen on the wire, the silence interval is
measured from the observed DATA end time, and a separate missing-stimulus
timeout fails the test rather than letting it report silence that was never
provoked.

The VIP legitimately complains twice while the bus is silent (a transfer-level
`Unexpected Device Timeout <Dev:2 EP:4 BULK_OUT_TRANSFER>` and the link-level
`tend_to_end_delay_check`). Both are demoted to UVM_INFO under the report id
`USB_HS_DISABLED_EP_EXPECTED_SILENCE` by a scoped report catcher that is armed
only after enumeration and deleted after the probe drains.

First-run check:

```
grep '^UVM_ERROR' vcs_sim.log | grep -v USB_HS_DISABLED_EP_EXPECTED_SILENCE
```

must come back empty.

## Note on the documented reset convention

The documentation says firmware should disable all endpoints after a bus reset.
`usb_boot()` in `libs/usb/usb.c` instead zeroes the endpoint list
(`0x010..0x0FF`), which leaves every unused endpoint at D = 0, ACTIVE = 0 - a
state that NAKs rather than staying silent. That deviation is recorded in
`docs/handover/claude_md/37_usb_hs_dev_disabled_ep.md` and is deliberately not
changed by this test, which programs only its own endpoint.

<!-- File contains AI-generated response based on internal company sources -->
