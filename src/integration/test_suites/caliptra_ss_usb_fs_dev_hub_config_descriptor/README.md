# caliptra_ss_usb_fs_dev_hub_config_descriptor

**Testcase:** `caliptra_ss_usb_fs_dev_hub_config_descriptor`

Full-Speed variant of `caliptra_ss_usb_hs_dev_hub_config_descriptor`. It checks
the CONFIGURATION descriptor returned by the on-chip hub on a link forced to
full speed (`high_speed_capable=0`). Unlike the HS test it does **not** check
OTHER_SPEED_CONFIGURATION: that descriptor is defined only for HS-capable
devices and is not valid on an FS-only link.

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence`:

1. Re-anchors the VIP host onto the hub (address 1).
2. Issues `GET_DESCRIPTOR(CONFIGURATION)` (bRequest=0x06, wValue=0x0200,
   wIndex=0x0000, wLength=0x0019) and checks the 25-byte composite descriptor
   via `usb_data_check_api.check_configuration_descriptor("hub")`.

The 25-byte response is a 9-byte configuration header followed by a 9-byte
interface descriptor and a 7-byte endpoint descriptor. The expected values
mirror the CONFIGURATION DESCRIPTOR block of the hub ROM constant in
`third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl`. The
`bmAttributes` bit6 (Self-Powered) is runtime-variable in the hub RTL and is
masked off before comparison.

## MCU firmware (interrupt-driven / IRQ)

Unlike the FS `get_hub_status` firmware (which is a pure INTSTAT polling loop),
this test's MCU firmware uses the **interrupt-driven (IRQ)** approach, mirroring
the HS `hub_config_descriptor` firmware:

- Includes `mcu_isr.h` (this is what links `mcu_isr.o`).
- Calls `init_usb_interrupts()` to enable the USB interrupt (PIC vector 3).
- The main loop drains the ISR mailbox (`mcu_intr_rcv.usb`) instead of reading
  and write-1-clearing INTSTAT directly. `service_usb_intr()` acknowledges
  INTSTAT in the ISR, so the foreground loop only snapshots and clears the
  mailbox bits.

The only functional difference from the HS firmware is Full-Speed bring-up:
`boot_usb_core_fs()` (instead of `boot_usb_core()`) sets `DEVCMDSTAT.PFSC`
(bit 21) so the device suppresses the K-chirp and the link negotiates and stays
at full speed for the FS-only host VIP.

The descriptor responses themselves are produced entirely by the hub-composite
RTL ROM, so no test-specific firmware logic is required beyond the standard hub
bring-up and interrupt-serviced EP0 event loop.

## Files

| File | Description |
|------|-------------|
| `caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence.svh` | Hub-aware enumeration + GET_DESCRIPTOR(CONFIGURATION) VIP sequence (FS, no OTHER_SPEED_CONFIGURATION) |
| `caliptra_ss_usb_fs_dev_hub_config_descriptor_test.svh` | FS UVM test class (forces FS-only VIP cfg, selects the sequence as default_sequence) |
| `caliptra_ss_usb_fs_dev_hub_config_descriptor.c` | MCU firmware: FS hub bring-up + interrupt-driven EP0 event loop |
| `caliptra_ss_usb_fs_dev_hub_config_descriptor.yml` | Simulation run config |
| `cptra_bringup.c` | Caliptra core bring-up companion firmware |
| `caliptra_isr.h` | Caliptra ISR service routines companion header |
