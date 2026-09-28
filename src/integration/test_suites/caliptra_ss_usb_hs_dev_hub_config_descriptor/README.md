# caliptra_ss_usb_hs_dev_hub_config_descriptor

**Testcase:** `caliptra_ss_usb_hs_dev_hub_config_descriptor`

High-Speed test that checks the CONFIGURATION and OTHER_SPEED_CONFIGURATION
descriptors returned by the on-chip hub. OTHER_SPEED_CONFIGURATION is defined
only for HS-capable devices, so this test is HS-only.

After enumeration completes (hub at address 1, USBDC0/dev0 at address 2), the
VIP host sequence `caliptra_ss_usb_hub_config_descriptor_sequence`:

1. Re-anchors the VIP host onto the hub (address 1).
2. Issues `GET_DESCRIPTOR(CONFIGURATION)` (bRequest=0x06, wValue=0x0200,
   wIndex=0x0000, wLength=0x0019) and checks the 25-byte composite descriptor
   via `usb_data_check_api.check_configuration_descriptor("hub")`.
3. Issues `GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION)` (bRequest=0x06,
   wValue=0x0700, wIndex=0x0000, wLength=0x0019) and checks the 25-byte
   composite descriptor via
   `usb_data_check_api.check_other_speed_configuration("hub")`.

Each 25-byte response is a 9-byte configuration/other-speed header followed by
a 9-byte interface descriptor and a 7-byte endpoint descriptor. The expected
values mirror the CONFIGURATION / OTHER SPEED CONFIGURATION DESCRIPTOR blocks of
the hub ROM constant in
`third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl`. The
`bmAttributes` bit6 (Self-Powered) is runtime-variable in the hub RTL and is
masked off before comparison. `bMaxPower` differs between the two descriptors
(0x14 for CONFIGURATION, 0xFA for OTHER_SPEED_CONFIGURATION).

## Files

| File | Description |
|------|-------------|
| `caliptra_ss_usb_hub_config_descriptor_sequence.svh` | Hub-aware enumeration + GET_DESCRIPTOR(CONFIGURATION / OTHER_SPEED_CONFIGURATION) VIP sequence |
| `caliptra_ss_usb_hs_dev_hub_config_descriptor_test.svh` | HS UVM test class (selects the sequence as default_sequence) |
| `caliptra_ss_usb_hs_dev_hub_config_descriptor.c` | MCU firmware: hub bring-up + EP0 event loop |
| `caliptra_ss_usb_hs_dev_hub_config_descriptor.yml` | Simulation run config |

The descriptor responses are produced entirely by the hub-composite RTL ROM, so
the firmware is the standard hub bring-up / EP0 poll loop (identical to
`caliptra_ss_usb_hs_dev_get_hub_status`).
