`ifndef IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API
`define IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

interface class caliptra_ss_usb_data_check_api;

  pure virtual function void check_device_descriptor(uvm_object usb_item, string device_name);

  pure virtual function void check_device_address(uvm_object usb_item, string device_name,
                                                  int unsigned expected_address);

  // Standard device GET_STATUS check. The response is a 2-byte status word;
  // usable for dev0, dev1 and hub (recipient=device). bit[0]=Self-Powered,
  // bit[1]=Remote-Wakeup.
  pure virtual function void check_get_status(uvm_object usb_item, string device_name,
                                              bit [15:0] expected);

  // Hub-class GetHubStatus check. The response is 4 bytes: wHubStatus
  // (bytes[1:0]) + wHubChange (bytes[3:2]), each a 16-bit little-endian word.
  pure virtual function void check_hub_status(uvm_object usb_item, string device_name,
                                              bit [15:0] expected_hub_status,
                                              bit [15:0] expected_hub_change);

  // GetDeviceQualifier check. The response is a 10-byte DEVICE_QUALIFIER
  // descriptor (USB 2.0 section 9.6.2, Table 9-9): bLength, bDescriptorType,
  // bcdUSB (LE), bDeviceClass, bDeviceSubClass, bDeviceProtocol,
  // bMaxPacketSize0, bNumConfigurations, bReserved.
  pure virtual function void check_device_qualifier(uvm_object usb_item, string device_name);

  // GET_DESCRIPTOR(CONFIGURATION) check. The response is a 25-byte composite
  // descriptor: a 9-byte CONFIGURATION header (bDescriptorType=0x02) followed
  // by a 9-byte INTERFACE descriptor and a 7-byte ENDPOINT descriptor. The
  // expected values mirror the CONFIGURATION DESCRIPTOR block of the hub ROM
  // constant in
  // third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
  // bmAttributes bit6 (Self-Powered) is runtime-variable in the hub RTL and is
  // masked off before comparison.
  pure virtual function void check_configuration_descriptor(uvm_object usb_item, string device_name);

  // GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION) check. Same 25-byte composite
  // layout as the CONFIGURATION descriptor but with bDescriptorType=0x07. This
  // descriptor is HS-only. The expected values mirror the OTHER SPEED
  // CONFIGURATION DESCRIPTOR block of the hub ROM constant. bmAttributes bit6
  // (Self-Powered) is masked off before comparison.
  pure virtual function void check_other_speed_configuration(uvm_object usb_item, string device_name);

  // GetHubDescriptor check. A hub-class GET_DESCRIPTOR(HUB) request
  // (bmRequestType=0xA0 CLASS/DEVICE, bRequest=0x06, wValue=0x2900,
  // wLength=0x0009) returns the 9-byte Hub Class Descriptor (USB 2.0 section
  // 11.23.2.1, Table 11-13):
  //   byte[0]   bDescLength         (=0x09)
  //   byte[1]   bDescriptorType     (=0x29, HUB)
  //   byte[2]   bNbrPorts           (=0x02)
  //   byte[4:3] wHubCharacteristics (little-endian, =0x0014)
  //   byte[5]   bPwrOn2PwrGood      (=0x00)
  //   byte[6]   bHubContrCurrent    (=0x00)
  //   byte[7]   DeviceRemovable     (=0x06)
  //   byte[8]   PortPwrCtrlMask     (=0xFF)
  // The expected values mirror the HUB DESCRIPTOR block of the hub ROM
  // constant in
  // third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
  pure virtual function void check_hub_descriptor(uvm_object usb_item, string device_name);


endclass:caliptra_ss_usb_data_check_api




`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

