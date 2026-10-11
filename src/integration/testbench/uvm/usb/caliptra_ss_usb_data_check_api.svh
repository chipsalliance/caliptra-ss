// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
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

  // Negotiated link speed check (DEVCMDSTAT.Speed, bits [23:22]). The value is
  // read straight out of the RTL through usb_dev_addr_probe, so no USB
  // transfer is involved and there is no usb_item argument. expected_speed
  // uses the IP encoding from usb_subcmp_pkg.p.vhdl:
  //   FULL_SPEED = 2'b01, HIGH_SPEED = 2'b10.
  // Only "dev0" and "dev1" are defined. Both names resolve to the same
  // compound-level net (a single upstream link means a single negotiated
  // speed), so checking both does not add independent coverage. See the header
  // of src/integration/testbench/usb_dev_addr_probe.sv.
  pure virtual function void check_device_speed(string device_name,
                                               bit [1:0] expected_speed);

  // Note: there is no CHIP_ID check in this API. CHIP_ID is INFO[31:16] =
  // {C_MAJOR_REV, C_MINOR_REV}, both VHDL generics of usb_reg_if, and VCS does
  // not support a cross-module reference whose target is a VHDL generic
  // (Error-[VHDLXMRE-NS]), so the value cannot be bridged into the TB. CHIP_ID
  // is checked in firmware instead, by reading the INFO register: see
  // usb_check_chip_id() in src/integration/test_suites/libs/usb/usb.c.


endclass:caliptra_ss_usb_data_check_api




`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

