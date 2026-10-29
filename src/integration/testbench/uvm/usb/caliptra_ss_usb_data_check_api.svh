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
  //
  // The same check is equally valid for recipient=endpoint (USB 2.0 section
  // 9.4.5, bmRequestType=0x82, wIndex=endpoint address). In that case the
  // returned 2-byte word has bit[0]=ENDPOINT_HALT and all other bits reserved
  // zero, so pass expected=16'h0001 for a halted endpoint and 16'h0000 for a
  // running one. On the compound hub the only Halt-able endpoint is EP1 IN
  // (wIndex=0x0081); see caliptra_ss_usb_hs_hub_endpoint_halt_sequence.svh.
  pure virtual function void check_get_status(uvm_object usb_item, string device_name,
                                              bit [15:0] expected);

  // Standard GET_INTERFACE check (USB 2.0 section 9.4.4). A GET_INTERFACE
  // request (bmRequestType=0x81 IN/STANDARD/INTERFACE, bRequest=0x0A,
  // wValue=0x0000, wIndex=interface number, wLength=0x0001) returns a single
  // byte holding the currently selected bAlternateSetting of that interface.
  // The compound hub EP0 answers this request from its descriptor RAM with a
  // constant 0x00: the hub exposes one interface with a single alternate
  // setting (see C_STD_REQ_GET_INTERFACE in
  // RTL/INTERFACE/usb_ep_config_hub_pkg.p.vhdl). The embedded device
  // controllers return their per-controller bAlternateSetting shadow in firmware,
  // so "hub", "dev0", and "dev1" are valid device_name values here.
  pure virtual function void check_get_interface(uvm_object usb_item, string device_name,
                                                 bit [7:0] expected_alt_setting);

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

  // GET_DESCRIPTOR(BOS) check. The response is a 12-byte Binary Device Object
  // Store: a 5-byte BOS header (bDescriptorType=0x0F) followed by a single
  // 7-byte DEVICE_CAPABILITY descriptor (bDescriptorType=0x10) of type USB 2.0
  // Extension (bDevCapabilityType=0x02) whose bmAttributes advertises LPM.
  // The expected values mirror the BOS DESCRIPTOR block of the hub ROM
  // constant in
  // third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
  pure virtual function void check_bos_descriptor(uvm_object usb_item, string device_name);


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

  // Hub PHY test-mode check (SET_FEATURE(DEVICE, TEST_MODE) accept/reject).
  // Like check_device_speed this reads the RTL through usb_dev_addr_probe, so
  // there is no usb_item argument and no USB transfer is involved.
  //
  // SET_FEATURE(TEST_MODE) is wValue=0x0002 with the test selector in
  // wIndex[15:8]. The hub EP0 handler accepts selectors 1..5 (Test_J, Test_K,
  // Test_SE0_NAK, Test_Packet, Test_Force_Enable) and stalls anything above 5
  // (see C_STD_REQ_SET_FEATURE_DEV in usb_ep0_handler.m.vhdl). On acceptance it
  // loads usb_phy_test_mode with selector[2:0]; on rejection the register is
  // left untouched. It resets to 3'b000 and no handler path ever clears it, so:
  //   expected = 3'b000        -> the request must have been rejected
  //   expected = selector[2:0] -> the request must have been accepted
  //
  // Only "hub" is a valid device_name: test mode is implemented for the hub
  // only (the compound device's downstream ports are neither removable nor
  // accessible, so the handler restricts the feature to device index 0).
  //
  // Caution for sequence authors: once a test mode is accepted, the PIE enters
  // BUS_EVENT_TEST_MODE and its only documented exit is a power cycle
  // (usb_pie.m.vhdl). An accepted SET_FEATURE(TEST_MODE) must therefore be the
  // last USB activity of a test.
  pure virtual function void check_phy_test_mode(string device_name,
                                                 bit [2:0] expected_test_mode);

  // Note: there is no CHIP_ID check in this API. CHIP_ID is INFO[31:16] =
  // {C_MAJOR_REV, C_MINOR_REV}, both VHDL generics of usb_reg_if, and VCS does
  // not support a cross-module reference whose target is a VHDL generic
  // (Error-[VHDLXMRE-NS]), so the value cannot be bridged into the TB. CHIP_ID
  // is checked in firmware instead, by reading the INFO register: see
  // usb_check_chip_id() in src/integration/test_suites/libs/usb/usb.c.


endclass:caliptra_ss_usb_data_check_api




`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

