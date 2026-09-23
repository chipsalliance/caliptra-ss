`ifndef IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL
`define IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL

covergroup cp_device(string name) with function sample(int unsigned name_id);
  option.per_instance = 1;
  option.name         = name;
  cp_device_name: coverpoint name_id {
    bins dev0 = {0};
    bins dev1 = {1};
    bins hub  = {2};
  }
endgroup

class caliptra_ss_usb_data_check_api_impl extends uvm_component implements caliptra_ss_usb_data_check_api;

  `uvm_component_utils(caliptra_ss_usb_data_check_api_impl)

  protected const string msg_tag = "USB_DATA_CHECK_API_IMPL";

  typedef enum int {
    DEV_NAME_DEV0    = 0,
    DEV_NAME_DEV1    = 1,
    DEV_NAME_HUB     = 2,
    DEV_NAME_UNKNOWN = 3
  } device_name_e;

  protected device_name_e cov_device_name;

  cp_device cg_get_status;
  cp_device cg_hub_status;
  cp_device cg_device_descriptor;
  cp_device cg_device_addr;
  cp_device cg_device_qualifier;
  cp_device cg_config_descriptor;
  cp_device cg_other_speed_config;
  cp_device cg_hub_descriptor;





  extern function new(string name ="caliptra_ss_usb_data_check_api_impl",
                      uvm_component parent=null);


  extern virtual function void build_phase(uvm_phase phase);

  extern virtual function void check_device_descriptor(uvm_object usb_item, string device_name);

  extern virtual function void check_device_address(uvm_object usb_item, string device_name,
                                                    int unsigned expected_address);

  extern virtual function void check_get_status(uvm_object usb_item, string device_name,
                                                bit [15:0] expected);

  extern virtual function void check_hub_status(uvm_object usb_item, string device_name,
                                                bit [15:0] expected_hub_status,
                                                bit [15:0] expected_hub_change);

  extern virtual function void check_device_qualifier(uvm_object usb_item, string device_name);

  extern virtual function void check_configuration_descriptor(uvm_object usb_item, string device_name);

  extern virtual function void check_other_speed_configuration(uvm_object usb_item, string device_name);

  extern virtual function void check_hub_descriptor(uvm_object usb_item, string device_name);


  // Shared worker for the CONFIGURATION (0x02) and OTHER_SPEED_CONFIGURATION
  // (0x07) descriptors. Both have an identical 25-byte composite layout and
  // differ only in the header bDescriptorType and the bMaxPower byte, so a
  // single routine parameterized by the expected descriptor type and the
  // covergroup handle checks both.
  extern protected function void check_config_like_descriptor(uvm_object   usb_item,
                                                              string       device_name,
                                                              int unsigned exp_bDescriptorType,
                                                              string       descr_label,
                                                              cp_device    cg_handle);

  extern protected function device_name_e name_to_id(string device_name);



endclass:caliptra_ss_usb_data_check_api_impl


function caliptra_ss_usb_data_check_api_impl::new(string name="caliptra_ss_usb_data_check_api_impl",
                                                  uvm_component parent);
  super.new(name,parent);
  cg_device_descriptor = new("check_device_descriptor");
  cg_device_addr       = new("check_device_address");
  cg_get_status        = new("check_get_status");
  cg_hub_status        = new("check_hub_status");
  cg_device_qualifier  = new("check_device_qualifier");
  cg_config_descriptor = new("check_configuration_descriptor");
  cg_other_speed_config = new("check_other_speed_configuration");
  cg_hub_descriptor    = new("check_hub_descriptor");
endfunction:new






// Map the string device_name onto the integral encoding sampled by the
// covergroups. Any unrecognized name falls back to DEV_NAME_UNKNOWN.
function caliptra_ss_usb_data_check_api_impl::device_name_e
    caliptra_ss_usb_data_check_api_impl::name_to_id(string device_name);
  case (device_name)
    "dev0":  return DEV_NAME_DEV0;
    "dev1":  return DEV_NAME_DEV1;
    "hub":   return DEV_NAME_HUB;
    default: return DEV_NAME_UNKNOWN;
  endcase
endfunction:name_to_id


function void caliptra_ss_usb_data_check_api_impl::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(caliptra_ss_usb_data_check_api)::set(null, "uvm_test_top", "usb_data_check_api", this);
endfunction:build_phase

function void caliptra_ss_usb_data_check_api_impl::check_device_descriptor(uvm_object usb_item, 
                                                                           string device_name);

  svt_usb_transfer item;
  bit [3:0]        ep_number;
  int unsigned     num_bytes;
  string           ep_direction;

  // Fields reconstructed from the received payload (little-endian wire order),
  // matching the packed usb_device_descriptor_t layout in usb.h.
  int unsigned act_bLength;
  int unsigned act_bDescriptorType;
  int unsigned act_bcdUSB;
  int unsigned act_bDeviceClass;
  int unsigned act_bDeviceSubClass;
  int unsigned act_bDeviceProtocol;
  int unsigned act_bMaxPacketSize0;
  int unsigned act_idVendor;
  int unsigned act_idProduct;
  int unsigned act_bcdDevice;
  int unsigned act_iManufacturer;
  int unsigned act_iProduct;
  int unsigned act_iSerialNumber;
  int unsigned act_bNumConfigurations;

  // Expected field values, selected by device_name below. The dev0/dev1 values
  // mirror the usb_dev0_device_descriptor / usb_dev1_device_descriptor
  // initializers in src/integration/test_suites/libs/usb/usb.c; the hub values
  // mirror the DEVICE DESCRIPTOR (HUB) block of the ROM constant in
  // third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
  int unsigned exp_bLength;
  int unsigned exp_bDescriptorType;
  int unsigned exp_bcdUSB;
  int unsigned exp_bDeviceClass;
  int unsigned exp_bDeviceSubClass;
  int unsigned exp_bDeviceProtocol;
  int unsigned exp_bMaxPacketSize0;
  int unsigned exp_idVendor;
  int unsigned exp_idProduct;
  int unsigned exp_bcdDevice;
  int unsigned exp_iManufacturer;
  int unsigned exp_iProduct;
  int unsigned exp_iSerialNumber;
  int unsigned exp_bNumConfigurations;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  ep_number    = item.get_endpoint_number_val();
  num_bytes    = item.payload_byte_count();
  ep_direction = item.get_ep_direction().name();

  CHK_NUM_BYTES: assert(num_bytes == 18) else
    `uvm_error(msg_tag, $sformatf("Expected 18 bytes but got %0d from %s EP%0d%s", 
                                  num_bytes, device_name, ep_number, ep_direction))

  `uvm_info(msg_tag, $sformatf("\t raw byte list is: %p", item.payload.data), UVM_LOW)

  // Reconstruct each descriptor field from the payload bytes. Multi-byte
  // fields are little-endian on the wire (low byte first).

  act_bLength            = 32'(item.payload.data[0]);
  act_bDescriptorType    = 32'(item.payload.data[1]);
  act_bcdUSB             = 32'({item.payload.data[3], item.payload.data[2]});
  act_bDeviceClass       = 32'(item.payload.data[4]);
  act_bDeviceSubClass    = 32'(item.payload.data[5]);
  act_bDeviceProtocol    = 32'(item.payload.data[6]);
  act_bMaxPacketSize0    = 32'(item.payload.data[7]);
  act_idVendor           = 32'({item.payload.data[9],  item.payload.data[8]});
  act_idProduct          = 32'({item.payload.data[11], item.payload.data[10]});
  act_bcdDevice          = 32'({item.payload.data[13], item.payload.data[12]});
  act_iManufacturer      = 32'(item.payload.data[14]);
  act_iProduct           = 32'(item.payload.data[15]);
  act_iSerialNumber      = 32'(item.payload.data[16]);
  act_bNumConfigurations = 32'(item.payload.data[17]);

  // Common (device-independent) expected fields.
  exp_bLength            = 18;
  exp_bDescriptorType    = 'h01; // DEVICE descriptor
  exp_bMaxPacketSize0    = 64;
  exp_bNumConfigurations = 1;

  // Device-specific expected fields.
  case (device_name)
    "dev0": begin // usb_dev0_device_descriptor
      exp_bcdUSB          = 'h0200;
      exp_bDeviceClass    = 'hFF;
      exp_bDeviceSubClass = 'h01;
      exp_bDeviceProtocol = 'h01;
      exp_idVendor        = 'h1234;
      exp_idProduct       = 'h0001;
      exp_bcdDevice       = 'h0100;
      exp_iManufacturer   = 'h01;
      exp_iProduct        = 'h02;
      exp_iSerialNumber   = 'h03;
    end
    "dev1": begin // usb_dev1_device_descriptor
      exp_bcdUSB          = 'h0210;
      exp_bDeviceClass    = 'hEF;
      exp_bDeviceSubClass = 'h02;
      exp_bDeviceProtocol = 'h01;
      exp_idVendor        = 'h5678;
      exp_idProduct       = 'h0002;
      exp_bcdDevice       = 'h0200;
      exp_iManufacturer   = 'h01;
      exp_iProduct        = 'h02;
      exp_iSerialNumber   = 'h03;
    end
    "hub": begin // hub DEVICE descriptor (firmware override of RTL ROM)
      // The ROM defaults are idProduct=0xBE00, bcdDevice=0x0100,
      // iManufacturer=0x00, iProduct=0x00, iSerialNumber=0x00. Firmware
      // (usb_hub_init_and_connect() in the MCU USB library) overrides these
      // to non-default values before HUB_CONNECT, while the hub descriptor
      // flip-flop array is still unlocked. bcdUSB, bDeviceClass (hub class),
      // bDeviceSubClass, bDeviceProtocol and idVendor are left at the ROM
      // defaults. See claude_md/19_hub_descriptor_write_map.md.
      exp_bcdUSB          = 'h0200;
      exp_bDeviceClass    = 'h09; // Hub class
      exp_bDeviceSubClass = 'h00;
      exp_bDeviceProtocol = 'h00;
      exp_idVendor        = 'h1FC9; // NXP VID (unchanged)
      exp_idProduct       = 'hBE01; // firmware override (was 'hBE00)
      exp_bcdDevice       = 'h0200; // firmware override (was 'h0100)
      exp_iManufacturer   = 'h01;   // firmware override (was 'h00)
      exp_iProduct        = 'h02;   // firmware override (was 'h00)
      exp_iSerialNumber   = 'h03;   // firmware override (was 'h00)
    end

    default: begin
      `uvm_error(msg_tag, $sformatf("Unknown device_name=%s (only dev0, dev1 and hub are defined)", 
                                    device_name))
      return;
    end
  endcase

  // Field-by-field comparison. Each field has its own labeled check so a
  // failure report names the field, the expected and the actual value.
  CHK_BLENGTH: assert(act_bLength == exp_bLength) else
    `uvm_error(msg_tag, $sformatf("%s bLength mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bLength, act_bLength))
  CHK_BDESCRIPTORTYPE: assert(act_bDescriptorType == exp_bDescriptorType) else
    `uvm_error(msg_tag, $sformatf("%s bDescriptorType mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDescriptorType, act_bDescriptorType))
  CHK_BCDUSB: assert(act_bcdUSB == exp_bcdUSB) else
    `uvm_error(msg_tag, $sformatf("%s bcdUSB mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, exp_bcdUSB, act_bcdUSB))
  CHK_BDEVICECLASS: assert(act_bDeviceClass == exp_bDeviceClass) else
    `uvm_error(msg_tag, $sformatf("%s bDeviceClass mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceClass, act_bDeviceClass))
  CHK_BDEVICESUBCLASS: assert(act_bDeviceSubClass == exp_bDeviceSubClass) else
    `uvm_error(msg_tag, $sformatf("%s bDeviceSubClass mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceSubClass, act_bDeviceSubClass))
  CHK_BDEVICEPROTOCOL: assert(act_bDeviceProtocol == exp_bDeviceProtocol) else
    `uvm_error(msg_tag, $sformatf("%s bDeviceProtocol mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceProtocol, act_bDeviceProtocol))
  CHK_BMAXPACKETSIZE0: assert(act_bMaxPacketSize0 == exp_bMaxPacketSize0) else
    `uvm_error(msg_tag, $sformatf("%s bMaxPacketSize0 mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bMaxPacketSize0, act_bMaxPacketSize0))
  CHK_IDVENDOR: assert(act_idVendor == exp_idVendor) else
    `uvm_error(msg_tag, $sformatf("%s idVendor mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, exp_idVendor, act_idVendor))
  CHK_IDPRODUCT: assert(act_idProduct == exp_idProduct) else
    `uvm_error(msg_tag, $sformatf("%s idProduct mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, exp_idProduct, act_idProduct))
  CHK_BCDDEVICE: assert(act_bcdDevice == exp_bcdDevice) else
    `uvm_error(msg_tag, $sformatf("%s bcdDevice mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, exp_bcdDevice, act_bcdDevice))
  CHK_IMANUFACTURER: assert(act_iManufacturer == exp_iManufacturer) else
    `uvm_error(msg_tag, $sformatf("%s iManufacturer mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_iManufacturer, act_iManufacturer))
  CHK_IPRODUCT: assert(act_iProduct == exp_iProduct) else
    `uvm_error(msg_tag, $sformatf("%s iProduct mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_iProduct, act_iProduct))
  CHK_ISERIALNUMBER: assert(act_iSerialNumber == exp_iSerialNumber) else
    `uvm_error(msg_tag, $sformatf("%s iSerialNumber mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_iSerialNumber, act_iSerialNumber))
  CHK_BNUMCONFIGURATIONS: assert(act_bNumConfigurations == exp_bNumConfigurations) else
    `uvm_error(msg_tag, $sformatf("%s bNumConfigurations mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bNumConfigurations, act_bNumConfigurations))

  `uvm_info(msg_tag, $sformatf("%s device descriptor fields checked from EP%0d%s", 
                               device_name, ep_number, ep_direction), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_device_descriptor.sample(cov_device_name);
endfunction:check_device_descriptor


function void caliptra_ss_usb_data_check_api_impl::check_device_address(uvm_object usb_item, 
                                                                        string device_name,
                                                                        int unsigned expected_address);

  svt_usb_transfer item;
  int unsigned     act_address;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  // get_device_address_val() returns the device address the RTL responded on
  // for this transfer, which is what we compare against the expected value.
  act_address = item.get_device_address_val();

  CHK_DEV_ADDRESS: assert(act_address == expected_address) else
    `uvm_error(msg_tag, $sformatf("%s device address mismatch: expected %0d got %0d", 
                                  device_name, expected_address, act_address))

  `uvm_info(msg_tag, $sformatf("%s device address checked (expected=%0d got=%0d)", 
                               device_name, expected_address, act_address), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_device_addr.sample(cov_device_name);
endfunction:check_device_address


// check_get_status - standard device GET_STATUS response check.
//
// A standard GET_STATUS to a device recipient returns a 2-byte status word
// (USB 2.0 section 9.4.5, Figure 9-4):
//   bit[0] = Self-Powered
//   bit[1] = Remote Wakeup
// All other bits are reserved and returned as zero. This method is usable
// for dev0, dev1 and the hub (all answer a device-recipient GET_STATUS).
function void caliptra_ss_usb_data_check_api_impl::check_get_status(uvm_object usb_item, 
                                                                    string device_name,
                                                                    bit [15:0] expected);

  svt_usb_transfer item;
  int unsigned     num_bytes;
  bit [15:0]       act_status;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  num_bytes = item.payload_byte_count();

  CHK_GET_STATUS_NUM_BYTES: assert(num_bytes == 2) else
    `uvm_error(msg_tag, $sformatf("%s GET_STATUS expected 2 bytes but got %0d", 
                                  device_name, num_bytes))

  // The device status word is the first 16-bit little-endian word of the
  // payload (low byte first).
  act_status = {item.payload.data[1], item.payload.data[0]};

  CHK_GET_STATUS: assert(act_status == expected) else
    `uvm_error(msg_tag, $sformatf("%s GET_STATUS mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, expected, act_status))

  `uvm_info(msg_tag, $sformatf("%s GET_STATUS checked (expected=0x%04h got=0x%04h)", 
                               device_name, expected, act_status), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_get_status.sample(cov_device_name);
endfunction:check_get_status


// check_hub_status - hub-class GetHubStatus response check.
//
// A hub-class GetHubStatus request returns a 4-byte hub status structure
// (USB 2.0 section 11.24.2.6, Table 11-19 / 11-20):
//   bytes[1:0] = wHubStatus  (bit0 Local Power Source, bit1 Over-current)
//   bytes[3:2] = wHubChange  (bit0 Local Power Source Change,
//                             bit1 Over-current Change)
// Only bits [1:0] of each word are defined; all other bits are reserved and
// masked off before comparison.
function void caliptra_ss_usb_data_check_api_impl::check_hub_status(uvm_object usb_item, 
                                                                    string device_name,
                                                                    bit [15:0] expected_hub_status,
                                                                    bit [15:0] expected_hub_change);

  svt_usb_transfer item;
  int unsigned     num_bytes;
  bit [15:0]       act_hub_status;
  bit [15:0]       act_hub_change;
  // Only bits [1:0] of wHubStatus and wHubChange are defined; the rest are
  // reserved and must be ignored in the comparison.
  localparam bit [15:0] HUB_STATUS_MASK = 16'h0003;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  num_bytes = item.payload_byte_count();

  CHK_HUB_STATUS_NUM_BYTES: assert(num_bytes == 4) else
    `uvm_error(msg_tag, $sformatf("%s GetHubStatus expected 4 bytes but got %0d", 
                                  device_name, num_bytes))

  // wHubStatus is the first 16-bit little-endian word, wHubChange the second.
  act_hub_status = {item.payload.data[1], item.payload.data[0]};
  act_hub_change = {item.payload.data[3], item.payload.data[2]};

  CHK_HUB_STATUS: assert((act_hub_status & HUB_STATUS_MASK) == (expected_hub_status & HUB_STATUS_MASK)) else
    `uvm_error(msg_tag, $sformatf("%s wHubStatus mismatch (mask 0x%04h): expected 0x%04h got 0x%04h", 
                                  device_name, HUB_STATUS_MASK, expected_hub_status, act_hub_status))

  CHK_HUB_CHANGE: assert((act_hub_change & HUB_STATUS_MASK) == (expected_hub_change & HUB_STATUS_MASK)) else
    `uvm_error(msg_tag, $sformatf("%s wHubChange mismatch (mask 0x%04h): expected 0x%04h got 0x%04h", 
                                  device_name, HUB_STATUS_MASK, expected_hub_change, act_hub_change))

  `uvm_info(msg_tag, $sformatf("%s GetHubStatus checked (wHubStatus exp=0x%04h got=0x%04h, wHubChange exp=0x%04h got=0x%04h, mask=0x%04h)", 
                               device_name, expected_hub_status, act_hub_status, 
                               expected_hub_change, act_hub_change, HUB_STATUS_MASK), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_hub_status.sample(cov_device_name);
endfunction:check_hub_status


// check_device_qualifier - GetDeviceQualifier response check.
//
// A GET_DESCRIPTOR(DEVICE_QUALIFIER) request returns a 10-byte descriptor
// (USB 2.0 section 9.6.2, Table 9-9):
//   byte[0]   bLength            (=0x0A)
//   byte[1]   bDescriptorType    (=0x06, DEVICE_QUALIFIER)
//   byte[3:2] bcdUSB             (little-endian)
//   byte[4]   bDeviceClass
//   byte[5]   bDeviceSubClass
//   byte[6]   bDeviceProtocol
//   byte[7]   bMaxPacketSize0
//   byte[8]   bNumConfigurations
//   byte[9]   bReserved          (=0x00)
// The expected values mirror the HUB DEVICE QUALIFIER DESCRIPTOR block of the
// ROM constant in
// third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
function void caliptra_ss_usb_data_check_api_impl::check_device_qualifier(uvm_object usb_item, 
                                                                          string device_name);

  svt_usb_transfer item;
  bit [3:0]        ep_number;
  int unsigned     num_bytes;
  string           ep_direction;

  // Fields reconstructed from the received payload (little-endian wire order).
  int unsigned act_bLength;
  int unsigned act_bDescriptorType;
  int unsigned act_bcdUSB;
  int unsigned act_bDeviceClass;
  int unsigned act_bDeviceSubClass;
  int unsigned act_bDeviceProtocol;
  int unsigned act_bMaxPacketSize0;
  int unsigned act_bNumConfigurations;
  int unsigned act_bReserved;

  // Expected field values, selected by device_name below.
  int unsigned exp_bLength;
  int unsigned exp_bDescriptorType;
  int unsigned exp_bcdUSB;
  int unsigned exp_bDeviceClass;
  int unsigned exp_bDeviceSubClass;
  int unsigned exp_bDeviceProtocol;
  int unsigned exp_bMaxPacketSize0;
  int unsigned exp_bNumConfigurations;
  int unsigned exp_bReserved;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  ep_number    = item.get_endpoint_number_val();
  num_bytes    = item.payload_byte_count();
  ep_direction = item.get_ep_direction().name();

  CHK_QUAL_NUM_BYTES: assert(num_bytes == 10) else
    `uvm_error(msg_tag, $sformatf("Expected 10 bytes but got %0d from %s EP%0d%s", 
                                  num_bytes, device_name, ep_number, ep_direction))

  `uvm_info(msg_tag, $sformatf("\t raw byte list is: %p", item.payload.data), UVM_LOW)

  // Reconstruct each descriptor field from the payload bytes. Multi-byte
  // fields are little-endian on the wire (low byte first).
  act_bLength            = 32'(item.payload.data[0]);
  act_bDescriptorType    = 32'(item.payload.data[1]);
  act_bcdUSB             = 32'({item.payload.data[3], item.payload.data[2]});
  act_bDeviceClass       = 32'(item.payload.data[4]);
  act_bDeviceSubClass    = 32'(item.payload.data[5]);
  act_bDeviceProtocol    = 32'(item.payload.data[6]);
  act_bMaxPacketSize0    = 32'(item.payload.data[7]);
  act_bNumConfigurations = 32'(item.payload.data[8]);
  act_bReserved          = 32'(item.payload.data[9]);

  // Common (device-independent) expected fields.
  exp_bLength         = 'h0A;
  exp_bDescriptorType = 'h06; // DEVICE_QUALIFIER descriptor
  exp_bReserved       = 'h00;

  // Device-specific expected fields.
  case (device_name)
    "hub": begin // hub DEVICE QUALIFIER descriptor (firmware override of RTL ROM)
      // The ROM defaults are bDeviceSubClass=0x00, bDeviceProtocol=0x00 and
      // bMaxPacketSize0=0x40. Firmware (usb_hub_init_and_connect() in the MCU
      // USB library) overrides these to non-default values before HUB_CONNECT,
      // while the hub descriptor flip-flop array is still unlocked, via a
      // single clean full-word write of qualifier word1 @ 0x2000_00C4.
      // bcdUSB, bDeviceClass and bNumConfigurations are left at the ROM
      // defaults. See claude_md/19_hub_descriptor_write_map.md.
      exp_bcdUSB             = 'h0200;
      exp_bDeviceClass       = 'h00;
      exp_bDeviceSubClass    = 'h02; // firmware override (was 'h00)
      exp_bDeviceProtocol    = 'h01; // firmware override (was 'h00)
      exp_bMaxPacketSize0    = 'h08; // firmware override (was 'h40)
      exp_bNumConfigurations = 'h01;
    end
    default: begin
      `uvm_error(msg_tag, $sformatf("Unknown device_name=%s (only hub is defined for the device qualifier)", 
                                    device_name))
      return;
    end
  endcase

  // Field-by-field comparison. Each field has its own labeled check so a
  // failure report names the field, the expected and the actual value.
  CHK_QUAL_BLENGTH: assert(act_bLength == exp_bLength) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bLength mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bLength, act_bLength))
  CHK_QUAL_BDESCRIPTORTYPE: assert(act_bDescriptorType == exp_bDescriptorType) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bDescriptorType mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDescriptorType, act_bDescriptorType))
  CHK_QUAL_BCDUSB: assert(act_bcdUSB == exp_bcdUSB) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bcdUSB mismatch: expected 0x%04h got 0x%04h", 
                                  device_name, exp_bcdUSB, act_bcdUSB))
  CHK_QUAL_BDEVICECLASS: assert(act_bDeviceClass == exp_bDeviceClass) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bDeviceClass mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceClass, act_bDeviceClass))
  CHK_QUAL_BDEVICESUBCLASS: assert(act_bDeviceSubClass == exp_bDeviceSubClass) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bDeviceSubClass mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceSubClass, act_bDeviceSubClass))
  CHK_QUAL_BDEVICEPROTOCOL: assert(act_bDeviceProtocol == exp_bDeviceProtocol) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bDeviceProtocol mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bDeviceProtocol, act_bDeviceProtocol))
  CHK_QUAL_BMAXPACKETSIZE0: assert(act_bMaxPacketSize0 == exp_bMaxPacketSize0) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bMaxPacketSize0 mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bMaxPacketSize0, act_bMaxPacketSize0))
  CHK_QUAL_BNUMCONFIGURATIONS: assert(act_bNumConfigurations == exp_bNumConfigurations) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bNumConfigurations mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bNumConfigurations, act_bNumConfigurations))
  CHK_QUAL_BRESERVED: assert(act_bReserved == exp_bReserved) else
    `uvm_error(msg_tag, $sformatf("%s qualifier bReserved mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, exp_bReserved, act_bReserved))

  `uvm_info(msg_tag, $sformatf("%s device qualifier fields checked from EP%0d%s", 
                               device_name, ep_number, ep_direction), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_device_qualifier.sample(cov_device_name);
endfunction:check_device_qualifier


// check_config_like_descriptor - shared worker for the CONFIGURATION and
// OTHER_SPEED_CONFIGURATION descriptors.
//
// A GET_DESCRIPTOR(CONFIGURATION) / GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION)
// request on the hub returns a 25-byte composite descriptor made of three
// concatenated standard descriptors (USB 2.0 sections 9.6.3 / 9.6.4):
//   CONFIGURATION / OTHER_SPEED_CONFIGURATION header (9 bytes):
//     byte[0]    bLength             (=0x09)
//     byte[1]    bDescriptorType     (=0x02 CONFIGURATION / =0x07 OTHER_SPEED)
//     byte[3:2]  wTotalLength        (little-endian, =0x0019)
//     byte[4]    bNumInterfaces      (=0x01)
//     byte[5]    bConfigurationValue (=0x01)
//     byte[6]    iConfiguration      (=0x04, firmware override of ROM 0x00;
//                                     same value on both descriptors per
//                                     USB 2.0 section 9.6.4)
//     byte[7]    bmAttributes        (bit7=1 reserved; bit6 Self-Powered is
//                                     runtime-variable in the hub RTL and is
//                                     masked off before comparison)
//     byte[8]    bMaxPower           (=0xFA both, RTL ROM default, not
//                                     overridden by firmware)
//   INTERFACE descriptor (9 bytes, bytes[9..17]):
//     byte[9]    bLength             (=0x09)
//     byte[10]   bDescriptorType     (=0x04 INTERFACE)
//     byte[11]   bInterfaceNumber    (=0x00)
//     byte[12]   bAlternateSetting   (=0x00)
//     byte[13]   bNumEndpoints       (=0x01)
//     byte[14]   bInterfaceClass     (=0x09 Hub)
//     byte[15]   bInterfaceSubClass  (=0x00)
//     byte[16]   bInterfaceProtocol  (=0x00)
//     byte[17]   iInterface          (=0x00)
//   ENDPOINT descriptor (7 bytes, bytes[18..24]):
//     byte[18]   bLength             (=0x07)
//     byte[19]   bDescriptorType     (=0x05 ENDPOINT)
//     byte[20]   bEndpointAddress    (=0x81 EP1 IN)
//     byte[21]   bmAttributes        (=0x03 Interrupt)
//     byte[23:22] wMaxPacketSize     (little-endian, =0x0001)
//     byte[24]   bInterval           (=0x0F HS branch)
// The expected values mirror the CONFIGURATION / OTHER SPEED CONFIGURATION
// DESCRIPTOR blocks of the hub ROM constant in
// third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl.
function void caliptra_ss_usb_data_check_api_impl::check_config_like_descriptor(uvm_object   usb_item,
                                                                                string       device_name,
                                                                                int unsigned exp_bDescriptorType,
                                                                                string       descr_label,
                                                                                cp_device    cg_handle);

  svt_usb_transfer item;
  bit [3:0]        ep_number;
  int unsigned     num_bytes;
  string           ep_direction;

  // bmAttributes bit6 (Self-Powered) is runtime-variable in the hub RTL and is
  // ignored in the comparison; all other defined bits are checked.
  localparam int unsigned BMATTR_SELF_POWERED_MASK = 'hBF; // ~bit6

  // CONFIGURATION / OTHER_SPEED_CONFIGURATION header fields.
  int unsigned act_cfg_bLength;
  int unsigned act_cfg_bDescriptorType;
  int unsigned act_wTotalLength;
  int unsigned act_bNumInterfaces;
  int unsigned act_bConfigurationValue;
  int unsigned act_iConfiguration;
  int unsigned act_bmAttributes;
  int unsigned act_bMaxPower;
  // INTERFACE descriptor fields.
  int unsigned act_if_bLength;
  int unsigned act_if_bDescriptorType;
  int unsigned act_bInterfaceNumber;
  int unsigned act_bAlternateSetting;
  int unsigned act_bNumEndpoints;
  int unsigned act_bInterfaceClass;
  int unsigned act_bInterfaceSubClass;
  int unsigned act_bInterfaceProtocol;
  int unsigned act_iInterface;
  // ENDPOINT descriptor fields.
  int unsigned act_ep_bLength;
  int unsigned act_ep_bDescriptorType;
  int unsigned act_bEndpointAddress;
  int unsigned act_ep_bmAttributes;
  int unsigned act_wMaxPacketSize;
  int unsigned act_bInterval;

  // Expected values selected by descriptor type (bMaxPower differs).
  int unsigned exp_bMaxPower;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  ep_number    = item.get_endpoint_number_val();
  num_bytes    = item.payload_byte_count();
  ep_direction = item.get_ep_direction().name();

  CHK_CFG_NUM_BYTES: assert(num_bytes == 25) else
    `uvm_error(msg_tag, $sformatf("Expected 25 bytes but got %0d from %s %s EP%0d%s", 
                                  num_bytes, device_name, descr_label, ep_number, ep_direction))

  `uvm_info(msg_tag, $sformatf("\t raw byte list is: %p", item.payload.data), UVM_LOW)

  // Reconstruct each descriptor field from the payload bytes. Multi-byte
  // fields are little-endian on the wire (low byte first).
  act_cfg_bLength         = 32'(item.payload.data[0]);
  act_cfg_bDescriptorType = 32'(item.payload.data[1]);
  act_wTotalLength        = 32'({item.payload.data[3], item.payload.data[2]});
  act_bNumInterfaces      = 32'(item.payload.data[4]);
  act_bConfigurationValue = 32'(item.payload.data[5]);
  act_iConfiguration      = 32'(item.payload.data[6]);
  act_bmAttributes        = 32'(item.payload.data[7]);
  act_bMaxPower           = 32'(item.payload.data[8]);

  act_if_bLength          = 32'(item.payload.data[9]);
  act_if_bDescriptorType  = 32'(item.payload.data[10]);
  act_bInterfaceNumber    = 32'(item.payload.data[11]);
  act_bAlternateSetting   = 32'(item.payload.data[12]);
  act_bNumEndpoints       = 32'(item.payload.data[13]);
  act_bInterfaceClass     = 32'(item.payload.data[14]);
  act_bInterfaceSubClass  = 32'(item.payload.data[15]);
  act_bInterfaceProtocol  = 32'(item.payload.data[16]);
  act_iInterface          = 32'(item.payload.data[17]);

  act_ep_bLength          = 32'(item.payload.data[18]);
  act_ep_bDescriptorType  = 32'(item.payload.data[19]);
  act_bEndpointAddress    = 32'(item.payload.data[20]);
  act_ep_bmAttributes     = 32'(item.payload.data[21]);
  act_wMaxPacketSize      = 32'({item.payload.data[23], item.payload.data[22]});
  act_bInterval           = 32'(item.payload.data[24]);

  // bMaxPower is 0xFA (500 mA) for BOTH descriptors in the current RTL ROM
  // (usb_ep0_hub_descr.m.vhdl lines 134 and 205). The default was changed in
  // the latest RTL - it is NOT 0x14 for the CONFIGURATION descriptor any more.
  // Firmware does not override bMaxPower, so the expectation tracks the ROM.
  exp_bMaxPower = 'hFA;

  // CONFIGURATION / OTHER_SPEED_CONFIGURATION header checks.
  CHK_CFG_BLENGTH: assert(act_cfg_bLength == 'h09) else
    `uvm_error(msg_tag, $sformatf("%s %s bLength mismatch: expected 0x09 got 0x%02h", 
                                  device_name, descr_label, act_cfg_bLength))
  CHK_CFG_BDESCRIPTORTYPE: assert(act_cfg_bDescriptorType == exp_bDescriptorType) else
    `uvm_error(msg_tag, $sformatf("%s %s bDescriptorType mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, descr_label, exp_bDescriptorType, act_cfg_bDescriptorType))
  CHK_CFG_WTOTALLENGTH: assert(act_wTotalLength == 'h0019) else
    `uvm_error(msg_tag, $sformatf("%s %s wTotalLength mismatch: expected 0x0019 got 0x%04h", 
                                  device_name, descr_label, act_wTotalLength))
  CHK_CFG_BNUMINTERFACES: assert(act_bNumInterfaces == 'h01) else
    `uvm_error(msg_tag, $sformatf("%s %s bNumInterfaces mismatch: expected 0x01 got 0x%02h", 
                                  device_name, descr_label, act_bNumInterfaces))
  CHK_CFG_BCONFIGURATIONVALUE: assert(act_bConfigurationValue == 'h01) else
    `uvm_error(msg_tag, $sformatf("%s %s bConfigurationValue mismatch: expected 0x01 got 0x%02h", 
                                  device_name, descr_label, act_bConfigurationValue))
  // iConfiguration is firmware-overridden from the ROM default 0x00 to 0x04.
  // The same value is written to BOTH the CONFIGURATION and the
  // OTHER_SPEED_CONFIGURATION header (USB 2.0 section 9.6.4 requires the
  // other-speed fields to mirror the configuration descriptor), so this shared
  // worker expects 0x04 regardless of descr_label. See
  // claude_md/19_hub_descriptor_write_map.md.
  CHK_CFG_ICONFIGURATION: assert(act_iConfiguration == 'h04) else
    `uvm_error(msg_tag, $sformatf("%s %s iConfiguration mismatch: expected 0x04 got 0x%02h", 
                                  device_name, descr_label, act_iConfiguration))
  // bmAttributes bit7 must be 1 (reserved, always set); bit6 (Self-Powered) is
  // runtime-variable and masked off; bits[4:0] are reserved and zero.
  CHK_CFG_BMATTRIBUTES: assert((act_bmAttributes & BMATTR_SELF_POWERED_MASK) == ('h80 & BMATTR_SELF_POWERED_MASK)) else
    `uvm_error(msg_tag, $sformatf("%s %s bmAttributes mismatch (mask 0x%02h, bit6 ignored): expected 0x80 got 0x%02h", 
                                  device_name, descr_label, BMATTR_SELF_POWERED_MASK, act_bmAttributes))
  CHK_CFG_BMAXPOWER: assert(act_bMaxPower == exp_bMaxPower) else
    `uvm_error(msg_tag, $sformatf("%s %s bMaxPower mismatch: expected 0x%02h got 0x%02h", 
                                  device_name, descr_label, exp_bMaxPower, act_bMaxPower))

  // INTERFACE descriptor checks.
  CHK_IF_BLENGTH: assert(act_if_bLength == 'h09) else
    `uvm_error(msg_tag, $sformatf("%s %s interface bLength mismatch: expected 0x09 got 0x%02h", 
                                  device_name, descr_label, act_if_bLength))
  CHK_IF_BDESCRIPTORTYPE: assert(act_if_bDescriptorType == 'h04) else
    `uvm_error(msg_tag, $sformatf("%s %s interface bDescriptorType mismatch: expected 0x04 got 0x%02h", 
                                  device_name, descr_label, act_if_bDescriptorType))
  CHK_IF_BINTERFACENUMBER: assert(act_bInterfaceNumber == 'h00) else
    `uvm_error(msg_tag, $sformatf("%s %s bInterfaceNumber mismatch: expected 0x00 got 0x%02h", 
                                  device_name, descr_label, act_bInterfaceNumber))
  CHK_IF_BALTERNATESETTING: assert(act_bAlternateSetting == 'h00) else
    `uvm_error(msg_tag, $sformatf("%s %s bAlternateSetting mismatch: expected 0x00 got 0x%02h", 
                                  device_name, descr_label, act_bAlternateSetting))
  CHK_IF_BNUMENDPOINTS: assert(act_bNumEndpoints == 'h01) else
    `uvm_error(msg_tag, $sformatf("%s %s bNumEndpoints mismatch: expected 0x01 got 0x%02h", 
                                  device_name, descr_label, act_bNumEndpoints))
  CHK_IF_BINTERFACECLASS: assert(act_bInterfaceClass == 'h09) else
    `uvm_error(msg_tag, $sformatf("%s %s bInterfaceClass mismatch: expected 0x09 got 0x%02h", 
                                  device_name, descr_label, act_bInterfaceClass))
  CHK_IF_BINTERFACESUBCLASS: assert(act_bInterfaceSubClass == 'h00) else
    `uvm_error(msg_tag, $sformatf("%s %s bInterfaceSubClass mismatch: expected 0x00 got 0x%02h", 
                                  device_name, descr_label, act_bInterfaceSubClass))
  CHK_IF_BINTERFACEPROTOCOL: assert(act_bInterfaceProtocol == 'h00) else
    `uvm_error(msg_tag, $sformatf("%s %s bInterfaceProtocol mismatch: expected 0x00 got 0x%02h", 
                                  device_name, descr_label, act_bInterfaceProtocol))
  CHK_IF_IINTERFACE: assert(act_iInterface == 'h00) else
    `uvm_error(msg_tag, $sformatf("%s %s iInterface mismatch: expected 0x00 got 0x%02h", 
                                  device_name, descr_label, act_iInterface))

  // ENDPOINT descriptor checks.
  CHK_EP_BLENGTH: assert(act_ep_bLength == 'h07) else
    `uvm_error(msg_tag, $sformatf("%s %s endpoint bLength mismatch: expected 0x07 got 0x%02h", 
                                  device_name, descr_label, act_ep_bLength))
  CHK_EP_BDESCRIPTORTYPE: assert(act_ep_bDescriptorType == 'h05) else
    `uvm_error(msg_tag, $sformatf("%s %s endpoint bDescriptorType mismatch: expected 0x05 got 0x%02h", 
                                  device_name, descr_label, act_ep_bDescriptorType))
  CHK_EP_BENDPOINTADDRESS: assert(act_bEndpointAddress == 'h81) else
    `uvm_error(msg_tag, $sformatf("%s %s bEndpointAddress mismatch: expected 0x81 got 0x%02h", 
                                  device_name, descr_label, act_bEndpointAddress))
  CHK_EP_BMATTRIBUTES: assert(act_ep_bmAttributes == 'h03) else
    `uvm_error(msg_tag, $sformatf("%s %s endpoint bmAttributes mismatch: expected 0x03 got 0x%02h", 
                                  device_name, descr_label, act_ep_bmAttributes))
  CHK_EP_WMAXPACKETSIZE: assert(act_wMaxPacketSize == 'h0001) else
    `uvm_error(msg_tag, $sformatf("%s %s wMaxPacketSize mismatch: expected 0x0001 got 0x%04h", 
                                  device_name, descr_label, act_wMaxPacketSize))
  CHK_EP_BINTERVAL: assert(act_bInterval == 'h0F) else
    `uvm_error(msg_tag, $sformatf("%s %s bInterval mismatch: expected 0x0F got 0x%02h", 
                                  device_name, descr_label, act_bInterval))

  `uvm_info(msg_tag, $sformatf("%s %s descriptor fields checked from EP%0d%s", 
                               device_name, descr_label, ep_number, ep_direction), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_handle.sample(cov_device_name);
endfunction:check_config_like_descriptor


// check_configuration_descriptor - GET_DESCRIPTOR(CONFIGURATION) response
// check (bDescriptorType=0x02). Delegates to the shared worker.
function void caliptra_ss_usb_data_check_api_impl::check_configuration_descriptor(uvm_object usb_item, 
                                                                                  string device_name);
  check_config_like_descriptor(.usb_item(usb_item),
                               .device_name(device_name),
                               .exp_bDescriptorType('h02),
                               .descr_label("configuration"),
                               .cg_handle(cg_config_descriptor));
endfunction:check_configuration_descriptor


// check_other_speed_configuration - GET_DESCRIPTOR(OTHER_SPEED_CONFIGURATION)
// response check (bDescriptorType=0x07). Delegates to the shared worker.
function void caliptra_ss_usb_data_check_api_impl::check_other_speed_configuration(uvm_object usb_item, 
                                                                                   string device_name);
  check_config_like_descriptor(.usb_item(usb_item),
                               .device_name(device_name),
                               .exp_bDescriptorType('h07),
                               .descr_label("other_speed_configuration"),
                               .cg_handle(cg_other_speed_config));
endfunction:check_other_speed_configuration


// check_hub_descriptor - GetHubDescriptor response check.
//
// A hub-class GET_DESCRIPTOR(HUB) request (bmRequestType=0xA0 CLASS/DEVICE,
// bRequest=0x06, wValue=0x2900, wLength=0x0009) returns the 9-byte Hub Class
// Descriptor (USB 2.0 section 11.23.2.1, Table 11-13):
//   byte[0]   bDescLength         (=0x09)
//   byte[1]   bDescriptorType     (=0x29, HUB)
//   byte[2]   bNbrPorts           (=0x02, 2 downstream ports)
//   byte[4:3] wHubCharacteristics (little-endian, =0x0014)
//   byte[5]   bPwrOn2PwrGood      (=0x32, firmware override of ROM 0x00)
//   byte[6]   bHubContrCurrent    (=0x64, firmware override of ROM 0x00)
//   byte[7]   DeviceRemovable     (=0x0A, firmware override of ROM 0x06)
//   byte[8]   PortPwrCtrlMask     (=0xFF)
// bDescLength, bDescriptorType, bNbrPorts, wHubCharacteristics and
// PortPwrCtrlMask mirror the HUB DESCRIPTOR block of the hub ROM constant in
// third_party/usb_hub_composite_device/RTL/RTL/usb_ep0_hub_descr.m.vhdl and
// have no firmware override. bPwrOn2PwrGood, bHubContrCurrent and
// DeviceRemovable ARE overridden by firmware (usb_hub_init_and_connect() in
// the MCU USB library) before HUB_CONNECT, while the hub descriptor flip-flop
// array is still unlocked, via a single clean full-word write of hub class
// descriptor word1 @ 0x2000_0084. See claude_md/19_hub_descriptor_write_map.md.
// The descriptor is speed-independent (same values in FS and HS).
function void caliptra_ss_usb_data_check_api_impl::check_hub_descriptor(uvm_object usb_item,
                                                                        string device_name);

  svt_usb_transfer item;
  bit [3:0]        ep_number;
  int unsigned     num_bytes;
  string           ep_direction;

  // Fields reconstructed from the received payload (little-endian wire order).
  int unsigned act_bDescLength;
  int unsigned act_bDescriptorType;
  int unsigned act_bNbrPorts;
  int unsigned act_wHubCharacteristics;
  int unsigned act_bPwrOn2PwrGood;
  int unsigned act_bHubContrCurrent;
  int unsigned act_DeviceRemovable;
  int unsigned act_PortPwrCtrlMask;

  // Cast first: all accesses to item below are invalid until the cast succeeds.
  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  ep_number    = item.get_endpoint_number_val();
  num_bytes    = item.payload_byte_count();
  ep_direction = item.get_ep_direction().name();

  CHK_HUBDESC_NUM_BYTES: assert(num_bytes == 9) else
    `uvm_error(msg_tag, $sformatf("Expected 9 bytes but got %0d from %s EP%0d%s",
                                  num_bytes, device_name, ep_number, ep_direction))

  `uvm_info(msg_tag, $sformatf("\t raw byte list is: %p", item.payload.data), UVM_LOW)

  // Reconstruct each descriptor field from the payload bytes. Multi-byte
  // fields are little-endian on the wire (low byte first).
  act_bDescLength         = 32'(item.payload.data[0]);
  act_bDescriptorType     = 32'(item.payload.data[1]);
  act_bNbrPorts           = 32'(item.payload.data[2]);
  act_wHubCharacteristics = 32'({item.payload.data[4], item.payload.data[3]});
  act_bPwrOn2PwrGood      = 32'(item.payload.data[5]);
  act_bHubContrCurrent    = 32'(item.payload.data[6]);
  act_DeviceRemovable     = 32'(item.payload.data[7]);
  act_PortPwrCtrlMask     = 32'(item.payload.data[8]);

  // Only the hub answers a GetHubDescriptor request.
  if (device_name != "hub") begin
    `uvm_error(msg_tag, $sformatf("Unknown device_name=%s (only hub is defined for the hub descriptor)",
                                  device_name))
    return;
  end

  // Field-by-field comparison. Each field has its own labeled check so a
  // failure report names the field, the expected and the actual value.
  CHK_HUBDESC_BDESCLENGTH: assert(act_bDescLength == 'h09) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor bDescLength mismatch: expected 0x09 got 0x%02h",
                                  device_name, act_bDescLength))
  CHK_HUBDESC_BDESCRIPTORTYPE: assert(act_bDescriptorType == 'h29) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor bDescriptorType mismatch: expected 0x29 got 0x%02h",
                                  device_name, act_bDescriptorType))
  CHK_HUBDESC_BNBRPORTS: assert(act_bNbrPorts == 'h02) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor bNbrPorts mismatch: expected 0x02 got 0x%02h",
                                  device_name, act_bNbrPorts))
  CHK_HUBDESC_WHUBCHARACTERISTICS: assert(act_wHubCharacteristics == 'h0014) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor wHubCharacteristics mismatch: expected 0x0014 got 0x%04h",
                                  device_name, act_wHubCharacteristics))
  CHK_HUBDESC_BPWRON2PWRGOOD: assert(act_bPwrOn2PwrGood == 'h32) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor bPwrOn2PwrGood mismatch: expected 0x32 got 0x%02h",
                                  device_name, act_bPwrOn2PwrGood))
  CHK_HUBDESC_BHUBCONTRCURRENT: assert(act_bHubContrCurrent == 'h64) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor bHubContrCurrent mismatch: expected 0x64 got 0x%02h",
                                  device_name, act_bHubContrCurrent))
  CHK_HUBDESC_DEVICEREMOVABLE: assert(act_DeviceRemovable == 'h0A) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor DeviceRemovable mismatch: expected 0x0A got 0x%02h",
                                  device_name, act_DeviceRemovable))
  CHK_HUBDESC_PORTPWRCTRLMASK: assert(act_PortPwrCtrlMask == 'hFF) else
    `uvm_error(msg_tag, $sformatf("%s hub descriptor PortPwrCtrlMask mismatch: expected 0xFF got 0x%02h",
                                  device_name, act_PortPwrCtrlMask))

  `uvm_info(msg_tag, $sformatf("%s hub descriptor fields checked from EP%0d%s",
                               device_name, ep_number, ep_direction), UVM_LOW)

  // Collect functional coverage as the last step of the method.
  cov_device_name = name_to_id(device_name);
  cg_hub_descriptor.sample(cov_device_name);
endfunction:check_hub_descriptor



`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL




