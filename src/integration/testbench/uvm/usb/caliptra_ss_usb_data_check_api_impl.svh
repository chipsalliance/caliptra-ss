`ifndef IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL
`define IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL


class caliptra_ss_usb_data_check_api_impl extends uvm_component implements caliptra_ss_usb_data_check_api;
  `uvm_component_utils(caliptra_ss_usb_data_check_api_impl)

  protected const string msg_tag = "USB_DATA_CHECK_API_IMPL";

  extern function new(string name ="caliptra_ss_usb_data_check_api_impl",
                      uvm_component parent=null);

  extern virtual function void build_phase(uvm_phase phase);

  extern virtual function void check_device_descriptor(uvm_object usb_item, int unsigned device_idx);
endclass:caliptra_ss_usb_data_check_api_impl


function caliptra_ss_usb_data_check_api_impl::new(string name="caliptra_ss_usb_data_check_api_impl",
                                                  uvm_component parent);
  super.new(name,parent);
endfunction:new

function void caliptra_ss_usb_data_check_api_impl::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(caliptra_ss_usb_data_check_api)::set(null, "uvm_test_top", "usb_data_check_api", this);
endfunction:build_phase

function void caliptra_ss_usb_data_check_api_impl::check_device_descriptor(uvm_object usb_item, 
                                                                           int unsigned device_idx);

  svt_usb_transfer item;

  if($cast(item,usb_item) != 1 || usb_item == null) begin
    `uvm_fatal(msg_tag, "impossible to cast usb_item to svt_usb_transfer")
  end

  `uvm_info(msg_tag, $sformatf("Got item from DEV%0d EP%0d %s. Total number of bytes is %0d", 
                                device_idx,
                                item.get_endpoint_number_val(), 
                                item.get_ep_direction().name(), 
                                item.payload_byte_count()),UVM_LOW)
  
  `uvm_info(msg_tag, $sformatf("\t raw byte list is: %p", item.payload.data), UVM_LOW)
endfunction:check_device_descriptor
`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API_IMPL