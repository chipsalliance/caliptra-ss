`ifndef IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API
`define IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

interface class caliptra_ss_usb_data_check_api;

  pure virtual function void check_device_descriptor(uvm_object usb_item, int unsigned device_idx);


endclass:caliptra_ss_usb_data_check_api
`endif // IFDEF_GUARD_CALIPTRA_SS_USB_DATA_CHECK_API

