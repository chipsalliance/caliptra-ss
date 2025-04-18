
initial begin
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.i3c.i3c.xhci.i3c_csr.ERR_HWIF_IN); // FIXME - remove https://github.com/chipsalliance/i3c-core/issues/22 
    $assertoff(0, caliptra_ss_top_tb.CPTRA_AXI_RD_32BITcptra_ss_mcu_rom_s_axi_if); // FIXME - https://github.com/chipsalliance/caliptra-ss/issues/157
end
