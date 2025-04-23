
initial begin
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.i3c.i3c.xhci.i3c_csr.ERR_HWIF_IN); // FIXME - remove https://github.com/chipsalliance/i3c-core/issues/22 
    $assertoff(0, caliptra_ss_top_tb.caliptra_ss_dut.mci_top_i.LCC_state_translator.DebugLockedCheck_A); // FIXME
end
