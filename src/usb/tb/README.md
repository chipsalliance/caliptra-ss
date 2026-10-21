# USB VIP-only tests

The Synopsys USB VIP owns all USB stimulus and observation. The top-level
UTMI wiring connects the DUT directly to the VIP; there is no custom UTMI
agent, packet mux, pin-driving sequence, or pin-sampling monitor.

Ordinary traffic uses protocol transfers. Directed packet exceptions and
explicit ISO token/data scheduling use the documented USB 2.0 packet
sequencer. These scenarios complete protocol traffic and stop automatic SOFs
before sending individual packets, then restore automatic SOFs afterwards.

The link-monitor callback records decoded packets. The remote PHY-monitor
callback collects the VIP's byte descriptors, including PID and CRC bytes,
through EOP. RX is toward the DUT; TX is from the DUT. Queue-backed DATA
observations cannot lose packets while an independent AXI checker runs.

AXI/RAL checks still verify DUT descriptors, SRAM, interrupt status, and
receive-time EPSKIP ordering. The VIP does not know the DUT's DMA layout.
See `USB_VIP_GAPS.md` at the repository root for excluded tests and remaining
capability or validation gaps.
