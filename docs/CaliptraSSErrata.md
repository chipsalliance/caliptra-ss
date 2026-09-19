<div align="center">
  <img src="./images/OCP_logo.png" alt="OCP Logo">
</div>

<h1 align="center"> Caliptra Subsystem Errata</h1>
<h3 align="center"> Version 2p1 </h3>

- [Scope](#scope)
- [Issues](#issues)
  - [ERRATA-000: I3C HDR Traffic](#errata-000-i3c-hdr-traffic)

# Scope

This document lists all known issues for this Caliptra-SS release.

Each issue has identifier of the form `ERRATA-###` for cross-references.




# Issues

## ERRATA-000: I3C HDR Traffic

**Type:**
Functional  

**Description:**  
I3C is an SDR traffic that should be able to tollerage HDR traffic. The I3C implementation does not detect HDR entry and ignore I3C traffic until it sees an HDR exit pattern.

This is directly tied to I3C release: [v1p4-patch](https://github.com/chipsalliance/i3c-core/releases/tag/v1p4-patch)

**Conditions:**  
I3C bus enters HDR mode and HDR traffic is put on the I3C bus.

**Impact:**  
When I3C bus enters HDR mode the Caliptra I3C can inadvertantly accept and/or respond to I3C HDR traffic. This could cause corruption on the bus, or cause the Caliptra I3C to become corrupt. 

**Workaround:**  
No HDR traffic is allowed on the I3C bus.

**Fix:**  
Future revisions of I3C will properly detect and ignore HDR traffic.

