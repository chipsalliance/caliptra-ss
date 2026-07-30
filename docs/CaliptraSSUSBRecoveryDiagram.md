# Caliptra Subsystem USB OCP Recovery Boot Flow

This document is the command-level source list for a later stick diagram. It
uses these actors:

| Actor | Responsibility |
|---|---|
| Recovery Agent (Host) | Enumerates the USB device, discovers recovery capabilities, pushes each recovery image, requests activation, and monitors status. |
| Recovery Device (USB Core) | Implements USB device EP0, exposes the OCP Recovery interface and command registers, buffers image data, reports status, and signals image availability. |
| Device Firmware (Caliptra) | Initializes the USB device path, consumes and authenticates recovery images, updates recovery state, and boots each accepted image. |

## Scope and interpretation

- The normative protocol source is **OCP Secure Firmware Recovery v1.1**.
- The selected image-transfer mechanism is the **Indirect FIFO CMS** because
  that is the Caliptra Subsystem USB recovery data path.
- USB-controller register names and internal interrupt signals are
  Caliptra-specific implementation details. The OCP specification requires the
  externally visible USB and recovery behavior, but does not prescribe those
  internal register accesses.
- One OCP Recovery command maps to exactly one USB EP0 control transfer.
  Reads use a Class/Interface Control IN transfer and writes use a
  Class/Interface Control OUT transfer. `bRequest=0x00`, `wValue[7:0]` contains
   the OCP command ID, and `wIndex[7:0]` contains the recovery interface number.
   For reads, the host sets `wLength` to the descriptor's
   `wMaxRdTransferSize`; for writes, `wLength` is the command payload length and
   must not exceed `wMaxWrTransferSize`.

## Complete ordered flow

### A. Power-on and USB recovery-interface initialization

1. **Recovery Device [USB Core]:** Power-on reset initializes the USB device
   controller and OCP Recovery register block. The recovery interface must be
   capable of remaining available in normal runtime and recovery mode once USB
   enumeration completes. Device interface mastering starts disabled if
   `DEVICE_RESET.InterfaceControl` is implemented.

2. **Device Firmware [Caliptra]:** Install the USB device, configuration,
   recovery-interface, and OCP Recovery functional descriptors before
   connecting the device to the host. The descriptors advertise:
   `bInterfaceClass=0xEF`, `bInterfaceSubClass=0x08`,
   `bInterfaceProtocol=0x01`, EP0 only, `wMaxWrTransferSize`,
   `wMaxRdTransferSize`, and OCP Recovery version 1.1.

3. **Device Firmware [Caliptra]:** Configure the USB controller for device
   mode; initialize the EP0 SETUP, OUT, and IN descriptors and buffers; program
   the endpoint-list and data-buffer bases; enable the device connection; enable
   device, EP0 OUT, and EP0 IN interrupt sources; and clear stale interrupt
   status.

4. **Recovery Device [USB Core] -> Device Firmware [Caliptra]:** Assert the USB
   device interrupt when a bus-reset or firmware-serviced EP0 event occurs.
   Caliptra Subsystem routes `usb_dev_irq` to MCU external interrupt vector 3.
   Firmware may service this interrupt by polling the USB interrupt/status
   registers, as the current bring-up firmware does.

### B. Standard USB enumeration

5. **Recovery Agent [Host]:** Detect device attachment and issue a USB port/bus
   reset.

6. **Recovery Device [USB Core] -> Device Firmware [Caliptra]:** Report the bus
   reset through the device interrupt/status indication.

7. **Device Firmware [Caliptra]:** Acknowledge the bus-reset indication,
   restore EP0 to the Default state, reset the USB device address to zero,
   clear the selected configuration, and re-arm EP0 SETUP reception.

8. **Recovery Agent [Host]:** Perform standard USB enumeration, including
   `GET_DESCRIPTOR(Device)`.

9. **Recovery Device [USB Core] -> Device Firmware [Caliptra]:** Assert the EP0
   event indication for firmware-serviced standard requests.

10. **Device Firmware [Caliptra]:** Return the USB Device Descriptor and
    complete the control transfer.

11. **Recovery Agent [Host]:** Issue `SET_ADDRESS`.

12. **Device Firmware [Caliptra]:** Return the zero-length status response,
    stage the new USB device address, complete the transfer, and re-arm EP0.

13. **Recovery Agent [Host]:** Issue
    `GET_DESCRIPTOR(Configuration)` for the complete configuration hierarchy.

14. **Device Firmware [Caliptra]:** Return the Configuration Descriptor, the
    single OCP Recovery Interface Descriptor, and the OCP Recovery Functional
    Descriptor. The host learns the interface number and maximum OCP read/write
    transfer sizes from this response.

15. **Recovery Agent [Host]:** Issue `SET_CONFIGURATION` with the advertised
    non-zero configuration value.

16. **Device Firmware [Caliptra]:** Accept the configuration, return the
    zero-length status response, record the Configured state, and re-arm EP0.

17. **Recovery Device [USB Core]:** The OCP Recovery interface is now available
    over EP0 and must respond to OCP Recovery commands. If several recovery
    transports exist, the Recovery Agent selects USB as the sole transport for
    this recovery session.

### C. Recovery discovery and entry

18. **Recovery Agent [Host]:** Read `PROT_CAP` (`0x22`). Verify the `"OCP RECV"`
    magic, protocol version 1.1, mandatory `DEVICE_ID` and `DEVICE_STATUS`
    capabilities, Push C-image support, FIFO CMS support (`bit 12`), CMS count,
    and maximum response time; record the advertised heartbeat period.

19. **Recovery Agent [Host]:** Read `DEVICE_ID` (`0x23`) and identify the
    Recovery Device.

20. **Recovery Agent [Host]:** Read `DEVICE_STATUS` (`0x24`). A zero status
    means status is still pending; continue polling until it becomes non-zero.
    This read also clears any host-visible `PROTOCOL_ERROR`.

21. **Recovery Agent [Host], conditional:** If the device is not already in
    recovery mode and forced recovery is supported and enabled, write
    `DEVICE_RESET` (`0x25`) with `ForcedRecovery=0xF` and an applicable reset
    request. Forced recovery takes effect at the next reset.

22. **Recovery Device [USB Core] / Device Firmware [Caliptra], conditional:**
    Perform the requested reset while preserving the ability to re-enumerate
    and recover. If forced recovery is disabled, report
    `RECOVERY_STATUS=0xE` (Error entering Recovery mode).

23. **Recovery Agent [Host], conditional:** After a bus-disruptive reset,
    repeat steps 5-20. After a non-bus-disruptive management reset, wait for the
    recovery interface to resume and poll status.

24. **Device Firmware [Caliptra]:** Enter recovery mode, set
    `DEVICE_STATUS=0x3` (Recovery mode, ready to accept a recovery image),
    populate the recovery reason code, and set
    `RECOVERY_STATUS.DeviceRecoveryStatus=0x1` (Awaiting recovery image) with
    the current `RecoveryImageIndex`.

25. **Recovery Agent [Host]:** Poll `DEVICE_STATUS` (`0x24`) until byte 0 is
    `0x3`.

26. **Recovery Agent [Host]:** Read `RECOVERY_STATUS` (`0x27`) and confirm
    `DeviceRecoveryStatus=0x1`. Record the `RecoveryImageIndex`; it identifies
    the recovery stage whose image must now be supplied.

### D. Transfer one recovery image through the FIFO CMS

27. **Recovery Agent [Host]:** Write `RECOVERY_CTRL` (`0x26`) selecting the
    code CMS used for recovery, with `RecoveryImageSelection=0x1` (use recovery
    image from the CMS) and `ActivateRecoveryImage=0`. For the mandatory pushed
    code region, `CMS=0`. This command must complete before activation.

28. **Recovery Agent [Host]:** Write `INDIRECT_FIFO_CTRL` (`0x2D`) with
    `CMS=0`, `Reset=1`, and `ImageSize` equal to the complete image size in
    four-byte units. This resets the FIFO read and write indexes.

29. **Recovery Agent [Host]:** Read `INDIRECT_FIFO_STATUS` (`0x2E`). Confirm
    that the selected region is a write-only code space, and record FIFO size,
    maximum transfer size, write index, and read index.

30. **Recovery Agent [Host]:** Partition the image into ordered chunks. Each
    chunk must be no larger than all of:
    the remaining image bytes, `INDIRECT_FIFO_STATUS.MaxTransferSize`, and the
    USB functional descriptor's `wMaxWrTransferSize`. Four-byte-aligned chunk
    sizes avoid padding gaps in the FIFO index.

31. **Recovery Agent [Host]:** Write the next chunk with
    `INDIRECT_FIFO_DATA` (`0x2F`) in one EP0 Control OUT transfer.

32. **Recovery Device [USB Core]:** Validate the USB control transfer, append
    the accepted bytes to the selected FIFO, and advance the write index in
    four-byte units. A transfer that would advance the write index to the read
    index must be rejected rather than overwrite unread image data. Over USB,
    rejection is represented through the binding's EP0 error/STALL handling.

33. **Recovery Device [USB Core] -> Device Firmware [Caliptra]:** Assert or
    maintain the Caliptra-specific recovery-payload-available indication when
    FIFO image data is available. In Caliptra Subsystem this is exposed as
    `cptra_ss_usb_recovery_payload_available_o`.

34. **Device Firmware [Caliptra]:** Read `INDIRECT_FIFO_CTRL.ImageSize` and
    `INDIRECT_FIFO_STATUS`; drain available words by reading the fixed
    `INDIRECT_FIFO_DATA` aperture; store them in the destination image buffer;
    and thereby advance the FIFO read index.

35. **Recovery Agent [Host]:** Apply FIFO flow control as needed. It may retry
    after a rejected full-FIFO write, or read `INDIRECT_FIFO_STATUS` and
    calculate free space from the read and write indexes before issuing more
    `INDIRECT_FIFO_DATA` writes.

36. **Recovery Agent [Host], Recovery Device [USB Core], and Device Firmware
    [Caliptra]:** Repeat steps 31-35 until the Recovery Agent has written and
    Device Firmware has consumed all `ImageSize` words without reordering or
    omission.

37. **Device Firmware [Caliptra]:** Verify that the full expected image has
    arrived, close the writable recovery region as needed to prevent
    time-of-check/time-of-use modification, and perform the device's required
    image integrity, authenticity, anti-rollback, and placement checks.

38. **Device Firmware [Caliptra]:** Set `DEVICE_STATUS=0x4` (Recovery Pending)
    when the complete image is waiting for activation. The recovery reason code
    remains populated.

39. **Recovery Agent [Host]:** Poll `DEVICE_STATUS` (`0x24`) until byte 0 is
    `0x4`. A fatal or boot-failure status terminates the successful flow.

### E. Activate and boot the image

40. **Recovery Agent [Host]:** Write `RECOVERY_CTRL` (`0x26`) with the selected
    code CMS/image mode and `ActivateRecoveryImage=0xF`.

41. **Recovery Device [USB Core] -> Device Firmware [Caliptra]:** Latch the
    write-one activation request and signal it to the recovery firmware/FSM.
    The device clears the activation field after accepting the request.

42. **Device Firmware [Caliptra]:** Set
    `RECOVERY_STATUS.DeviceRecoveryStatus=0x2` (Booting recovery image), then
    restart through the immutable device trust anchor. A management reset may
    implement this activation if it does not violate the required recovery
    behavior.

43. **Device Firmware [Caliptra]:** Authenticate and launch the selected
    recovery image stage. The running stage may initialize additional hardware
    or prepare storage required for a later recovery image.

44. **Recovery Device [USB Core]:** Keep the OCP Recovery EP0 interface
    responsive across the activation/restart so the Recovery Agent can observe
    progress and provide another image if requested.

45. **Recovery Agent [Host]:** Poll `RECOVERY_STATUS` (`0x27`) and
    `DEVICE_STATUS` (`0x24`) within the device's advertised maximum response
    time. Interpret the result as follows:
    - `RECOVERY_STATUS=0x1` with an incremented `RecoveryImageIndex`: another
      recovery image stage is required.
    - `RECOVERY_STATUS=0x3`: all recovery stages succeeded.
    - `RECOVERY_STATUS=0xC`, `0xD`, or `0xF`, or a device boot/fatal status:
      recovery failed.

### F. Multi-stage continuation or final completion

46. **Device Firmware [Caliptra], more stages required:** Increment
    `RecoveryImageIndex`, set `RECOVERY_STATUS=0x1` (Awaiting recovery image),
    set `DEVICE_STATUS=0x3` (Recovery mode), reset/prepare the FIFO for the next
    image, and deassert stale payload-available state from the prior stage.

47. **Recovery Agent [Host], more stages required:** Observe the new image
    index and repeat steps 27-45 for that stage. Repeat until every required
    device firmware image has been transferred, accepted, activated, and
    booted.

48. **Device Firmware [Caliptra], final stage successful:** Set
    `RECOVERY_STATUS=0x3` (Recovery successful). While the recovery image is
    running, `DEVICE_STATUS=0x5` (Running Recovery Image) is the defined
    intermediate device state.

49. **Device Firmware [Caliptra]:** Complete the device-specific transition
    from recovery firmware to operational firmware.

50. **Device Firmware [Caliptra]:** Set `DEVICE_STATUS=0x1` (Device Healthy)
    once operational firmware is running. This is the terminal successful
    state requested for the diagram: all required device firmware has been
    transferred and booted.

51. **Recovery Agent [Host]:** Read `RECOVERY_STATUS=0x3` and
    `DEVICE_STATUS=0x1`, then end the recovery session.

## Error branches to retain in the diagram

- An unsupported command, unsupported parameter, incorrect write length, or
  invalid transfer integrity check sets the corresponding
  `DEVICE_STATUS.PROTOCOL_ERROR`; reading `DEVICE_STATUS` clears that field.
- A USB EP0 STALL is recovered first with
  `CLEAR_FEATURE(ENDPOINT_HALT)`. If that fails, the host escalates to USB
  port/bus reset and resumes from enumeration.
- A FIFO write that would overrun unread data is flow-controlled; it is not a
  successful image transfer.
- Image authentication failure is reported as `RECOVERY_STATUS=0xD`; general
  stage activation failure is `0xC`; invalid CMS is `0xF`.
- A failed stage must not advance to the next image index or to Device Healthy.

## Specification sources

- OCP Secure Firmware Recovery v1.1 section 6, Recovery Process.
- Section 7.2, Forced Recovery.
- Section 7.4, Recovery Image Push.
- Section 7.5, Recovery Image Selection.
- Section 7.6, Recovery Image Activation.
- Section 7.8, Normal/Healthy Operation.
- Section 8 and Table 1, command availability and scope.
- Section 8.1, Capability/Discovery.
- Sections 8.2, 8.2.1, 8.2.2, and 8.2.5, indirect memory and FIFO CMS.
- Sections 8.5 through 8.5.6, USB EP0 transport, descriptors, enumeration, and
  USB-specific error recovery.
- Section 9.1, protocol error handling.
- Section 9.2 command definitions for `PROT_CAP`, `DEVICE_ID`,
  `DEVICE_STATUS`, `DEVICE_RESET`, `RECOVERY_CTRL`, `RECOVERY_STATUS`,
  `INDIRECT_FIFO_CTRL`, `INDIRECT_FIFO_STATUS`, and `INDIRECT_FIFO_DATA`.

## Caliptra implementation references

- `src/integration/test_suites/libs/usb/usb.c`: USB controller and EP0
  initialization, bus-reset handling, enumeration request handling, and USB
  interrupt servicing.
- `src/integration/test_suites/libs/usb/usb_ocp_recovery.c`: OCP Recovery USB
  interface and functional descriptors.
- `src/integration/test_suites/caliptra_ss_usb_ocp_recovery_init/`: MCU USB
  ownership and Caliptra streaming-boot handoff.
- `src/integration/test_suites/cptra_usb_ocp_recovery/`: Caliptra-side recovery
  aperture polling and FIFO consumption example.
- `src/integration/rtl/caliptra_ss_top.sv`: USB device interrupt routing and
  `cptra_ss_usb_recovery_payload_available_o`.

## Sequence diagram

```mermaid
%%{init: {'theme': 'base', 'themeVariables': {
  'signalColor': '#000000',
  'signalTextColor': '#222222',
  'labelTextColor': '#222222',
  'loopTextColor': '#222222',
  'noteTextColor': '#222222',
  'actorTextColor': '#222222',
  'actorBorder': '#000000',
  'activationBorderColor': '#000000'
}}}%%
sequenceDiagram
    participant Agent as Recovery Agent (Host)
    participant USB   as Recovery Device (USB Core)
    participant FW    as Device Firmware (Caliptra)

    rect rgb(180, 210, 245)
        Note over Agent,FW: A. Power-on and USB Recovery-Interface Initialization
        USB->>USB: Power-on reset, init USB controller and OCP Recovery registers
        FW->>FW: Install USB / config / interface / OCP Recovery descriptors
        FW->>USB: PROT_CAP -- magic, version 1.1, capabilities, FIFO CMS bit, CMS count
        FW->>USB: HW_STATUS -- initial hardware health status
        FW->>USB: DEVICE_STATUS=0x1 (Device Healthy), RECOVERY_STATUS=0x0
        FW->>USB: Configure EP0 descriptors and buffers, enable connection and interrupts
        USB-->>FW: usb_dev_irq (bus-reset or EP0 event)
    end

    rect rgb(160, 210, 175)
        Note over Agent,FW: B. Standard USB Enumeration
        Agent->>USB: USB port / bus reset
        USB-->>FW: Report bus reset
        FW->>FW: Ack bus-reset, restore EP0 Default state, reset address to 0, re-arm EP0
        Agent->>USB: GET_DESCRIPTOR(Device)
        USB-->>FW: EP0 SETUP event
        FW-->>Agent: Device Descriptor
        Agent->>USB: SET_ADDRESS
        USB-->>FW: EP0 SETUP event
        FW-->>Agent: ZLP status response
        FW->>USB: Stage new device address, re-arm EP0
        Agent->>USB: GET_DESCRIPTOR(Configuration)
        USB-->>FW: EP0 SETUP event
        FW-->>Agent: Configuration + Interface + OCP Recovery Functional Descriptor
        Agent->>USB: SET_CONFIGURATION
        USB-->>FW: EP0 SETUP event
        FW-->>Agent: ZLP status response
        FW->>FW: Record Configured state, re-arm EP0
        Note over USB: OCP Recovery interface now available over EP0
    end

    rect rgb(220, 190, 120)
        Note over Agent,FW: C. Recovery Discovery and Entry
        Agent->>USB: OCP IN: PROT_CAP (0x22)
        USB-->>Agent: PROT_CAP -- magic, version 1.1, capabilities, FIFO CMS bit, CMS count
        Agent->>USB: OCP IN: DEVICE_ID (0x23)
        USB-->>Agent: Device identity
        loop Poll until DEVICE_STATUS != 0
            Agent->>USB: OCP IN: DEVICE_STATUS (0x24)
            USB-->>Agent: DEVICE_STATUS
        end
        FW->>FW: Enter recovery mode
        FW->>USB: DEVICE_STATUS=0x3 (Recovery mode, ready to accept image)
        FW->>USB: RECOVERY_STATUS=0x1 (Awaiting recovery image), set RecoveryImageIndex
        loop Poll until DEVICE_STATUS == 0x3
            Agent->>USB: OCP IN: DEVICE_STATUS (0x24)
            USB-->>Agent: DEVICE_STATUS
        end
        Agent->>USB: OCP IN: RECOVERY_STATUS (0x27)
        USB-->>Agent: RECOVERY_STATUS=0x1, RecoveryImageIndex=N
    end

    rect rgb(210, 140, 140)
        Note over Agent,FW: D. Transfer Recovery Image via Indirect FIFO CMS
        Agent->>USB: OCP OUT: RECOVERY_CTRL (0x26) CMS=0, RecoveryImageSelection=0x1, Activate=0
        Agent->>USB: OCP OUT: INDIRECT_FIFO_CTRL (0x2D) CMS=0, Reset=1, ImageSize=N words
        Agent->>USB: OCP IN: INDIRECT_FIFO_STATUS (0x2E)
        USB-->>Agent: FIFO size, MaxTransferSize, write index, read index
        loop Until all ImageSize words transferred and consumed
            Agent->>USB: OCP OUT: INDIRECT_FIFO_DATA (0x2F) -- next chunk
            USB->>USB: Append chunk to FIFO, advance write index
            USB-->>FW: Assert cptra_ss_usb_recovery_payload_available_o
            FW->>USB: INDIRECT_FIFO_CTRL.ImageSize + INDIRECT_FIFO_STATUS
            FW->>USB: INDIRECT_FIFO_DATA aperture (drain available words)
            USB->>USB: Advance FIFO read index
            FW->>FW: Store words in image buffer
        end
        FW->>FW: Verify full image received, close recovery region, integrity / authenticity / anti-rollback check
        FW->>USB: DEVICE_STATUS=0x4 (Recovery Pending)
        loop Poll until DEVICE_STATUS == 0x4
            Agent->>USB: OCP IN: DEVICE_STATUS (0x24)
            USB-->>Agent: DEVICE_STATUS
        end
    end

    rect rgb(175, 145, 210)
        Note over Agent,FW: E. Activate and Boot the Image
        Agent->>USB: OCP OUT: RECOVERY_CTRL (0x26) ActivateRecoveryImage=0xF
        USB-->>FW: Latch activation request, signal recovery FSM
        USB->>USB: Clear activation field after accepting request
        FW->>USB: RECOVERY_STATUS=0x2 (Booting recovery image)
        FW->>FW: Authenticate and launch recovery image stage
        Note over USB: OCP Recovery EP0 remains responsive during activation / restart
        loop Poll within advertised max response time
            Agent->>USB: OCP IN: RECOVERY_STATUS (0x27) + DEVICE_STATUS (0x24)
            USB-->>Agent: Status response
        end
    end

    rect rgb(100, 175, 155)
        Note over Agent,FW: F. Final Completion
        FW->>USB: RECOVERY_STATUS=0x3 (Recovery successful)
        FW->>USB: DEVICE_STATUS=0x5 (Running Recovery Image)
        FW->>FW: Transition from recovery firmware to operational firmware
        FW->>USB: HW_STATUS -- updated post-recovery hardware health
        FW->>USB: DEVICE_STATUS=0x1 (Device Healthy)
        Agent->>USB: OCP IN: RECOVERY_STATUS (0x27) + DEVICE_STATUS (0x24)
        USB-->>Agent: RECOVERY_STATUS=0x3, DEVICE_STATUS=0x1
        Note over Agent: Recovery session complete
    end
```
