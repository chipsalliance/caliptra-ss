#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Build USB-transferred executable DV artifacts; never preload their ELFs."""

import hashlib
import os
from pathlib import Path
import struct
import subprocess


MAGIC = 0x344F4C46
MANIFEST_MAGIC = 0x34464E4D
FORMAT_VERSION = 1
HEADER_BYTES = 64


def digest_words(payload):
    return struct.unpack(">12I", hashlib.sha384(payload).digest())


def main():
    root = Path(os.environ["CALIPTRA_SS_ROOT"])
    source = Path(__file__).resolve().parent
    includes = root / "src/integration/rtl/soc_address_map"
    compiler = "riscv64-unknown-elf-gcc"
    # Derive the artifact's link address from the platform address-map header.
    address = subprocess.run(
        [compiler, "-E", "-P", "-x", "c", "-I", str(includes), "-"],
        input='#include "soc_address_map.h"\nSOC_MCI_TOP_MCU_SRAM_BASE_ADDR\n',
        text=True, capture_output=True, check=True,
    ).stdout.strip()
    mcu_base = int(address.strip("()"), 0)
    payloads = []
    for name, base in (("core", 0x40000000), ("mcu", mcu_base + HEADER_BYTES)):
        script = Path(f"flow004_{name}.ld")
        script.write_text(
            "OUTPUT_ARCH(riscv)\nENTRY(image_entry)\nSECTIONS {\n"
            f". = 0x{base:x};\n"
            ".text : { *(.text.entry) *(.text*) *(.rodata*) . = ALIGN(4); }\n"
            ".data : { *(.data*) *(.sdata*) }\n"
            ".bss : { *(.bss*) *(.sbss*) *(COMMON) }\n"
            'ASSERT(SIZEOF(.data) == 0 && SIZEOF(.bss) == 0, '
            '"Downloaded entry must not require preloaded data")\n'
            "/DISCARD/ : { *(.comment) *(.riscv.attributes) }\n}\n",
            encoding="ascii",
        )
        subprocess.run(
            [compiler, "-Os", "-Wall", "-Wextra", "-Werror",
             "-march=rv32imc_zicsr_zifencei", "-mabi=ilp32",
             "-msmall-data-limit=0", "-ffreestanding", "-fno-builtin",
             "-nostdlib", "-Wl,--build-id=none", "-T", str(script),
             "-I", str(includes), str(source / f"{name}_image.c"),
             "-o", f"flow004_{name}.elf"],
            check=True,
        )
        subprocess.run(
            ["riscv64-unknown-elf-objcopy", "-O", "binary", "-j", ".text",
             f"flow004_{name}.elf", f"flow004_{name}.bin"],
            check=True,
        )
        payload = Path(f"flow004_{name}.bin").read_bytes()
        payload = payload.ljust(max(512, (len(payload) + 3) & ~3), b"\0")
        payloads.append(payload)

    core, mcu = payloads
    manifest = struct.pack("<15I", MANIFEST_MAGIC, mcu_base, len(mcu),
                           *digest_words(mcu)).ljust(512, b"\0")
    for stage, payload in enumerate((core, manifest, mcu)):
        image = struct.pack("<16I", MAGIC, stage, len(payload), FORMAT_VERSION,
                            *digest_words(payload)) + payload
        if len(image) > 4096:
            raise ValueError(f"stage {stage} exceeds the 4-KiB execution region")
        Path(f"flow004_stage{stage}.hex").write_text(
            "".join(f"{byte:02x}\n" for byte in image), encoding="ascii"
        )
        print(f"FLOW004 stage={stage} bytes={len(image)} "
              f"sha384={hashlib.sha384(payload).hexdigest()}")


if __name__ == "__main__":
    main()
