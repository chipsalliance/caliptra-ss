#!/usr/bin/env sh
''':'
exec /usr/bin/env python3w -r requirements.txt "$0" "$@"
'''
# SPDX-License-Identifier: Apache-2.0
#
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

import argparse
import itertools
import secrets

from Crypto.Hash import cSHAKE128

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--unhashed-token", help='''
                        Unhashed token, formatted as hexadecimal number in
                        little-endian order (i.e., the least-significant byte
                        is at the end). Must be 128 bit in length and thus
                        consist of 32 hexadecimal digits. May optionally contain
                        a `0x` prefix. Must not contain any separators (such as
                        spaces or underscores). If omitted, this program
                        generates the unhashed token using Python's `secrets`
                        module and outputs it.
                        ''', action=ValidateTokenHexString, required=False)

    return parser.parse_args()


class ValidateTokenHexString(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        if value.startswith("0x"):
            if len(value) != 34:
                parser.error(f"{value} starts with `0x` "
                             "but does not contain 32 digits.")
        else:
            if len(value) != 32:
                parser.error(f"{value} does not contain 32 digits.")
        try:
            val = int(value, 16)
        except ValueError as e:
            parser.error(str(e))
        setattr(namespace, self.dest, val)


if __name__ == "__main__":
    args = parse_args()

    # Obtain the unhashed token, which is a dynamic input to LC_CTRL to perform
    # transitions.
    if args.unhashed_token is not None:
        # If the unhashed token was provided as command-line argument, read it
        # from there.
        unhashed_token = args.unhashed_token
    else:
        # If the unhashed token was not provided, generate it using the
        # `secrets` module, which provides access to the most secure source of
        # randomness that your operating system provides.
        unhashed_token = secrets.randbits(128)

    # Store the unhashed token as little-endian byte array.
    unhashed_token = unhashed_token.to_bytes(16, byteorder="little")

    # Print unhashed token in C's little-endian byte but big-endian word order.
    unhashed_token_words = itertools.batched(unhashed_token, 4)
    unhashed_token_words = [f"0x{int.from_bytes(w, byteorder="little"):08x}"
                            for w in unhashed_token_words]
    print("uint32_t raw_unlock_token[4] = {")
    print("    " + ", ".join(unhashed_token_words))
    print("};")

    # Compute cSHAKE of the token with a fixed, lc_ctrl-specifi customization
    # string.
    customization_string = 'LC_CTRL'.encode('UTF-8')
    shake = cSHAKE128.new(data=unhashed_token, custom=customization_string)

    # Assemble bytes in little endian order.
    shake_bytes = []
    for i in range(0, 4):
        shake_bytes.append(int.from_bytes(shake.read(4), byteorder="little"))

    # Print SystemVerilog literal of the hashed token, which is stored in HW,
    # with `_` between 32-bit words and lowest word at the end.
    print("")
    print("lc_ctrl_state_pkg::lc_token_t RndCnstRawUnlockTokenHashed = {")
    print("  128'h" + "_".join([f"{b:08x}" for b in reversed(shake_bytes)]))
    print("};")
