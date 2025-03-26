#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate RTL and documentation collateral from OTP memory
map definition file (hjson).
"""
import argparse
import datetime
import logging as log
import random
from pathlib import Path
from Crypto.Hash import cSHAKE128

import hjson

from lib.common import wrapped_docstring
from lib.otp_mem_img import OtpMemImg
from lib.otp_mem_map import OtpMemMap


# Default output path (can be overridden on the command line). Note that
# "BITWIDTH" will be replaced with the architecture's bitness.
MEMORY_MEM_FILE = 'otp-img.BITWIDTH.vmem'


def _override_seed(args, seed_name, config):
    '''Override the seed key in config with value specified in args'''
    arg_seed = getattr(args, seed_name)

    # An override seed of 0 will not trigger the override, which is intended, as
    # the OTP-generation Bazel rule sets the default seed values to 0.
    if arg_seed:
        log.warning('Commandline override of {} with {}.'.format(
            seed_name, arg_seed))
        config['seed'] = arg_seed
    # Otherwise, we either take it from the .hjson if present, or
    # randomly generate a new seed if not.
    else:
        new_seed = random.getrandbits(256)
        if config.setdefault('seed', new_seed) == new_seed:
            log.warning('No {} specified, setting to {}.'.format(
                seed_name, new_seed))


def main():
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="gen-otp-img",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-stamp',
                        action='store_true',
                        help='''
                        Add a comment 'Generated on [Date] with [Command]' to
                        generated output files.
                        ''')
    parser.add_argument('--otp-seed',
                        type=int,
                        metavar='<seed>',
                        help='''
                        Custom seed for RNG to compute randomized OTP netlist constants.

                        Note that this seed must coincide with the seed used for generating
                        the OTP memory map (gen-otp-mmap.py).

                        This value typically does not need to be specified as it is taken from
                        the OTP memory map definition Hjson.
                        ''')
    parser.add_argument('-o',
                        '--out',
                        type=str,
                        metavar='<path>',
                        default=MEMORY_MEM_FILE,
                        help='''
                        Custom output path for generated MEM file.
                        Defaults to {}
                        '''.format(MEMORY_MEM_FILE))
    parser.add_argument('--lc-state-def',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Life cycle state definition file in Hjson format.
                        ''')
    parser.add_argument('--mmap-def',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Path to OTP memory map file in Hjson format.
                        ''')
    parser.add_argument('--lc-state',
                        type=str,
                        metavar='state',
                        required=True,
                        help='''
                        Life cycle state to write into the OTP.
                        ''')
    parser.add_argument('--lc-cnt',
                        type=int,
                        metavar='counter',
                        required=True,
                        help='''
                        Life cycle counter to write into the OTP.
                        ''')
    parser.add_argument('--token-configuration',
                        type=str,
                        metavar='token-configuration',
                        required=False,
                        help='''
                        HSJON file containing the tokens required for state transitions.
                        ''')

    args = parser.parse_args()

    log.info('Loading LC state definition file {}'.format(args.lc_state_def))
    with open(args.lc_state_def, 'r') as infile:
        lc_state_cfg = hjson.load(infile)
    log.info('Loading OTP memory map definition file {}'.format(args.mmap_def))
    with open(args.mmap_def, 'r') as infile:
        otp_mmap_cfg = hjson.load(infile)
    
    token_cfg = None
    if args.token_configuration is not None:
        with open(args.token_configuration, 'r') as infile:
                token_cfg = hjson.load(infile)
 
     # If specified, override the seed.
    _override_seed(args, 'otp_seed', otp_mmap_cfg)

    img_config = {}
    img_config['seed'] = 0 # Not used.
    img_config['partitions'] = []
    # Configure the LC state & counter.
    lc_config = {}
    lc_config['name'] = 'LIFE_CYCLE'
    lc_config['count'] = args.lc_cnt
    lc_config['state'] = args.lc_state
    lc_config['items'] = []
    lc_config['lock'] = False
    img_config['partitions'].append(lc_config)
    # Configure the unlock token.
    if token_cfg is not None:
        # Configure the partition.
        token_config = {}
        token_config['name'] = 'SECRET_LC_TRANSITION_PARTITION'
        token_config['lock'] = True # Lock the partition such that the digest is calculated.
        token_config['items'] = []
        # Create the tokens.
        for token_name, token_value in token_cfg.items():
            # Hash the token.
            value = int(token_value, 0)
            data = value.to_bytes(16, byteorder='little')
            custom = 'LC_CTRL'.encode('UTF-8')
            shake = cSHAKE128.new(data=data, custom=custom)
            digest = int.from_bytes(shake.read(16), byteorder='little')
            # Create the token item.
            token_item = {}
            token_item['name'] = token_name
            token_item['value'] = str(hex(digest))
            token_config['items'].append(token_item)
        # Append the tokens to the partition.
        img_config['partitions'].append(token_config)

    try:
        otp_mem_img = OtpMemImg(lc_state_cfg, otp_mmap_cfg, img_config, '')

    except RuntimeError as err:
        log.error(err)
        exit(1)

    # Print all defined args into header comment for reference
    argstr = ''
    for arg, argval in sorted(vars(args).items()):
        if argval:
            if not isinstance(argval, list):
                argval = [argval]
            for a in argval:
                argname = '-'.join(arg.split('_'))
                # Get absolute paths for all files specified.
                a = a.resolve() if isinstance(a, Path) else a
                argstr += ' \\\n//   --' + argname + ' ' + str(a) + ''

    file_header = '//\n'
    if args.stamp:
        dt = datetime.datetime.now(datetime.timezone.utc)
        dtstr = dt.strftime("%a, %d %b %Y %H:%M:%S %Z")
        file_header = '// Generated on {} with\n// $ gen-otp-img.py {}\n//\n'.format(
            dtstr, argstr)

    memfile_body, bitness = otp_mem_img.streamout_memfile()

    # If the out argument does not contain "BITWIDTH", it will not be changed.
    memfile_path = Path(args.out.replace('BITWIDTH', str(bitness)))

    # Use binary mode and a large buffer size to improve performance.
    with open(memfile_path, 'wb', buffering=2097152) as outfile:
        outfile.write(file_header.encode('utf-8'))
        outfile.write(memfile_body.encode('utf-8'))


if __name__ == "__main__":
    main()
